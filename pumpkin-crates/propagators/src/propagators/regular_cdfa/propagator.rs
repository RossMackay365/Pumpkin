use std::cmp::PartialOrd;
use std::fmt::Debug;
use std::hash::Hash;

use enumset::__internal::EnumSetTypeRepr;
use itertools::Itertools;
use pumpkin_checking::AtomicConstraint;
use pumpkin_checking::CheckerVariable;
use pumpkin_checking::InferenceChecker;
use pumpkin_checking::IntExt;
use pumpkin_checking::VariableState;
use pumpkin_core::conjunction;
use pumpkin_core::containers::HashMap;
use pumpkin_core::declare_inference_label;
use pumpkin_core::predicate;
use pumpkin_core::predicates::PropositionalConjunction;
use pumpkin_core::proof::ConstraintTag;
use pumpkin_core::proof::InferenceCode;
use pumpkin_core::propagation::DomainEvents;
use pumpkin_core::propagation::InferenceCheckers;
use pumpkin_core::propagation::LocalId;
use pumpkin_core::propagation::PropagationContext;
use pumpkin_core::propagation::Propagator;
use pumpkin_core::propagation::PropagatorConstructor;
use pumpkin_core::propagation::PropagatorConstructorContext;
use pumpkin_core::propagation::ReadDomains;
use pumpkin_core::state::PropagationStatusCP;
use pumpkin_core::variables::IntegerVariable;

#[derive(Clone, Debug)]
pub struct RegularCdfaPropagatorConstructor<Var, CVar> {
    pub sequence: Box<[Var]>,
    pub num_states: u32,
    pub num_inputs: u32,
    pub transition_matrix: Vec<Vec<i32>>,
    pub initial_state: i32,
    pub inc: Vec<Vec<i32>>,
    pub count: CVar,

    pub constraint_tag: ConstraintTag,
}
declare_inference_label!(RegularCdfa);

impl<Var: IntegerVariable + 'static, CVar: IntegerVariable + 'static> PropagatorConstructor
    for RegularCdfaPropagatorConstructor<Var, CVar>
{
    type PropagatorImpl = RegularCdfaPropagator<Var, CVar>;

    fn add_inference_checkers(&self, mut checkers: InferenceCheckers<'_>) {
        let RegularCdfaPropagatorConstructor {
            sequence,
            num_states,
            num_inputs,
            transition_matrix,
            initial_state,
            inc,
            count,
            constraint_tag,
        } = self;

        // Add Inference Checker
        checkers.add_inference_checker(
            InferenceCode::new(*constraint_tag, RegularCdfa),
            Box::new(RegularCdfaChecker {
                sequence: sequence.clone(),
                count: count.clone(),

                c_dfa: Cdfa {
                    num_states: *num_states,
                    num_inputs: *num_inputs,
                    transition_matrix: transition_matrix
                        .iter()
                        .map(|vec| vec.iter().map(|&q| q as u32 - 1).collect_vec())
                        .collect_vec(),
                    initial_state: *initial_state as u32 - 1,
                    inc: inc
                        .iter()
                        .map(|vec| vec.iter().map(|&c| c as u32).collect_vec())
                        .collect_vec(),
                },
            }),
        );
    }

    fn create(self, mut context: PropagatorConstructorContext) -> Self::PropagatorImpl {
        let RegularCdfaPropagatorConstructor {
            sequence,
            num_states,
            num_inputs,
            transition_matrix,
            initial_state,
            inc,
            count,
            constraint_tag,
        } = self;

        // Throw error on incorrect format.
        if transition_matrix
            .iter()
            .any(|vec| vec.iter().any(|&q| q < 1))
        {
            panic!("transition_matrix contains negative number.")
        }

        if initial_state < 1 {
            panic!("initial_state is {initial_state} and should be larger than 0.")
        }

        if inc.iter().any(|vec| vec.iter().any(|&c| c < 0)) {
            panic!("inc contains negative number.")
        }

        // Register Variables (count and sequence) with Solver
        context.register(count.clone(), DomainEvents::ANY_INT, LocalId::from(0));

        for (idx, var) in sequence.iter().enumerate() {
            context.register(
                var.clone(),
                DomainEvents::ANY_INT,
                LocalId::from((idx + 1) as u32),
            );
        }

        RegularCdfaPropagator {
            sequence,
            count,

            c_dfa: Cdfa {
                num_states,
                num_inputs,
                transition_matrix: transition_matrix
                    .iter()
                    .map(|vec| vec.iter().map(|&q| q as u32 - 1).collect_vec())
                    .collect_vec(),
                initial_state: initial_state as u32 - 1,
                inc: inc
                    .iter()
                    .map(|vec| vec.iter().map(|&c| c as u32).collect_vec())
                    .collect_vec(),
            },

            inference_code: InferenceCode::new(constraint_tag, RegularCdfa),
        }
    }
}

#[derive(Clone, Debug)]
pub struct RegularCdfaPropagator<Var, CVar> {
    sequence: Box<[Var]>,
    count: CVar,
    pub c_dfa: Cdfa,

    inference_code: InferenceCode,
}

impl<Var: IntegerVariable + 'static, CVar: IntegerVariable + 'static> Propagator
    for RegularCdfaPropagator<Var, CVar>
{
    fn name(&self) -> &str {
        "RegularCdfaPropagator"
    }

    fn propagate_from_scratch(&self, mut context: PropagationContext) -> PropagationStatusCP {
        // Get current predicates.
        let base_explanation = self.get_removed_symbol_predicates(&mut context);
        let n = self.sequence.len();

        // Compute the minimum and maximum qcf and qcb tables
        let min_qcf_table = &mut Vec::with_capacity(n + 1);
        let min_qcb_table = &mut Vec::with_capacity(n + 1);

        let max_qcf_table = &mut Vec::with_capacity(n + 1);
        let max_qcb_table = &mut Vec::with_capacity(n + 1);

        compute_qcb_and_qcf(
            &self.sequence,
            &self.c_dfa,
            &context,
            min_qcb_table,
            min_qcf_table,
            insert_min,
            0,
        );

        compute_qcb_and_qcf(
            &self.sequence,
            &self.c_dfa,
            &context,
            max_qcb_table,
            max_qcf_table,
            insert_max,
            0,
        );

        // Create a conjuntion to collect predicates var != l
        // for each l we remove from the domain of a given var.
        let mut removed_symbols = conjunction!();

        // Get the lower and upper bounds of count.
        let lb = context.domains().lower_bound(&self.count);
        let ub = context.domains().upper_bound(&self.count);

        // For each variable in sequence.
        for (i, var) in self.sequence.iter().enumerate() {
            // Get the states that can be the ith state,
            // with the minimum and maximum costs to get
            // from the start to them and from them to the end.
            let min_qcf = min_qcf_table.get(i).unwrap();
            let max_qcf = max_qcf_table.get(i).unwrap();
            let qcf = combine_table(min_qcf, max_qcf);

            let min_qcb = min_qcb_table.get(n - i - 1).unwrap();
            let max_qcb = max_qcb_table.get(n - i - 1).unwrap();
            let qcb = combine_table(min_qcb, max_qcb);

            // For each symbol in their domain.
            'symbols: for l in context
                .iterate_domain(var)
                .map(|l| l as usize - 1)
                .collect_vec()
            {
                let mut impossible_count_predicates =
                    conjunction!([self.count >= lb] & [self.count <= ub]);

                // Compute the minimum value of c when the ith var in the sequence is l.
                for (prev_q, min_c_before, max_c_before) in qcf
                    .iter()
                    .map(|&(q, min_c, max_c)| (q.to_usize(), min_c, max_c))
                {
                    let ref_q = self.c_dfa.transition_matrix[prev_q][l];

                    for (min_c_after, max_c_after) in qcb.iter().filter_map(|&(q, min_c, max_c)| {
                        if q == ref_q {
                            Some((min_c, max_c))
                        } else {
                            None
                        }
                    }) {
                        let min_c = min_c_before + self.c_dfa.inc[prev_q][l] + min_c_after;
                        let max_c = max_c_before + self.c_dfa.inc[prev_q][l] + max_c_after;

                        if (ub as u32) < min_c || max_c < (lb as u32) {
                            for hole in context
                                .domains()
                                .get_holes(&self.count)
                                .filter(|&v| min_c <= (v as u32) && (v as u32) <= max_c)
                            {
                                impossible_count_predicates.push(predicate![self.count != hole]);
                            }
                        } else {
                            // go to the next symbol.
                            continue 'symbols;
                        }
                    }
                }

                // All values in the domain of count fall outside of all possible bounds if the ith
                // symbol is l.
                let reason = concat_conjunctions(&base_explanation, &impossible_count_predicates);
                let p = predicate![var != l as i32 + 1];
                context.post(p, (reason, &self.inference_code))?;

                removed_symbols.push(p);
            }
        }

        // Propagate both a lower and an upper bound for Count.
        let reason = concat_conjunctions(&base_explanation, &removed_symbols);

        min_qcf_table.clear();
        max_qcf_table.clear();
        compute_qcf(
            &self.sequence,
            &self.c_dfa,
            &context,
            min_qcf_table,
            insert_min,
            n,
        );
        compute_qcf(
            &self.sequence,
            &self.c_dfa,
            &context,
            max_qcf_table,
            insert_max,
            n,
        );

        self.propagate_lb_count(&mut context, min_qcf_table, &reason)?;
        self.propagate_ub_count(&mut context, max_qcf_table, &reason)?;

        Ok(())
    }
}

impl<Var: IntegerVariable + 'static, Cvar: IntegerVariable + 'static>
    RegularCdfaPropagator<Var, Cvar>
{
    // fn propagate_at_most(&self, mut context: PropagationContext) -> PropagationStatusCP {
    //     let base_explanation = self.get_removed_symbol_predicates(&mut context);
    //     let n = self.sequence.len();

    //     let qcb_table = &mut Vec::with_capacity(n);
    //     let qcf_table = &mut Vec::with_capacity(n);

    //     compute_qcf(&context, qcf_table, insert_min, n);
    //     compute_qcb(&context, qcb_table, qcf_table, insert_min, 0);

    //     let mut removed_symbols = conjunction!();
    //     // For each variable in sequence.
    //     for (i, var) in self.sequence.iter().enumerate() {
    //     // Get the states that can be the ith state, with the minimum costs to get
    //         // from the start to them and from them to the end.
    //         let qcf = qcf_table.get(i - 1).unwrap();
    //         let qcb = qcb_table.get(n - i).unwrap();

    //         // For each symbol in their domain.
    //         for l in context
    //             .iterate_domain(var)
    //             .map(|l| l as usize)
    //             .collect_vec()
    //         {
    //
    //             // Compute the minimum value of c when the ith var in the sequence is l.
    //             let mut min_c = u32::MAX;
    //             for (prev_q, min_c_before) in qcf.iter().map(|&(q, c)| (q.to_usize(), c)) {
    //                 let ref_q = self.c_dfa.transition_matrix[prev_q][l];

    //                 for min_c_after in qcb
    //                     .iter()
    //                     .filter_map(|&(q, c)| if q == ref_q { Some(c) } else { None })
    //                 {
    //                     let new_c = min_c_before + self.c_dfa.inc[prev_q][l] + min_c_after;

    //                     min_c = u32::min(min_c, new_c);
    //                 }
    //             }

    //             // min_c(var_i == l) <= MAX(DOM(count))
    //             if context.upper_bound(&self.count) < min_c as i32 {
    //                 let reason = concat_conjunctions(
    //                     &base_explanation,
    //                     &conjunction!([self.count <= min_c as i32 + 1]),
    //                 );
    //                 let p = predicate![var != l as i32];

    //                 context.post(p, (reason, &self.inference_code))?;

    //                 removed_symbols.push(p);
    //             }
    //         }
    //     }

    //     qcf_table.clear();
    //     compute_qcf(&context, qcf_table, insert_min, n);

    //     self.propagate_max_count(
    //         &mut context,
    //         qcf_table,
    //         &concat_conjunctions(&base_explanation, &removed_symbols),
    //     )
    // }

    fn propagate_lb_count(
        &self,
        context: &mut PropagationContext,
        min_qcf_table: &[Vec<(u32, u32)>],
        reason: &PropositionalConjunction,
    ) -> PropagationStatusCP {
        let n = self.sequence.len();

        let mut min_c = u32::MAX;
        for &(_, c) in min_qcf_table.get(n).unwrap().iter() {
            min_c = u32::min(min_c, c)
        }

        // MIN(c) <= DOM(count)
        context.post(
            predicate![self.count >= min_c as i32],
            (reason.clone(), &self.inference_code),
        )?;

        Ok(())
    }

    fn propagate_ub_count(
        &self,
        context: &mut PropagationContext,
        max_qcf_table: &[Vec<(u32, u32)>],
        reason: &PropositionalConjunction,
    ) -> PropagationStatusCP {
        let n = self.sequence.len();

        let mut max_c = u32::MIN;
        for &(_, c) in max_qcf_table.get(n).unwrap().iter() {
            max_c = u32::max(max_c, c)
        }

        // MAX(c) >= DOM(count)
        context.post(
            predicate![self.count <= max_c as i32],
            (reason.clone(), &self.inference_code),
        )?;

        Ok(())
    }

    fn get_removed_symbol_predicates(
        &self,
        context: &mut PropagationContext,
    ) -> PropositionalConjunction {
        self.sequence
            .iter()
            .map(|var| {
                let mut vec = Vec::with_capacity(self.c_dfa.num_inputs.to_usize());
                for l in 1..(self.c_dfa.num_inputs + 1) {
                    if !context.domains().contains(var, l as i32) {
                        vec.push((var, l as i32));
                    }
                }
                vec
            })
            .concat()
            .iter()
            .map(|&(var, l)| predicate![var != l])
            .collect()
    }
}

#[derive(Clone, Debug)]
struct RegularCdfaChecker<Var, CVar> {
    sequence: Box<[Var]>,
    count: CVar,
    c_dfa: Cdfa,
}

impl<Var, CVar, Atomic> InferenceChecker<Atomic> for RegularCdfaChecker<Var, CVar>
where
    Var: CheckerVariable<Atomic>,
    CVar: CheckerVariable<Atomic>,
    Atomic: AtomicConstraint,
{
    fn check(&self, mut state: VariableState<Atomic>, _: &[Atomic], _: Option<&Atomic>) -> bool {
        let n = self.sequence.len();

        // Get domains of the variables in the sequence.
        let mut sequence_domains = vec![];
        for var in &self.sequence {
            let symbols = (1..(self.c_dfa.num_inputs + 1))
                .filter_map(|l| {
                    if var.induced_domain_contains(&state, l as i32) {
                        Some(l as usize - 1)
                    } else {
                        None
                    }
                })
                .collect_vec();
            sequence_domains.push(symbols);
        }

        // Get all possible counts after consuming the sequence.
        let qcf_table = &mut Vec::with_capacity(n + 1);
        let qcb_table = &mut Vec::with_capacity(n + 1);
        compute_qcb_and_qcf_for_check(&sequence_domains, &self.c_dfa, qcf_table, qcb_table, 0);

        // Check that all values in the domain of count are still possible.
        let mut consistent = true;

        let lb = self.count.induced_lower_bound(&state);
        let ub = self.count.induced_upper_bound(&state);

        // For each variable in sequence, determine which symbols it can and can't be.
        for (i, symbols) in sequence_domains.iter().enumerate() {
            let var = self.sequence.get(i).unwrap();

            // Get the states that can be the ith state,
            // with the minimum and maximum costs to get
            // from the start to them and from them to the end.
            let qcf = qcf_table.get(i).unwrap();
            let qcb = qcb_table.get(n - i - 1).unwrap();

            // For each symbol in their domain.
            'symbols: for &l in symbols {
                // Compute the minimum value of c when the ith var in the sequence is l.
                for (prev_q, min_c_before, max_c_before) in qcf
                    .iter()
                    .map(|&(q, (min_c, max_c))| (q.to_usize(), min_c, max_c))
                {
                    let ref_q = self.c_dfa.transition_matrix[prev_q][l];

                    for (min_c_after, max_c_after) in
                        qcb.iter().filter_map(|&(q, (min_c, max_c))| {
                            if q == ref_q {
                                Some((min_c, max_c))
                            } else {
                                None
                            }
                        })
                    {
                        let min_c = IntExt::Int(
                            (min_c_before + self.c_dfa.inc[prev_q][l] + min_c_after) as i32,
                        );
                        let max_c = IntExt::Int(
                            (max_c_before + self.c_dfa.inc[prev_q][l] + max_c_after) as i32,
                        );

                        // NOT (ub < min_c || max_c < lb)
                        // lb <= max_c && min_c <= ub
                        if lb.max(max_c) == max_c && ub.min(min_c) == min_c {
                            // Var i can equal l
                            let atomic = var.atomic_equal((l + 1) as i32);
                            consistent &= state.apply(&atomic);

                            // go to the next symbol.
                            continue 'symbols;
                        }
                    }
                }
                // No configuration where var i can equal l was found, so var i is not equal to l.
                let atomic = var.atomic_not_equal((l + 1) as i32);
                consistent &= state.apply(&atomic);
            }
        }

        // Check the upper and lower bound of count.
        let mut min_min_c = u32::MAX;
        let mut max_max_c = u32::MIN;
        for &(_, (min_c, max_c)) in qcf_table.get(n).unwrap().iter() {
            min_min_c = u32::min(min_min_c, min_c);
            max_max_c = u32::max(max_max_c, max_c);
        }

        // min_min_c <= count <= max_max_c
        let atomic_lb = self.count.atomic_greater_than(min_min_c as i32);
        let atomic_ub = self.count.atomic_less_than(max_max_c as i32);
        consistent &= state.apply(&atomic_lb);
        consistent &= state.apply(&atomic_ub);

        !consistent
    }
}

// enum BoundType {
//     MIN,
//     MAX,
// }
#[derive(Clone, Debug)]
pub struct Cdfa {
    num_states: u32,
    num_inputs: u32,
    transition_matrix: Vec<Vec<u32>>,
    initial_state: u32,
    inc: Vec<Vec<u32>>,
}

type InsertFunc<K, V> = fn(&mut HashMap<K, V>, K, V);

fn insert_min<K: Hash + Eq, V: PartialOrd>(hm: &mut HashMap<K, V>, k: K, v: V) {
    match hm.get(&k) {
        Some(ref_v) => {
            if v < *ref_v {
                let _ = hm.insert(k, v);
            }
        }
        None => {
            let _ = hm.insert(k, v);
        }
    };
}

fn insert_max<K: Hash + Eq, V: PartialOrd>(hm: &mut HashMap<K, V>, k: K, v: V) {
    match hm.get(&k) {
        Some(ref_v) => {
            if v > *ref_v {
                let _ = hm.insert(k, v);
            }
        }
        None => {
            let _ = hm.insert(k, v);
        }
    };
}

fn compute_qcf_for_check(
    sequence_domains: &Vec<Vec<usize>>,
    c_dfa: &Cdfa,
    qcf_table: &mut Vec<Vec<(u32, (u32, u32))>>,
    i: usize,
) {
    let n = sequence_domains.len();
    let index = if i > n { n } else { i };

    if index < qcf_table.len() {
        return;
    }

    if i == 0 {
        qcf_table.insert(0, vec![(c_dfa.initial_state, (0, 0))]);
        return;
    }

    compute_qcf_for_check(sequence_domains, c_dfa, qcf_table, index - 1);
    let pairs = qcf_table.get(index - 1).unwrap();

    let symbols = sequence_domains.get(index - 1).unwrap();

    let mut new_min_pairs: HashMap<u32, u32> = HashMap::default();
    let mut new_max_pairs: HashMap<u32, u32> = HashMap::default();

    for (q, (min_count, max_count)) in pairs.iter().map(|&(q, counts)| (q as usize, counts)) {
        for &l in symbols.iter() {
            let new_q = c_dfa.transition_matrix[q][l];
            let new_min_count = min_count + c_dfa.inc[q][l];
            let new_max_count = max_count + c_dfa.inc[q][l];

            insert_min(&mut new_min_pairs, new_q, new_min_count);
            insert_max(&mut new_max_pairs, new_q, new_max_count);
        }
    }

    let mut new_vec = vec![];
    for q in 1..(c_dfa.num_states + 1) {
        if new_min_pairs.contains_key(&q) && new_max_pairs.contains_key(&q) {
            new_vec.push((
                q,
                (
                    *new_min_pairs.get(&q).unwrap(),
                    *new_max_pairs.get(&q).unwrap(),
                ),
            ));
        }
    }

    qcf_table.insert(index, new_vec);
}

fn compute_qcb_and_qcf_for_check(
    sequence_domains: &Vec<Vec<usize>>,
    c_dfa: &Cdfa,
    qcf_table: &mut Vec<Vec<(u32, (u32, u32))>>,
    qcb_table: &mut Vec<Vec<(u32, (u32, u32))>>,

    i: usize,
) {
    let n = sequence_domains.len();
    let index = if i > n { n } else { i };

    if index < qcb_table.len() {
        return;
    }

    if index == n {
        compute_qcf_for_check(sequence_domains, c_dfa, qcf_table, n);
        qcb_table.insert(
            0,
            qcf_table
                .get(n)
                .unwrap()
                .iter()
                .map(|&(q, _)| (q, (0, 0)))
                .collect_vec(),
        );
        return;
    }

    compute_qcb_and_qcf_for_check(sequence_domains, c_dfa, qcf_table, qcb_table, index + 1);
    let pairs = qcb_table.get(n - index - 1).unwrap();

    let mut new_min_pairs: HashMap<u32, u32> = HashMap::default();
    let mut new_max_pairs: HashMap<u32, u32> = HashMap::default();

    let symbols = sequence_domains.get(index).unwrap();

    for &(q, (min_c, max_c)) in pairs.iter() {
        for &l in symbols.iter() {
            for prev_q in 0..c_dfa.num_states {
                if c_dfa.transition_matrix[prev_q as usize][l] == q {
                    let new_min_c = min_c + c_dfa.inc[prev_q as usize][l];
                    let new_max_c = max_c + c_dfa.inc[prev_q as usize][l];

                    insert_min(&mut new_min_pairs, prev_q, new_min_c);
                    insert_max(&mut new_max_pairs, prev_q, new_max_c);
                }
            }
        }
    }

    let mut new_vec = vec![];
    for q in 1..(c_dfa.num_states + 1) {
        if new_min_pairs.contains_key(&q) && new_max_pairs.contains_key(&q) {
            new_vec.push((
                q,
                (
                    *new_min_pairs.get(&q).unwrap(),
                    *new_max_pairs.get(&q).unwrap(),
                ),
            ));
        }
    }

    qcb_table.insert(n - index, new_vec);
}

fn compute_qcf<Var: IntegerVariable + 'static>(
    sequence: &[Var],
    c_dfa: &Cdfa,
    context: &PropagationContext,
    qcf_table: &mut Vec<Vec<(u32, u32)>>,
    insert_fn: InsertFunc<u32, u32>,
    i: usize,
) {
    let n = sequence.len();
    let index = if i > n { n } else { i };

    if index < qcf_table.len() {
        return;
    }

    if i == 0 {
        qcf_table.insert(0, vec![(c_dfa.initial_state, 0)]);
        return;
    }

    compute_qcf(sequence, c_dfa, context, qcf_table, insert_fn, index - 1);
    let pairs = qcf_table.get(index - 1).unwrap();

    let var = sequence.get(index - 1).unwrap();

    let mut new_pairs: HashMap<u32, u32> = HashMap::default();

    for (q, c) in pairs.iter().map(|&(q, c)| (q as usize, c)) {
        for l in context.iterate_domain(var).map(|l| l as usize - 1) {
            let new_q = c_dfa.transition_matrix[q][l];
            let new_c = c + c_dfa.inc[q][l];

            insert_fn(&mut new_pairs, new_q, new_c);
        }
    }

    let new_vec = new_pairs
        .iter()
        .map(|(&q, &c)| (q, c))
        .sorted_by(|(q1, _), (q2, _)| q1.cmp(q2))
        .collect_vec();

    qcf_table.insert(index, new_vec);
}

fn compute_qcb_and_qcf<Var: IntegerVariable + 'static>(
    sequence: &[Var],
    c_dfa: &Cdfa,
    context: &PropagationContext,
    qcb_table: &mut Vec<Vec<(u32, u32)>>,
    qcf_table: &mut Vec<Vec<(u32, u32)>>,
    insert_fn: InsertFunc<u32, u32>,
    i: usize,
) {
    let n = sequence.len();
    let index = if i > n { n } else { i };

    if index < qcb_table.len() {
        return;
    }

    if index == n {
        compute_qcf(sequence, c_dfa, context, qcf_table, insert_fn, n);
        qcb_table.insert(
            0,
            qcf_table
                .get(n)
                .unwrap()
                .iter()
                .map(|&(q, _)| (q, 0))
                .collect_vec(),
        );
        return;
    }

    compute_qcb_and_qcf(
        sequence,
        c_dfa,
        context,
        qcb_table,
        qcf_table,
        insert_fn,
        index + 1,
    );
    let pairs = qcb_table.get(n - index - 1).unwrap();

    let var = sequence
        .get(index)
        .unwrap_or_else(|| panic!(" {n}: {i} => {index}"));

    let mut new_pairs: HashMap<u32, u32> = HashMap::default();

    for &(q, c) in pairs.iter() {
        for l in context.iterate_domain(var).map(|l| l as usize - 1) {
            for prev_q in 0..c_dfa.num_states {
                if c_dfa.transition_matrix[prev_q as usize][l] == q {
                    let new_c = c + c_dfa.inc[prev_q as usize][l];

                    insert_fn(&mut new_pairs, prev_q, new_c);
                }
            }
        }
    }

    let new_vec = new_pairs
        .iter()
        .map(|(&q, &c)| (q, c))
        .sorted_by(|(q1, _), (q2, _)| q1.cmp(q2))
        .collect_vec();
    qcb_table.insert(n - index, new_vec);
}

fn combine_table(min_table: &[(u32, u32)], max_table: &[(u32, u32)]) -> Vec<(u32, u32, u32)> {
    let mut i: usize = 0;
    let mut j: usize = 0;
    let mut table = Vec::new();

    while let (Some(&(q_min, min_c)), Some(&(q_max, max_c))) = (min_table.get(i), max_table.get(j))
    {
        if q_min < q_max {
            i += 1;
        } else if q_min > q_max {
            j += 1;
        } else {
            i += 1;
            j += 1;
            table.push((q_min, min_c, max_c));
        }
    }

    table
}

fn concat_conjunctions(
    a: &PropositionalConjunction,
    b: &PropositionalConjunction,
) -> PropositionalConjunction {
    a.iter().chain(b.iter()).copied().collect()
}
