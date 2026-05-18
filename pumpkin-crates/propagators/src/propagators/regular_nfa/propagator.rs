use std::collections::HashSet;

use pumpkin_checking::AtomicConstraint;
use pumpkin_checking::CheckerVariable;
use pumpkin_checking::InferenceChecker;
use pumpkin_checking::VariableState;
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
use pumpkin_core::state::propagator_conflict;
use pumpkin_core::variables::IntegerVariable;

use crate::propagators::regular_helpers::{LayeredGraph, Letter, NFA};

#[derive(Clone, Debug)]
pub struct RegularNfaPropagatorConstructor<Var> {
    pub sequence: Box<[Var]>,
    pub num_states: u32,
    pub num_inputs: u32,
    pub transition_matrix: Vec<Vec<Vec<i32>>>,
    pub initial_state: i32,
    pub accepting_states: Vec<i32>,

    pub constraint_tag: ConstraintTag,
}
declare_inference_label!(RegularNfa);

impl<Var: IntegerVariable + 'static> PropagatorConstructor
    for RegularNfaPropagatorConstructor<Var>
{
    type PropagatorImpl = RegularNfaPropagator<Var>;

    fn add_inference_checkers(&self, mut checkers: InferenceCheckers<'_>) {
        // Construct NFA
        let nfa = NFA::from(
            self.num_states,
            self.num_inputs,
            self.transition_matrix.clone(),
            self.initial_state,
            self.accepting_states.clone(),
        );
        
        // Add Inference Checker
        checkers.add_inference_checker(
            InferenceCode::new(self.constraint_tag, RegularNfa),
            Box::new(RegularNfaChecker {
                sequence: self.sequence.clone(),
                nfa,
            }),
        );
    }

    
    fn create(self, mut context: PropagatorConstructorContext) -> Self::PropagatorImpl {
        let RegularNfaPropagatorConstructor {
            sequence,
            num_states,
            num_inputs,
            transition_matrix,
            initial_state,
            accepting_states,
            constraint_tag,
        } = self;

        // Register Variables with Solver
        for (idx, var) in sequence.iter().enumerate() {
            context.register(var.clone(), DomainEvents::ANY_INT, LocalId::from(idx as u32));
        }

        // Build NFA and Internal Graph
        let nfa = NFA::from(
            num_states,
            num_inputs,
            transition_matrix,
            initial_state,
            accepting_states,
        );
        let internal_graph = LayeredGraph::from((nfa, sequence.len()));

        // Return Constructed Regular_NFA Propagator
        RegularNfaPropagator {
            sequence,
            internal_graph,
            inference_code: InferenceCode::new(constraint_tag, RegularNfa),
        }
    }
}

#[derive(Clone, Debug)]
pub struct RegularNfaPropagator<Var> {
    sequence: Box<[Var]>,
    internal_graph: LayeredGraph,
    inference_code: InferenceCode,
}

impl<Var: IntegerVariable + 'static> Propagator for RegularNfaPropagator<Var> {
    fn name(&self) -> &str {
        "RegularNFAPropagator"
    }

    // Propagation Three Step Approach:
      // Step 1: Update Graph to Represent Current Domain Values (Kill_Externally_Removed)
      // Step 2: Check for Conflicts (i.e. No Accepting Paths Exist)
      // Step 3: Core Propagation -> Remove Values with no Future Accepting Paths
    fn propagate_from_scratch(&self, mut context: PropagationContext) -> PropagationStatusCP {
        let mut graph = self.internal_graph.clone();

        let removed = self.kill_externally_removed(&context, &mut graph);

        if let Some(conflict) = self.detect_conflict(&graph, removed) {
            return conflict;
        }

        self.propagate_into_domains(&mut context, &graph)
    }
}

impl<Var: IntegerVariable + 'static> RegularNfaPropagator<Var> {
    // Updates Layered Graph to Represent Current Domain Values
    fn kill_externally_removed(
        &self,
        context: &PropagationContext<'_>,
        graph: &mut LayeredGraph,
    ) -> HashSet<(usize, i32)> {
        let mut removed: HashSet<(usize, i32)> = HashSet::new();

        // Take Set Difference Between Values Alive in Graph and Values Alive in Variable Domain
        for (idx, var) in self.sequence.iter().enumerate() {
            let alive_in_graph: HashSet<i32> = graph.living_values(idx).into_iter().collect();
            let in_domain: HashSet<i32> = context.iterate_domain(var).collect();

            // Kill Values in Set Difference
            for &letter in alive_in_graph.difference(&in_domain) {
                graph.kill_value(idx, letter);
                let _ = removed.insert((idx, letter));
            }
        }

        // Return Removed Values
        removed
    }

    // Check if Current Domain Values have Accepting Path -> Otherwise, Construct Conflict Explanation
    fn detect_conflict(
        &self,
        graph: &LayeredGraph,
        removed: HashSet<(usize, i32)>,
    ) -> Option<PropagationStatusCP> {
        if graph.is_consistent() {
            return None;
        }

        // Constructed Conflict Explanation: Combination of Previously Removed Values
        let reason: PropositionalConjunction = removed
            .into_iter()
            .map(|(idx, letter)| predicate![self.sequence[idx] != letter])
            .collect();

        Some(propagator_conflict(reason, &self.inference_code))
    }

    // Core Propagation -> Remove Values with no Future Accepting Paths
    fn propagate_into_domains(
        &self,
        context: &mut PropagationContext<'_>,
        graph: &LayeredGraph,
    ) -> PropagationStatusCP {
        for (idx, var) in self.sequence.iter().enumerate() {
            let alive_in_graph: HashSet<i32> = graph.living_values(idx).into_iter().collect();
            let in_domain: Vec<i32> = context.iterate_domain(var).collect();

            // If No Future Accepting Path Exists with Value, Remove from Domain with Generated Explanation
            for value in in_domain {
                if alive_in_graph.contains(&value) {
                    continue;
                }

                let reason: PropositionalConjunction = graph
                    .explain_removal(idx, value)
                    .into_iter()
                    .map(|(j, letter)| predicate![self.sequence[j] != letter])
                    .collect();

                context.post(
                    predicate![var != value],
                    (reason, &self.inference_code),
                )?;
            }
        }

        Ok(())
    }
}

#[derive(Clone, Debug)]
pub struct RegularNfaChecker<Var> {
    sequence: Box<[Var]>,
    nfa: NFA<Letter>,
}

impl<Var, Atomic> InferenceChecker<Atomic> for RegularNfaChecker<Var>
where
    Var: CheckerVariable<Atomic>,
    Atomic: AtomicConstraint,
{
    fn check(&self, state: VariableState<Atomic>, _: &[Atomic], _: Option<&Atomic>) -> bool {
        // Track Reachable States
        let mut reachable: HashSet<usize> = HashSet::new();
        let _ = reachable.insert(self.nfa.starting_state);

        // Iterate Through Layers -> Track Reachable States
        for var in self.sequence.iter() {
            let mut next_reachable: HashSet<usize> = HashSet::new();
            
            // For Each Input in Each Reachble State
            for &q in &reachable {
                for &letter in &self.nfa.alphabet {
                    // Skip Inputs Removed from Variable Domain
                    if !var.induced_domain_contains(&state, letter) {
                        continue;
                    }

                    // Add Next State/s to Next_Reachable
                    if let Some(end_states) = self.nfa.transitions.get(&(q, letter)) {
                        for &q_next in end_states {
                            let _ = next_reachable.insert(q_next);
                        }
                    }
                }
            }

            // Update Reachable
            reachable = next_reachable;

            // No States are Reachable -> Conflict Detected
            if reachable.is_empty() {
                return true;
            }
        }

        // Conflict Detected if Accepting States and Reachable are Disjoint
        reachable.is_disjoint(&self.nfa.accepting_states)
    }
}

#[cfg(test)]
mod tests {
    use pumpkin_checking::TestAtomic;
    use pumpkin_checking::VariableState;
    use pumpkin_core::state::State;

    use super::*;
    use crate::StateExt;

    // 2-state NFA accepting binary strings that start with `0`:
    //   - state 0: initial, non-accepting.
    //   - state 1: accepting.
    //   - state 0: letter 0 -> {0, 1} (nondeterministic, deliberately involves multi-successors), letter 1 -> {} (trap).
    //   - state 1: letter 0 -> {1},    letter 1 -> {1}.
    fn starts_with_zero_nfa() -> NFA<Letter> {
        NFA::from(
            /* num_states */ 2,
            /* num_inputs */ 2,
            /* transition_matrix */
            vec![
                vec![vec![0, 1], vec![]],
                vec![vec![1], vec![1]],
            ],
            /* initial_state */ 0,
            /* accepting_states */ vec![1],
        )
    }

    fn starts_with_zero_transition_matrix() -> Vec<Vec<Vec<i32>>> {
        vec![
            vec![vec![0, 1], vec![]],
            vec![vec![1], vec![1]],
        ]
    }

    // Propagator Tests
    #[test]
    fn first_letter_propagated_to_zero_on_length_two() {
        let mut state = State::default();

        let x0 = state.new_interval_variable(0, 1, None);
        let x1 = state.new_interval_variable(0, 1, None);
        let constraint_tag = state.new_constraint_tag();

        let _ = state.add_propagator(RegularNfaPropagatorConstructor {
            sequence: vec![x0, x1].into(),
            num_states: 2,
            num_inputs: 2,
            transition_matrix: starts_with_zero_transition_matrix(),
            initial_state: 0,
            accepting_states: vec![1],
            constraint_tag,
        });
        state.propagate_to_fixed_point().expect("no empty domains");

        state.assert_bounds(x0, 0, 0);
        state.assert_bounds(x1, 0, 1);
    }

    #[test]
    fn only_first_letter_is_forced_on_length_three() {
        let mut state = State::default();

        let x0 = state.new_interval_variable(0, 1, None);
        let x1 = state.new_interval_variable(0, 1, None);
        let x2 = state.new_interval_variable(0, 1, None);
        let constraint_tag = state.new_constraint_tag();

        let _ = state.add_propagator(RegularNfaPropagatorConstructor {
            sequence: vec![x0, x1, x2].into(),
            num_states: 2,
            num_inputs: 2,
            transition_matrix: starts_with_zero_transition_matrix(),
            initial_state: 0,
            accepting_states: vec![1],
            constraint_tag,
        });
        state.propagate_to_fixed_point().expect("no empty domains");

        state.assert_bounds(x0, 0, 0);
        state.assert_bounds(x1, 0, 1);
        state.assert_bounds(x2, 0, 1);
    }

    #[test]
    fn conflict_when_first_letter_pre_assigned_one() {
        let mut state = State::default();

        let x0 = state.new_interval_variable(1, 1, None);
        let x1 = state.new_interval_variable(0, 1, None);
        let constraint_tag = state.new_constraint_tag();

        let _ = state.add_propagator(RegularNfaPropagatorConstructor {
            sequence: vec![x0, x1].into(),
            num_states: 2,
            num_inputs: 2,
            transition_matrix: starts_with_zero_transition_matrix(),
            initial_state: 0,
            accepting_states: vec![1],
            constraint_tag,
        });

        assert!(state.propagate_to_fixed_point().is_err());
    }

    // Checker Tests
    #[test]
    fn conflict_detected_on_unsatisfiable_premise() {
        // Force First Letter to One -> Trap at Initial State -> Always UNSAT -> Conflict
        let premises = [TestAtomic {
            name: "x0",
            comparison: pumpkin_checking::Comparison::Equal,
            value: 1,
        }];

        let state = VariableState::prepare_for_conflict_check(premises, None)
            .expect("no conflicting atomics");

        let checker = RegularNfaChecker {
            sequence: vec!["x0", "x1"].into(),
            nfa: starts_with_zero_nfa(),
        };

        assert!(checker.check(state, &premises, None));
    }

    #[test]
    fn no_conflict_detected_on_satisfiable_premise() {
        // Force First Letter to Zero -> Accepting Path "00" Exists -> No Conflict
        let premises = [TestAtomic {
            name: "x0",
            comparison: pumpkin_checking::Comparison::Equal,
            value: 0,
        }];

        let state = VariableState::prepare_for_conflict_check(premises, None)
            .expect("no conflicting atomics");

        let checker = RegularNfaChecker {
            sequence: vec!["x0", "x1"].into(),
            nfa: starts_with_zero_nfa(),
        };

        assert!(!checker.check(state, &premises, None));
    }

    #[test]
    fn conflict_detected_on_valid_premise_consequent() {
        // No Premise -> Consequent is First Letter is 0 -> (Not) Consequent = Conflict
        let premises: [TestAtomic; 0] = [];

        let consequent = Some(TestAtomic {
            name: "x0",
            comparison: pumpkin_checking::Comparison::Equal,
            value: 0,
        });

        let state = VariableState::prepare_for_conflict_check(premises, consequent)
            .expect("no conflicting atomics");

        let checker = RegularNfaChecker {
            sequence: vec!["x0", "x1"].into(),
            nfa: starts_with_zero_nfa(),
        };

        assert!(checker.check(state, &premises, consequent.as_ref()));
    }
}
