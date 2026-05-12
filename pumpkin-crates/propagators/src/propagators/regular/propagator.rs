use pumpkin_core::declare_inference_label;
use pumpkin_core::proof::ConstraintTag;
use pumpkin_core::proof::InferenceCode;
use pumpkin_core::propagation::PropagationContext;
use pumpkin_core::propagation::Propagator;
use pumpkin_core::propagation::PropagatorConstructor;
use pumpkin_core::propagation::PropagatorConstructorContext;
use pumpkin_core::propagation::LocalId;
use pumpkin_core::propagation::DomainEvents;
use pumpkin_core::state::PropagationStatusCP;
use pumpkin_core::variables::IntegerVariable;

use crate::propagators::regular_helpers::{DFA, LayeredGraph};

#[derive(Clone, Debug)]
pub struct RegularPropagatorConstructor<Var> {
    pub sequence: Box<[Var]>,
    pub num_states: u32,
    pub num_inputs: u32,
    pub transition_matrix: Vec<Vec<i32>>,
    pub initial_state: i32,
    pub accepting_states: Vec<i32>,

    pub constraint_tag: ConstraintTag,
}
declare_inference_label!(RegularDfa);

impl<Var: IntegerVariable + 'static> PropagatorConstructor for RegularPropagatorConstructor<Var> {
    type PropagatorImpl = RegularPropagator<Var>;

    fn create(self, mut context: PropagatorConstructorContext) -> Self::PropagatorImpl {
      let RegularPropagatorConstructor {
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
          context.register(var.clone(), DomainEvents::BOUNDS, LocalId::from(idx as u32));
      }

      // Build Internal Graph
      let dfa = DFA::from(num_states, num_inputs, transition_matrix, initial_state, accepting_states);
      let internal_graph = LayeredGraph::from((dfa, sequence.len()));

      // Return Constructed Regular Propagator
      RegularPropagator {
          sequence,
          internal_graph,
          inference_code: InferenceCode::new(constraint_tag, RegularDfa),
      }
    }
}

#[derive(Clone, Debug)]
pub struct RegularPropagator<Var> {
    sequence: Box<[Var]>,
    internal_graph: LayeredGraph,
    inference_code: InferenceCode,
}

impl<Var: IntegerVariable + 'static> Propagator for RegularPropagator<Var> {
    fn name(&self) -> &str {
        "RegularDFAPropagator"
    }

    fn propagate_from_scratch(&self, context: PropagationContext) -> PropagationStatusCP {
        todo!()
    }
}
