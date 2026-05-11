use pumpkin_core::declare_inference_label;
use pumpkin_core::proof::ConstraintTag;
use pumpkin_core::proof::InferenceCode;
use pumpkin_core::propagation::PropagationContext;
use pumpkin_core::propagation::Propagator;
use pumpkin_core::propagation::PropagatorConstructor;
use pumpkin_core::propagation::PropagatorConstructorContext;
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

    fn create(self, context: PropagatorConstructorContext) -> Self::PropagatorImpl {
        todo!()
    }
}

#[derive(Clone, Debug)]
pub struct RegularCdfaPropagator<Var, CVar> {
    pub sequence: Box<[Var]>,
    pub num_states: u32,
    pub num_inputs: u32,
    pub transition_matrix: Vec<Vec<i32>>,
    pub initial_state: i32,
    pub inc: Vec<Vec<i32>>,
    pub count: CVar,

    inference_code: InferenceCode,
}

impl<Var: IntegerVariable + 'static, CVar: IntegerVariable + 'static> Propagator
    for RegularCdfaPropagator<Var, CVar>
{
    fn name(&self) -> &str {
        todo!()
    }

    fn propagate_from_scratch(&self, context: PropagationContext) -> PropagationStatusCP {
        todo!()
    }
}
