use pumpkin_core::constraints::Constraint;
use pumpkin_core::proof::ConstraintTag;
use pumpkin_core::variables::IntegerVariable;
use pumpkin_propagators::regular_cdfa::RegularCdfaPropagatorConstructor;

pub fn regular_cdfa<Var: IntegerVariable + 'static, CVar: IntegerVariable + 'static>(
    sequence: impl Into<Box<[Var]>>,
    num_states: u32,
    num_inputs: u32,
    transition_matrix: Vec<Vec<i32>>,
    initial_state: i32,
    inc: Vec<Vec<i32>>,
    count: CVar,
    constraint_tag: ConstraintTag,
) -> impl Constraint {
    RegularCdfaPropagatorConstructor {
        sequence: sequence.into(),
        num_states,
        num_inputs,
        transition_matrix,
        initial_state,
        inc,
        count,
        constraint_tag,
    }
}
