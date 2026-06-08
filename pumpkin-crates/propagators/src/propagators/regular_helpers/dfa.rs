use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::Debug;
use std::hash::Hash;


use super::layered_graph::Letter;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DFA<Item>
where
    Item: Hash + Eq,
{
    pub(crate) states: usize,
    pub(crate) alphabet: HashSet<Item>,
    pub(crate) transitions: HashMap<(usize, Item), usize>,
    pub(crate) starting_state: usize,
    pub(crate) accepting_states: HashSet<usize>,
}

impl DFA<Letter> {
    pub(crate) fn from(
        num_states: u32,
        num_inputs: u32,
        transition_matrix: Vec<Vec<i32>>,
        initial_state: i32,
        accepting_states: Vec<i32>,
    ) -> Self {
        let alphabet: HashSet<Letter> = (1..=num_inputs as Letter).collect();

        let transitions: HashMap<(usize, Letter), usize> = transition_matrix
            .iter()
            .enumerate()
            .flat_map(|(state_idx, row)| {
                row.iter()
                    .enumerate()
                    .filter_map(move |(input_idx, &next_state)| {
                        // MZN convention: d[i,j] = 0 means dead/trap state. Skip.
                        if next_state == 0 {
                            return None;
                        }
                        Some((
                            (state_idx + 1, (input_idx + 1) as Letter),
                            next_state as usize,
                        ))
                    })
            })
            .collect();

        let accepting_states: HashSet<usize> =
            accepting_states.iter().map(|&s| s as usize).collect();

        DFA {
            states: num_states as usize,
            alphabet,
            transitions,
            starting_state: initial_state as usize,
            accepting_states,
        }
    }
}
