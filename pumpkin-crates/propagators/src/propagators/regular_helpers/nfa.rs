use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::Debug;
use std::hash::Hash;

use super::layered_graph::Letter;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NFA<Item>
where
    Item: Hash + Eq,
{
    pub(crate) states: usize,
    pub(crate) alphabet: HashSet<Item>,
    pub(crate) transitions: HashMap<(usize, Item), Vec<usize>>,
    pub(crate) starting_state: usize,
    pub(crate) accepting_states: HashSet<usize>,
}

impl NFA<Letter> {
    pub fn from(
        num_states: u32,
        num_inputs: u32,
        transition_matrix: Vec<Vec<Vec<i32>>>,
        initial_state: i32,
        accepting_states: Vec<i32>,
    ) -> Self {
        let alphabet: HashSet<Letter> = (0..num_inputs as Letter).collect();

        let transitions: HashMap<(usize, Letter), Vec<usize>> = transition_matrix
            .into_iter()
            .enumerate()
            .flat_map(|(state, row)| {
                row.into_iter()
                    .enumerate()
                    .filter_map(move |(input, next_states)| {
                        if next_states.is_empty() {
                            None
                        } else {
                            let targets: Vec<usize> =
                                next_states.into_iter().map(|q| q as usize).collect();
                            Some(((state, input as Letter), targets))
                        }
                    })
            })
            .collect();

        let accepting_states: HashSet<usize> =
            accepting_states.iter().map(|&s| s as usize).collect();

        NFA {
            states: num_states as usize,
            alphabet,
            transitions,
            starting_state: initial_state as usize,
            accepting_states,
        }
    }
}
