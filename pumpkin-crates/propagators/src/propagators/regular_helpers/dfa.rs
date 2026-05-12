use std::fmt::Debug;
use std::hash::Hash;

use itertools::Itertools;

use std::collections::HashMap;
use std::collections::HashSet;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DFA<Item>
where
    Item: Hash + Eq,
{
    pub(crate) states: usize,
    pub(crate) alphabet: HashSet<Item>,
    pub(crate) transitions: HashMap<(usize, Item), usize>,
    pub(crate) starting_state: usize,
    pub(crate) accepting_states: HashSet<usize>,
}