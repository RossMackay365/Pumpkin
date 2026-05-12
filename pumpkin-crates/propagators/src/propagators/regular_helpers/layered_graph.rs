use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::VecDeque;
use std::fmt::Display;
use std::fmt::Debug;
use std::hash::Hash;

use itertools::Itertools;

use super::DrawEdge;
use super::DrawNode;
use super::DrawnGraph;
use super::GraphDraw;

#[derive(Debug, Clone)]
#[allow(dead_code, reason = "not implemented yet")]
pub struct LayeredGraph {
    alphabet: Vec<Letter>,
    layers: Vec<Layer>,
    arcs: Arcs,
    arc_life: HashMap<Arc, bool>,
    node_life: HashMap<Node, bool>,
    accepting: Vec<usize>,
    starting: usize,
    domain: HashMap<usize, HashSet<Letter>>,
    state_count: usize,
}

type Letter = i32;

type StartLayer = usize;
type State = usize;
type StartState = State;
type EndState = State;

type Layer = HashSet<Node>;

type Assignment = (usize, Letter);

#[derive(Debug, Clone)]
struct Arcs {
    outbound: HashMap<Node, HashSet<Arc>>,
    inbound: HashMap<Node, HashSet<Arc>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash)]
pub(crate) struct Node {
    layer: usize,
    state: usize,
}

impl Display for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}{}", self.state, self.layer)?;

        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash)]
struct Arc {
    start_layer: StartLayer,
    start_state: StartState,
    end_state: EndState,
    letter: Letter,
}

impl Arc {
    fn start(&self) -> Node {
        Node {
            layer: self.start_layer,
            state: self.start_state,
        }
    }

    fn end(&self) -> Node {
        Node {
            layer: self.start_layer + 1,
            state: self.end_state,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
#[allow(dead_code, reason = "usage not implemented yet")]
enum Direction {
    None = 0,
    Forward = 1,
    Backward = 2,
    Both = 3,
}

impl From<(DFA<Letter>, usize)> for LayeredGraph {
    fn from((dfa, var_count): (DFA<Letter>, usize)) -> Self {
        let layer_count = var_count + 1;
        let state_count = dfa.states;

        // Forward pass
        //
        // Create the layered graph by initializing with the starting node.
        // Then, for each layer,
        // iterate over all current nodes,
        // and add reachable nodes in the next layer.
        let (layers, node_life, arcs, arc_life) = {
            let initial_node = Node {
                layer: 0,
                state: dfa.starting_state,
            };
            let mut queue = VecDeque::from(vec![initial_node]);
            let mut next_queue = VecDeque::new();

            let mut layers = Vec::new();
            let mut outbound_arcs: HashMap<Node, HashSet<Arc>> = HashMap::default();
            let mut inbound_arcs: HashMap<Node, HashSet<Arc>> = HashMap::default();
            let mut node_life = HashMap::default();
            let mut arc_life: HashMap<Arc, bool> = HashMap::default();

            for layer_index in 0..layer_count {
                let mut layer = HashSet::default();

                while let Some(node) = queue.pop_front() {
                    let _ = layer.insert(node);
                    let _ = node_life.insert(node, true);

                    if layer_index < var_count {
                        for letter in &dfa.alphabet {
                            if let Some(end_state) = dfa.transitions.get(&(node.state, *letter)) {
                                let arc = Arc {
                                    start_layer: layer_index,
                                    start_state: node.state,
                                    end_state: *end_state,
                                    letter: *letter,
                                };

                                let to_node = arc.end();

                                next_queue.push_back(to_node);
                                let _ = arc_life.insert(arc, true);
                                let _ = outbound_arcs.entry(node).or_default().insert(arc);
                                let _ = inbound_arcs.entry(to_node).or_default().insert(arc);
                            }
                        }
                    }
                }

                layers.push(layer);

                std::mem::swap(&mut queue, &mut next_queue);
            }

            let arcs = Arcs {
                outbound: outbound_arcs,
                inbound: inbound_arcs,
            };

            (layers, node_life, arcs, arc_life)
        };
        debug_assert_eq!(layers.len(), layer_count);

        // Move accepting nodes
        let mut accepting = Vec::from_iter(dfa.accepting_states);
        accepting.sort();

        // Set starting state
        let starting = dfa.starting_state;

        // Domain
        let mut domain = HashMap::default();
        for variable_index in 0..var_count {
            let _ = domain.insert(variable_index, dfa.alphabet.clone());
        }

        // Move alphabet
        let mut alphabet = Vec::from_iter(dfa.alphabet);
        alphabet.sort();

        let mut layered_graph = LayeredGraph {
            alphabet,
            layers,
            arcs,
            arc_life,
            node_life,
            accepting,
            starting,
            domain,
            state_count,
        };

        layered_graph.backward_pass();

        layered_graph
    }
}

impl LayeredGraph {
    fn starting_node(&self) -> Node {
        Node {
            layer: 0,
            state: self.starting,
        }
    }

    /// Deletes nodes which cannot reach the end
    fn backward_pass(&mut self) {
        let last_layer = self.layers.len() - 1;
        let accepting = self.accepting.iter().flat_map(|state| {
            let node = Node {
                state: *state,
                layer: last_layer,
            };
            self.layers[last_layer].get(&node)
        });

        let mut marked: HashSet<Node> = HashSet::default();

        let mut queue = VecDeque::from_iter(accepting.cloned());
        let mut next_queue = VecDeque::new();

        while !queue.is_empty() {
            while let Some(node) = queue.pop_front() {
                let _ = marked.insert(node);
                for arc in self.inbound_edges_all(node) {
                    next_queue.push_back(arc.start());
                }
            }

            std::mem::swap(&mut queue, &mut next_queue);
        }

        let all_nodes = self.layers.iter().flatten().cloned().collect_vec();

        for node in all_nodes {
            if !marked.contains(&node) {
                self.delete_node(node);
            }
        }
    }

    fn delete_edge(&mut self, arc: Arc) {
        if let Some(set) = self.arcs.outbound.get_mut(&arc.start()) {
            let _ = set.remove(&arc);
        };
        if let Some(set) = self.arcs.inbound.get_mut(&arc.end()) {
            let _ = set.remove(&arc);
        };
        let _ = self.arc_life.remove(&arc);
    }

    fn delete_node(&mut self, node: Node) {
        let outbound_arcs = self
            .arcs
            .outbound
            .get(&node)
            .into_iter()
            .flatten()
            .cloned()
            .collect_vec();
        for arc in outbound_arcs {
            self.delete_edge(arc);
        }

        let inbound_arcs = self
            .arcs
            .inbound
            .get(&node)
            .into_iter()
            .flatten()
            .cloned()
            .collect_vec();
        for arc in inbound_arcs {
            self.delete_edge(arc);
        }

        let _ = self.arcs.outbound.remove(&node);
        let _ = self.arcs.inbound.remove(&node);
        let _ = self.layers[node.layer].remove(&node);
        let _ = self.node_life.remove(&node);
    }

    pub fn living_values(&self, variable_index: usize) -> Vec<Letter> {
        debug_assert!(variable_index + 1 < self.layers.len());
        let mut values = HashSet::new();
        for node in &self.layers[variable_index] {
            if !self.node_life[node] {
                continue;
            }
            for edge in self.outbound_edges(*node) {
                if self.is_alive(*edge) {
                    let _ = values.insert(edge.letter);
                }
            }
        }
        values.into_iter().collect()
    }

    pub fn kill_value(&mut self, variable_index: usize, value: Letter) {
        let _ = self
            .domain
            .get_mut(&variable_index)
            .expect("each variable has a domain")
            .remove(&value);

        let edges_to_kill = self.layers[variable_index]
            .iter()
            // .filter(|node| self.layer_life[node.layer][node.state])
            .flat_map(|node| self.outbound_edges(*node))
            .filter(|edge| edge.letter == value)
            .cloned()
            .collect_vec();

        edges_to_kill
            .into_iter()
            .for_each(|edge| self.kill_edge(edge, Direction::Both));
    }

    fn is_alive(&self, edge: Arc) -> bool {
        self.arc_life[&edge]
    }

    fn is_in_domain(&self, edge: Arc) -> bool {
        self.domain[&edge.start_layer].contains(&edge.letter)
    }

    /// Returns true if the node ought to be alive.
    fn check_node(&mut self, node: Node) -> bool {
        let has_inbound = self.inbound_edges(node).into_iter().next().is_some();
        let has_outbound = self.outbound_edges(node).into_iter().next().is_some();
        let is_first = node.layer == 0 && self.starting == node.state;
        let is_last = node.layer == self.layers.len() - 1 && self.accepting.contains(&node.state);
        if !is_first && !has_inbound {
            return false;
        }
        if !is_last && !has_outbound {
            return false;
        }
        true
    }

    fn kill_node(&mut self, node: Node, direction: Direction) {
        if let Some(life) = self.node_life.get_mut(&node) {
            *life = false;
        } else {
            // If the node was never initialized, early quit
            return;
        }

        if direction as usize & 1 != 0 {
            for edge in self.outbound_edges(node).into_iter().cloned().collect_vec() {
                self.kill_edge(edge, Direction::Forward);
            }
        }
        if direction as usize & 2 != 0 {
            for edge in self.inbound_edges(node).into_iter().cloned().collect_vec() {
                self.kill_edge(edge, Direction::Backward)
            }
        }
    }

    fn kill_edge(&mut self, edge: Arc, direction: Direction) {
        let was_alive = self.arc_life.insert(edge, false);

        if let Some(was_alive) = was_alive {
            if was_alive {
                if direction as usize & 1 != 0 {
                    let node = edge.end();
                    let should_live = self.check_node(node);
                    if !should_live {
                        self.kill_node(node, Direction::Both);
                    }
                }
                if direction as usize & 2 != 0 {
                    let node = edge.start();
                    if !self.check_node(node) {
                        self.kill_node(node, Direction::Both);
                    }
                }
            }
        }
    }

    fn outbound_edges_all(&self, node: Node) -> impl IntoIterator<Item = &Arc> {
        self.arcs.outbound.get(&node).into_iter().flatten()
    }

    fn outbound_edges(&self, node: Node) -> impl IntoIterator<Item = &Arc> {
        self.outbound_edges_all(node)
            .into_iter()
            .filter(|edge| self.is_alive(**edge))
    }

    fn inbound_edges_all(&self, node: Node) -> impl IntoIterator<Item = &Arc> {
        self.arcs.inbound.get(&node).into_iter().flatten()
    }

    fn inbound_edges(&self, node: Node) -> impl IntoIterator<Item = &Arc> {
        self.inbound_edges_all(node)
            .into_iter()
            .filter(|edge| self.is_alive(**edge))
    }

    fn letter_index(&self, letter: Letter) -> usize {
        self.alphabet
            .iter()
            .position(|other| *other == letter)
            .expect("letter must be in alphabet")
    }

    pub fn explain_removal(
        &self,
        variable_index: usize,
        letter: Letter,
    ) -> impl IntoIterator<Item = Assignment> {
        let reaches_accepting = self
            .reaches_accepting(variable_index, letter)
            .into_iter()
            .collect::<HashSet<_>>();
        let mut explanation: HashSet<(usize, i32)> = HashSet::default();
        let mut queue: HashSet<_> = HashSet::default();
        // Initialize the queue with starting node
        let _ = queue.insert(self.starting_node());
        if cfg![debug_assertions] {
            dbg!(&reaches_accepting);
        }
        while !queue.is_empty() {
            if cfg![debug_assertions] {
                dbg!(&queue);
                dbg!(&explanation);
            }
            for node in &queue {
                for edge in self.outbound_edges_all(*node) {
                    if edge.start_layer != variable_index && reaches_accepting.contains(&edge.end())
                    {
                        let _ = explanation.insert((edge.start_layer, edge.letter));
                    }
                }
            }
            let mut new_queue = HashSet::default();
            for node in queue {
                for edge in self.outbound_edges_all(node) {
                    let allowed_edge = edge.start_layer == variable_index && edge.letter == letter;
                    let general_edge = edge.start_layer != variable_index
                        && !explanation.contains(&(edge.start_layer, edge.letter));
                    if allowed_edge || general_edge {
                        let _ = new_queue.insert(edge.end());
                    }
                }
            }
            queue = new_queue;
        }

        explanation
    }

    /// Find all nodes which reach an accepting state in the last layer,
    /// assuming that given variable has the given value.
    fn reaches_accepting(
        &self,
        variable_index: usize,
        letter: Letter,
    ) -> impl IntoIterator<Item = Node> {
        let mut reaches_accepting: HashSet<Node> = HashSet::default();
        // Initialize using accepting nodes
        let last_layer = self.layers.len() - 1;
        let accepting = self.accepting.iter().flat_map(|state| {
            let node = Node {
                state: *state,
                layer: last_layer,
            };
            self.layers[last_layer].get(&node)
        });
        let mut queue =
            VecDeque::from_iter(accepting.flat_map(|node| self.inbound_edges_all(*node)));

        while let Some(edge) = queue.pop_front() {
            if reaches_accepting.contains(&edge.start()) {
                continue;
            }
            if edge.start_layer == variable_index && edge.letter == letter {
                let node = edge.start();
                let _ = reaches_accepting.insert(node);
                queue.extend(self.inbound_edges_all(node));
            } else if edge.start_layer == variable_index && edge.letter != letter {
                continue;
            } else if self.is_in_domain(*edge) && reaches_accepting.insert(edge.start()) {
                queue.extend(self.inbound_edges_all(edge.start()));
            }
        }

        reaches_accepting
    }

    pub fn is_consistent(&self) -> bool {
        !self.living_values(0).is_empty()
    }

    pub fn count_nodes(&self) -> usize {
        let mut total = 0;

        for layer in &self.layers {
            total += layer.len();
        }

        total
    }
}

impl GraphDraw<Node> for LayeredGraph {
    fn draw(&self) -> DrawnGraph<Node> {
        let mut graph = DrawnGraph::default();

        for nodes in &self.layers {
            for node in nodes {
                let mut modifiers = vec!["state"];
                let x = node.layer as f32 * 2.5;
                let y = node.state as f32;

                let name = format!("$q_{{{}}}^{{{}}}$", node.state, node.layer);

                if !self.node_life[node] {
                    modifiers.push("nearly transparent")
                }

                if node.layer == self.layers.len() - 1 && self.accepting.contains(&node.state) {
                    modifiers.push("accepting");
                }

                let node = DrawNode {
                    modifiers: modifiers.into_iter().map(String::from).collect(),
                    id: *node,
                    x,
                    y,
                    name,
                };

                graph.draw_node(node);
            }
        }

        let mut marked = vec![false; self.alphabet.len()];
        let styles = [
            "dashed",
            "solid",
            "dotted",
            "loosely dotted",
            "densely dashed",
            "dashdotted",
        ];
        for edge in self.arcs.outbound.values().flatten() {
            let mut modifiers = Vec::new();

            if !self.is_alive(*edge) {
                modifiers.push("nearly transparent");
            }

            let mut label = None;

            let letter_index = self.letter_index(edge.letter);
            modifiers.push(styles[letter_index % styles.len()]);
            if !marked[letter_index] && self.is_alive(*edge) {
                label = Some(edge.letter.to_string());
                marked[letter_index] = true;
            }

            if letter_index == 0 {
                modifiers.push("bend left=10");
            } else {
                modifiers.push("bend right=10")
            }

            let edge = DrawEdge {
                modifiers: modifiers.into_iter().map(String::from).collect(),
                from: edge.start(),
                to: edge.end(),
                label,
            };

            graph.draw_edge(edge);
        }

        graph
    }
}