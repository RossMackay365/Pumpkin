use std::fmt::*;

#[derive(Debug, Clone)]
pub(crate) struct DrawNode<Id> {
    pub(crate) modifiers: Vec<String>,
    pub(crate) id: Id,
    pub(crate) x: f32,
    pub(crate) y: f32,
    pub(crate) name: String,
}

impl<Id: Clone + Debug + Display> Display for DrawNode<Id> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        writeln!(
            f,
            "\\node[{}] ({}) at ({}, {}) {{{}}};",
            self.modifiers.join(", "),
            self.id,
            self.x,
            self.y,
            self.name
        )?;

        Ok(())
    }
}

#[derive(Debug, Clone)]
pub(crate) struct DrawEdge<Id> {
    pub(crate) modifiers: Vec<String>,
    pub(crate) from: Id,
    pub(crate) to: Id,
    pub(crate) label: Option<String>,
}

impl<Id: Clone + Debug + Display> Display for DrawEdge<Id> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let label_text = match &self.label {
            Some(label) => label,
            None => "",
        };
        writeln!(
            f,
            "\\draw ({}) edge[{}] node {{{}}} ({});",
            self.from,
            self.modifiers.join(", "),
            label_text,
            self.to
        )?;

        Ok(())
    }
}

#[derive(Debug, Clone)]
pub(crate) struct DrawnGraph<Id: Clone + Debug + Display> {
    nodes: Vec<DrawNode<Id>>,
    edges: Vec<DrawEdge<Id>>,
}

impl<Id: Clone + Debug + Display> DrawnGraph<Id> {
    pub(crate) fn draw_node(&mut self, node: DrawNode<Id>) {
        self.nodes.push(node);
    }

    pub(crate) fn draw_edge(&mut self, edge: DrawEdge<Id>) {
        self.edges.push(edge);
    }
}

impl<Id: Clone + Debug + Display> Default for DrawnGraph<Id> {
    fn default() -> Self {
        DrawnGraph {
            nodes: Vec::new(),
            edges: Vec::new(),
        }
    }
}

impl<Id: Clone + Debug + Display> Display for DrawnGraph<Id> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        writeln!(f)?;
        for node in &self.nodes {
            Display::fmt(node, f)?;
        }
        for edge in &self.edges {
            Display::fmt(edge, f)?;
        }
        writeln!(f)?;

        Ok(())
    }
}

#[allow(dead_code, reason = "debug drawing utility")]
pub(crate) trait GraphDraw<Id: Clone + Debug + Display> {
    fn draw(&self) -> DrawnGraph<Id>;
}