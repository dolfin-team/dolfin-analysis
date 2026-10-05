//! Replays the workspace's `fact` blocks into a [`TypeGraph`]: one node per
//! fact, one per inline `[ … ]` block, references between facts as edges.

use std::collections::HashMap;

use rowl::error::Span;
use rowl::{Declaration, FactAssertion, FactValue, Literal, OntologyFile, PrimitiveKind, QualifiedName, TemporalKind};

use super::node::{AssertedValue, NodeId, TypeGraph};
use super::{ClassId, PropId, Scope, TypeIndex};

#[derive(Debug, Default, Clone)]
pub struct FactGraph {
    pub graph: TypeGraph,
    /// `(file namespace, fact id)` → node.
    nodes: HashMap<(String, String), NodeId>,
    /// Fact id → nodes, across namespaces (for references without a namespace).
    by_id: HashMap<String, Vec<NodeId>>,
    /// `(file namespace, start offset)` of an inline `[ … ]` block → node.
    blocks: HashMap<(String, usize), NodeId>,
}

impl FactGraph {
    /// Every fact in `files`, typed against `idx`. `files` are the same
    /// `(namespace, file)` pairs as [`TypeIndex::build`].
    pub fn build<'a>(idx: &TypeIndex, files: impl IntoIterator<Item = (&'a QualifiedName, &'a OntologyFile)>) -> Self {
        let files: Vec<(String, &OntologyFile)> = files.into_iter().map(|(ns, f)| (ns.full(), f)).collect();
        let mut fg = FactGraph::default();

        // Nodes first, so a fact can reference one declared after it.
        for (ns, file) in &files {
            for decl in &file.declarations {
                if let Declaration::Fact(f) = decl {
                    let n = fg.graph.add_node();
                    fg.nodes.insert((ns.clone(), f.id.clone()), n);
                    fg.by_id.entry(f.id.clone()).or_default().push(n);
                }
            }
        }

        for (ns, file) in &files {
            let scope = Scope::new(ns, file);
            for decl in &file.declarations {
                if let Declaration::Fact(f) = decl {
                    let n = fg.nodes[&(ns.clone(), f.id.clone())];
                    for t in &f.types {
                        fg.graph.assert_type(idx, n, &scope.resolve(&idx.classes, t));
                    }
                    fg.replay(idx, &scope, n, &f.assertions);
                }
            }
        }
        fg
    }

    /// The node of fact `id` declared in the file with namespace `ns`.
    pub fn node_of(&self, ns: &QualifiedName, id: &str) -> Option<NodeId> {
        self.nodes.get(&(ns.full(), id.to_owned())).copied()
    }

    /// The node of the inline `[ … ]` block at `span` in the file with
    /// namespace `ns`.
    pub fn block_node(&self, ns: &QualifiedName, span: Option<&Span>) -> Option<NodeId> {
        self.blocks.get(&(ns.full(), span?.start.offset)).copied()
    }

    /// The node of the fact a rule constant (`jack`, `alias.jack`) written in
    /// the file with namespace `ns` refers to.
    pub fn fact_named(&self, ns: &QualifiedName, file: &OntologyFile, name: &QualifiedName) -> Option<NodeId> {
        let ns = ns.full();
        let scope = Scope::new(&ns, file);
        let qualifier = match &name.parts[..] {
            [_] => None,
            [q, _] => Some(q.as_str()),
            _ => return None,
        };
        match self.fact(&scope, qualifier, &name.last()) {
            AssertedValue::Node(n) => Some(n),
            AssertedValue::Literal(_) => None,
        }
    }

    /// How many facts use each property, per class, counting only facts
    /// whose typing is settled: the frequency input of [`super::suggest::suggest`].
    pub fn usage(&self) -> HashMap<(ClassId, PropId), u32> {
        let mut out = HashMap::new();
        for node in self.graph.nodes() {
            let [typing] = node.alternatives.as_slice() else { continue };
            for &c in typing {
                for p in node.assertions.iter().flat_map(|a| &a.props) {
                    *out.entry((c, *p)).or_default() += 1;
                }
            }
        }
        out
    }

    fn replay(&mut self, idx: &TypeIndex, scope: &Scope, n: NodeId, assertions: &[FactAssertion]) {
        for a in assertions {
            match a {
                FactAssertion::TypeHint { type_ref, .. } => {
                    self.graph.assert_type(idx, n, &scope.resolve(&idx.classes, type_ref));
                }
                FactAssertion::Property { property, values, .. } => {
                    let props = scope.resolve(&idx.props, property);
                    for v in values {
                        let v = self.value(idx, scope, v);
                        self.graph.assert_prop(idx, n, &props, v);
                    }
                }
                // `is employer of acme` = `acme employer <this>`.
                FactAssertion::Inverse { property, value, .. } => {
                    if let AssertedValue::Node(m) = self.value(idx, scope, value) {
                        let props = scope.resolve(&idx.props, property);
                        self.graph.assert_prop(idx, m, &props, AssertedValue::Node(n));
                    }
                }
            }
        }
    }

    fn value(&mut self, idx: &TypeIndex, scope: &Scope, v: &FactValue) -> AssertedValue {
        match v {
            FactValue::Literal { value, .. } => AssertedValue::Literal(primitive(value)),
            // `:Name` is the package namespace, which declares no facts.
            FactValue::Reference { qualifier: None, .. } => AssertedValue::Literal(None),
            FactValue::Reference { qualifier, name, .. } => self.fact(scope, qualifier.as_deref(), name),
            // A bare name is a fact id or an enum member; ponytail: enum
            // members are not typed yet, so they check as an unknown literal.
            FactValue::Named { name, .. } => self.fact(scope, None, &name.last()),
            FactValue::Block { type_hint, assertions, span } => {
                let m = self.graph.add_node();
                if let Some(s) = span {
                    self.blocks.insert((scope.ns.to_owned(), s.start.offset), m);
                }
                if let Some(t) = type_hint {
                    self.graph.assert_type(idx, m, &scope.resolve(&idx.classes, t));
                }
                self.replay(idx, scope, m, assertions);
                AssertedValue::Node(m)
            }
        }
    }

    /// A fact reference: in the aliased namespace, else this file's, else the
    /// only fact with that id anywhere.
    fn fact(&self, scope: &Scope, qualifier: Option<&str>, id: &str) -> AssertedValue {
        let ns = match qualifier {
            Some(alias) => scope.prefixes.get(alias).map(|p| p.full()),
            None => Some(scope.ns.to_owned()),
        };
        ns.and_then(|ns| self.nodes.get(&(ns, id.to_owned())).copied())
            .or_else(|| match self.by_id.get(id).map(Vec::as_slice) {
                Some(&[n]) => Some(n),
                _ => None,
            })
            .map_or(AssertedValue::Literal(None), AssertedValue::Node)
    }
}

pub(super) fn primitive(l: &Literal) -> Option<PrimitiveKind> {
    match l {
        Literal::Int { .. } => Some(PrimitiveKind::Int),
        Literal::Float { .. } => Some(PrimitiveKind::Float),
        Literal::String { .. } => Some(PrimitiveKind::String),
        Literal::Boolean { .. } => Some(PrimitiveKind::Boolean),
        Literal::Temporal { kind, .. } => Some(match kind {
            TemporalKind::Date => PrimitiveKind::Date,
            TemporalKind::DateTime => PrimitiveKind::DateTime,
            TemporalKind::Time => PrimitiveKind::Time,
            TemporalKind::Duration => PrimitiveKind::Duration,
        }),
        Literal::Iri { .. } | Literal::Quantity { .. } => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::infer::node::pick_prop;
    use rowl::parser::parse_ontology;

    const SCHEMA: &str = "\
concept Agent:
  has name: one string

concept Company:
  has vat: optional string

concept Employee:
  sub Agent
  has employer: optional Company

concept Leader:
  sub Agent
  has team: some Employee

concept Manager:
  sub Employee, Leader

concept Director:
  sub Employee, Leader
  has budget: optional float
";

    const DATA: &str = "\
fact alice a Agent
  name \"Alice\"
  employer acme
  team bob
  budget 12000

fact acme a Company
  vat \"FR123\"

fact bob a Agent
  name \"Bob\"

fact carol a Agent
  employer [
    vat \"X\"
  ]

fact dave a Agent
  is team of carol
";

    fn build() -> (TypeIndex, FactGraph, QualifiedName) {
        let files: Vec<(QualifiedName, OntologyFile)> = [("hr", SCHEMA), ("data", DATA)]
            .into_iter()
            .map(|(ns, src)| {
                let r = parse_ontology(src);
                let file = r.ontology.clone().unwrap_or_else(|| panic!("{:?}", r.errors()));
                (QualifiedName::from_single(ns.to_owned()), file)
            })
            .collect();
        let idx = TypeIndex::build(files.iter().map(|(ns, f)| (ns, f)));
        let fg = FactGraph::build(&idx, files.iter().map(|(ns, f)| (ns, f)));
        (idx, fg, QualifiedName::from_single("data".to_owned()))
    }

    fn types<'a>(idx: &'a TypeIndex, fg: &FactGraph, n: NodeId) -> Vec<Vec<&'a str>> {
        fg.graph
            .node(n)
            .alternatives
            .iter()
            .map(|t| t.iter().map(|&c| idx.class_name(c)).collect())
            .collect()
    }

    #[test]
    fn facts_narrow_from_their_properties_and_neighbours() {
        let (idx, fg, data) = build();
        let node = |id| fg.node_of(&data, id).unwrap();

        assert_eq!(types(&idx, &fg, node("alice")), [["hr.Director"]]);
        assert_eq!(types(&idx, &fg, node("acme")), [["hr.Company"]]);
        // `bob` is typed by `alice`'s `team` although declared after it.
        assert_eq!(types(&idx, &fg, node("bob")), [["hr.Employee"]]);
        assert!(fg.graph.node(node("alice")).conflicts.is_empty());
    }

    #[test]
    fn inline_blocks_and_inverse_assertions() {
        let (idx, fg, data) = build();
        let node = |id| fg.node_of(&data, id).unwrap();

        // `carol` gets `employer` (Employee) and, through `dave`, `team` (Leader).
        assert_eq!(types(&idx, &fg, node("carol")), [["hr.Manager"], ["hr.Director"]]);
        assert_eq!(types(&idx, &fg, node("dave")), [["hr.Employee"]]);
        // The `[ vat "X" ]` block is its own node, typed Company.
        let AssertedValue::Node(block) = fg.graph.node(node("carol")).assertions[0].value else {
            panic!("`employer [ … ]` should reference the block's node");
        };
        assert_eq!(types(&idx, &fg, block), [["hr.Company"]]);
    }

    #[test]
    fn pick_prop_uses_the_subject_typing() {
        let files: Vec<(QualifiedName, OntologyFile)> = [
            ("person", "concept Person:\n  has name: string\n"),
            ("animal", "concept Animal:\n  has name: string\n"),
            ("ex", "fact jack a person.Person\n  name \"Jack\"\n  pet [\n    a animal.Animal\n    name \"Rex\"\n  ]\n\nfact x a Unknown\n  name \"?\"\n"),
        ]
        .into_iter()
        .map(|(ns, src)| {
            let r = parse_ontology(src);
            (QualifiedName::from_single(ns.to_owned()), r.ontology.clone().unwrap_or_else(|| panic!("{:?}", r.errors())))
        })
        .collect();
        let idx = TypeIndex::build(files.iter().map(|(ns, f)| (ns, f)));
        let fg = FactGraph::build(&idx, files.iter().map(|(ns, f)| (ns, f)));
        let (ex, file) = (&files[2].0, &files[2].1);
        let name = QualifiedName::from_single("name".to_owned());
        let candidates = idx.props_for(ex, file, &name);
        let pick = |n: Option<NodeId>| pick_prop(&idx, n.map(|n| fg.graph.node(n)), &candidates).map(|p| idx.prop_name(p));

        assert_eq!(candidates.len(), 2);
        assert_eq!(pick(fg.node_of(ex, "jack")), Some("person.name"));
        let FactValue::Block { span, .. } = pet_value(file) else { unreachable!() };
        let rex = fg.block_node(ex, span.as_ref());
        assert_eq!(pick(rex), Some("animal.name"));
        // Undeclared type: `name` fits both Person and Animal.
        assert_eq!(pick(fg.node_of(ex, "x")), None);
    }

    fn pet_value(file: &OntologyFile) -> &FactValue {
        let Declaration::Fact(f) = &file.declarations[0] else { unreachable!() };
        let FactAssertion::Property { values, .. } = &f.assertions[1] else { unreachable!() };
        &values[0]
    }

    #[test]
    fn usage_counts_settled_facts_only() {
        let (idx, fg, _) = build();
        let usage = fg.usage();
        let (c, p) = (|n| idx.class_id(n).unwrap(), |n| idx.prop_id(n).unwrap());

        assert_eq!(usage.get(&(c("hr.Director"), p("hr.budget"))), Some(&1));
        assert_eq!(usage.get(&(c("hr.Company"), p("hr.vat"))), Some(&2));
        // `carol` is Manager or Director: not counted.
        assert_eq!(usage.get(&(c("hr.Manager"), p("hr.employer"))), None);
    }
}
