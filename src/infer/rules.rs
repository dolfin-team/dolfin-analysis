//! Types the nodes of one rule or query (variables, constants, `[ … ]`
//! blocks, subject-less patterns) from its patterns, so a bare property name
//! there resolves the way it does in a fact (see [`super::node::pick_prop`]).

use std::collections::HashMap;

use rowl::{
    Constraint, ConstraintBlock, Expr, Object, OntologyFile, Pattern, PropertyPattern, QualifiedName, QueryClause,
    QueryDef, Subject, SubjectPattern, ThenItem,
};

use super::facts::{FactGraph, primitive};
use super::node::{AssertedValue, NodeId, TypeGraph};
use super::{Scope, TypeIndex};

#[derive(Debug, Default, Clone)]
pub struct RuleGraph {
    pub graph: TypeGraph,
    vars: HashMap<String, NodeId>,
    constants: HashMap<String, NodeId>,
    /// Start offset of an anonymous node's source (constraint block, query
    /// subject block or subject-less pattern) → node.
    blocks: HashMap<usize, NodeId>,
}

impl RuleGraph {
    /// One flattened rule (`match` patterns + `then` items) of the file `file`
    /// with namespace `ns`. A constant naming a fact starts with that fact's
    /// settled type from `facts`.
    pub fn build(
        idx: &TypeIndex,
        facts: &FactGraph,
        ns: &QualifiedName,
        file: &OntologyFile,
        patterns: &[Pattern],
        then: &[ThenItem],
    ) -> Self {
        let ns_full = ns.full();
        let mut b = Builder::new(idx, facts, ns, file, &ns_full);
        for p in patterns {
            b.pattern(p);
        }
        for t in then {
            match t {
                ThenItem::AssertionTriple { assertion: a, .. } => b.triple(&a.subject, &a.property, &a.object),
                ThenItem::AssertionTyping { subject, typing, .. } => {
                    let s = b.subject(subject);
                    let classes = b.scope.resolve(&idx.classes, typing);
                    b.rg.graph.assert_type(idx, s, &classes);
                }
                ThenItem::NestedRule { .. } => {}
            }
        }
        b.rg
    }

    /// A query's nodes, same inputs as [`Self::build`]. Composed queries are
    /// not followed.
    pub fn build_query(idx: &TypeIndex, facts: &FactGraph, ns: &QualifiedName, file: &OntologyFile, query: &QueryDef) -> Self {
        let ns_full = ns.full();
        let mut b = Builder::new(idx, facts, ns, file, &ns_full);
        let mut primary = None;
        b.clauses(&query.body.clauses, &mut primary);
        b.rg
    }

    /// The node of variable `name` (`?x`).
    pub fn var_node(&self, name: &str) -> Option<NodeId> {
        self.vars.get(name).copied()
    }

    /// The anonymous node whose source starts at `offset`.
    pub fn node_at(&self, offset: usize) -> Option<NodeId> {
        self.blocks.get(&offset).copied()
    }

    pub fn subject_node(&self, s: &Subject) -> Option<NodeId> {
        match s {
            Subject::Variable { name, .. } => self.vars.get(name).copied(),
            Subject::Constant { name, .. } => self.constants.get(&name.full()).copied(),
            Subject::Constraint { block, .. } => self.block_node(block),
        }
    }

    pub fn object_node(&self, o: &Object) -> Option<NodeId> {
        match o {
            Object::Variable { name, .. } => self.vars.get(name).copied(),
            Object::Constant { value, .. } => self.constants.get(&value.full()).copied(),
            Object::Constraint { block } => self.block_node(block),
            Object::Literal { .. } => None,
        }
    }

    pub fn block_node(&self, block: &ConstraintBlock) -> Option<NodeId> {
        self.blocks.get(&block.span.as_ref()?.start.offset).copied()
    }
}

struct Builder<'a> {
    idx: &'a TypeIndex,
    facts: &'a FactGraph,
    ns: &'a QualifiedName,
    file: &'a OntologyFile,
    scope: Scope<'a>,
    rg: RuleGraph,
}

impl<'a> Builder<'a> {
    fn new(idx: &'a TypeIndex, facts: &'a FactGraph, ns: &'a QualifiedName, file: &'a OntologyFile, ns_full: &'a str) -> Self {
        Builder { idx, facts, ns, file, scope: Scope::new(ns_full, file), rg: RuleGraph::default() }
    }

    /// `primary` = the first named subject, which a top-level `is p of ?o`
    /// is about (as in `dolfin_query`).
    fn clauses(&mut self, clauses: &[QueryClause], primary: &mut Option<NodeId>) {
        for c in clauses {
            match c {
                QueryClause::SubjectPattern(sp) => self.subject_pattern(sp, primary),
                QueryClause::InverseTriple(it) => {
                    if let (Some(s), AssertedValue::Node(o)) = (*primary, self.object(&it.object)) {
                        self.prop(o, &it.property, AssertedValue::Node(s));
                    }
                }
                QueryClause::ExistenceBlock(eb) => self.clauses(&eb.clauses, primary),
                QueryClause::AggregationQuery(aq) => self.clauses(&aq.sub_clauses, primary),
                QueryClause::Composition(_) | QueryClause::BooleanFilter(_) => {}
            }
        }
    }

    fn subject_pattern(&mut self, sp: &SubjectPattern, primary: &mut Option<NodeId>) {
        let n = match &sp.subject {
            Some(v) => {
                let n = self.var(v);
                if primary.is_none() && !v.starts_with("?_") {
                    *primary = Some(n);
                }
                n
            }
            None => self.anonymous(sp.span.as_ref().map(|s| s.start.offset)),
        };
        if let Some(t) = &sp.type_ref {
            let classes = self.scope.classes(&self.idx.classes, t);
            self.rg.graph.assert_type(self.idx, n, &classes);
        }
        self.property_patterns(n, &sp.properties);
    }

    fn property_patterns(&mut self, n: NodeId, patterns: &[PropertyPattern]) {
        for pp in patterns {
            match pp {
                PropertyPattern::Value { property, object, .. } | PropertyPattern::Optional { property, object, .. } => {
                    let v = self.object(object);
                    self.prop(n, property, v);
                }
                PropertyPattern::Constrained { property, block, .. } => {
                    let m = self.block(block);
                    self.prop(n, property, AssertedValue::Node(m));
                }
                PropertyPattern::Inverse { property, outer_var, .. } => {
                    let m = self.var(outer_var);
                    self.prop(m, property, AssertedValue::Node(n));
                }
                PropertyPattern::InverseNested { property, block, .. } => {
                    let m = self.block(block);
                    self.prop(m, property, AssertedValue::Node(n));
                }
                PropertyPattern::Nested { property, block, .. } => {
                    let m = self.anonymous(block.span.as_ref().map(|s| s.start.offset));
                    self.property_patterns(m, &block.properties);
                    self.prop(n, property, AssertedValue::Node(m));
                }
                // ponytail: a branch does not narrow the subject (it is one
                // of several); its block is still typed from its own content.
                PropertyPattern::Disjunction { either_branch, or_branches, .. } => {
                    for b in std::iter::once(either_branch).chain(or_branches) {
                        self.block(&b.block);
                    }
                }
            }
        }
    }

    fn anonymous(&mut self, offset: Option<usize>) -> NodeId {
        let n = self.rg.graph.add_node();
        if let Some(o) = offset {
            self.rg.blocks.insert(o, n);
        }
        n
    }

    fn pattern(&mut self, p: &Pattern) {
        match p {
            Pattern::Triple { subject, property, object, .. } => self.triple(subject, property, object),
            Pattern::Type { subject, type_ref, .. } => {
                let s = self.subject(subject);
                let classes = self.scope.classes(&self.idx.classes, type_ref);
                self.rg.graph.assert_type(self.idx, s, &classes);
            }
            // `s is p of o` = `o p s`.
            Pattern::Inverse { subject, property, object, .. } => {
                let s = self.subject(subject);
                if let AssertedValue::Node(o) = self.object(object) {
                    self.prop(o, property, AssertedValue::Node(s));
                }
            }
            // Not rendered in N3 either.
            Pattern::Quantified { .. } | Pattern::QueryCall { .. } => {}
        }
    }

    fn triple(&mut self, subject: &Subject, property: &QualifiedName, object: &Object) {
        let s = self.subject(subject);
        let o = self.object(object);
        self.prop(s, property, o);
    }

    fn prop(&mut self, n: NodeId, property: &QualifiedName, value: AssertedValue) {
        let props = self.scope.resolve(&self.idx.props, property);
        self.rg.graph.assert_prop(self.idx, n, &props, value);
    }

    fn subject(&mut self, s: &Subject) -> NodeId {
        match s {
            Subject::Variable { name, .. } => self.var(name),
            Subject::Constant { name, .. } => self.constant(name),
            Subject::Constraint { block, .. } => self.block(block),
        }
    }

    fn object(&mut self, o: &Object) -> AssertedValue {
        match o {
            Object::Variable { name, .. } => AssertedValue::Node(self.var(name)),
            Object::Constant { value, .. } => AssertedValue::Node(self.constant(value)),
            Object::Constraint { block } => AssertedValue::Node(self.block(block)),
            Object::Literal { value: Expr::Literal { value, .. }, .. } => AssertedValue::Literal(primitive(value)),
            Object::Literal { .. } => AssertedValue::Literal(None),
        }
    }

    fn var(&mut self, name: &str) -> NodeId {
        if let Some(&n) = self.rg.vars.get(name) {
            return n;
        }
        let n = self.rg.graph.add_node();
        self.rg.vars.insert(name.to_owned(), n);
        n
    }

    fn constant(&mut self, name: &QualifiedName) -> NodeId {
        if let Some(&n) = self.rg.constants.get(&name.full()) {
            return n;
        }
        let n = self.rg.graph.add_node();
        self.rg.constants.insert(name.full(), n);
        if let Some(f) = self.facts.fact_named(self.ns, self.file, name)
            && let [typing] = self.facts.graph.node(f).alternatives.as_slice() {
                for &c in typing {
                    self.rg.graph.assert_type(self.idx, n, &[c]);
                }
            }
        n
    }

    fn block(&mut self, block: &ConstraintBlock) -> NodeId {
        let n = self.anonymous(block.span.as_ref().map(|s| s.start.offset));
        for c in &block.constraints {
            match c {
                Constraint::TypeIs { type_ref, .. } => {
                    let classes = self.scope.classes(&self.idx.classes, type_ref);
                    self.rg.graph.assert_type(self.idx, n, &classes);
                }
                Constraint::Comparison { .. } => {}
                Constraint::PropertyValue { property, value, .. } => {
                    let v = self.object(value);
                    self.prop(n, property, v);
                }
                Constraint::PropertyConstraint { property, block, .. } => {
                    let m = self.block(block);
                    self.prop(n, property, AssertedValue::Node(m));
                }
                Constraint::Inverse { property, value, .. } => {
                    if let AssertedValue::Node(m) = self.object(value) {
                        self.prop(m, property, AssertedValue::Node(n));
                    }
                }
                Constraint::InverseNested { property, block, .. } => {
                    let m = self.block(block);
                    self.prop(m, property, AssertedValue::Node(n));
                }
            }
        }
        n
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::infer::node::pick_prop;
    use rowl::Declaration;
    use rowl::parser::parse_ontology;

    #[test]
    fn rule_nodes_pick_properties_by_type() {
        let files: Vec<(QualifiedName, OntologyFile)> = [
            ("person", "concept Person:\n  has name: string\n  has pet: Animal\n"),
            ("animal", "concept Animal:\n  has name: string\n"),
            (
                "ex",
                "rule r:\n  match:\n    ?x a person.Person\n    ?x name ?n\n    ?x pet [ name ?m ]\n  then:\n    ?x name ?m\n",
            ),
        ]
        .into_iter()
        .map(|(ns, src)| {
            let r = parse_ontology(src);
            (QualifiedName::from_single(ns.to_owned()), r.ontology.clone().unwrap_or_else(|| panic!("{:?}", r.errors())))
        })
        .collect();
        let idx = TypeIndex::build(files.iter().map(|(ns, f)| (ns, f)));
        let facts = FactGraph::build(&idx, files.iter().map(|(ns, f)| (ns, f)));
        let (ex, file) = (&files[2].0, &files[2].1);
        let Declaration::Rule(rule) = &file.declarations[0] else { unreachable!() };
        let rg = RuleGraph::build(&idx, &facts, ex, file, &rule.match_block.patterns, &rule.then_block.items);

        let name = idx.props_for(ex, file, &QualifiedName::from_single("name".to_owned()));
        let pick = |n: Option<NodeId>| pick_prop(&idx, n.map(|n| rg.graph.node(n)), &name).map(|p| idx.prop_name(p));
        let x = Subject::Variable { name: "?x".to_owned(), span: None };
        assert_eq!(pick(rg.subject_node(&x)), Some("person.name"));

        // `pet [ name ?m ]`: the block is typed Animal by `pet`'s range.
        let Pattern::Triple { object: Object::Constraint { block }, .. } = &rule.match_block.patterns[2] else {
            unreachable!()
        };
        assert_eq!(pick(rg.block_node(block)), Some("animal.name"));
    }

    #[test]
    fn query_nodes_pick_properties_by_type() {
        let files: Vec<(QualifiedName, OntologyFile)> = [
            ("person", "concept Person:\n  has name: string\n  has pet: Animal\n"),
            ("animal", "concept Animal:\n  has name: string\n"),
            ("ex", "query q:\n  ?x a person.Person\n    name ?n\n    pet [ name ?m ]\n"),
        ]
        .into_iter()
        .map(|(ns, src)| {
            let r = parse_ontology(src);
            (QualifiedName::from_single(ns.to_owned()), r.ontology.clone().unwrap_or_else(|| panic!("{:?}", r.errors())))
        })
        .collect();
        let idx = TypeIndex::build(files.iter().map(|(ns, f)| (ns, f)));
        let facts = FactGraph::build(&idx, files.iter().map(|(ns, f)| (ns, f)));
        let (ex, file) = (&files[2].0, &files[2].1);
        let query = file.queries().remove(0);
        let rg = RuleGraph::build_query(&idx, &facts, ex, file, &query);

        let name = idx.props_for(ex, file, &QualifiedName::from_single("name".to_owned()));
        let pick = |n: Option<NodeId>| pick_prop(&idx, n.map(|n| rg.graph.node(n)), &name).map(|p| idx.prop_name(p));
        assert_eq!(pick(rg.var_node("?x")), Some("person.name"));
        let QueryClause::SubjectPattern(sp) = &query.body.clauses[0] else { unreachable!() };
        let PropertyPattern::Constrained { block, .. } = &sp.properties[1] else { unreachable!() };
        assert_eq!(pick(rg.block_node(block)), Some("animal.name"));
    }
}
