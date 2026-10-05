//! Incremental typing of the nodes (facts) being authored.
//!
//! Each node carries a set of *alternatives*: what it could be, given what is
//! asserted so far. An alternative is a conjunction of classes (a *typing*),
//! usually a single class. Several alternatives = the assertions do not
//! decide yet; the editor shows them as a choice.
//!
//! Asserting a property narrows the subject to the property's domain and, for
//! a reference, the object to its range. When a class and the domain have no
//! common subclass the node simply gets both (`{Employee, Company}`): that is
//! a class the user has not written yet, not a conflict. Cardinality and
//! value-type constraints are evidence *against* an alternative; only when
//! they rule out every alternative is a conflict recorded, and the node keeps
//! its alternatives so drafting goes on.

use rowl::PrimitiveKind;

use super::{ClassId, PropId, TypeIndex, ValueType};

pub type NodeId = usize;

/// A conjunction of classes, sorted, with no class that is an ancestor of
/// another member. Empty = nothing known yet.
pub type Typing = Vec<ClassId>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssertedValue {
    /// A literal; `None` when its datatype is not known (e.g. an IRI).
    Literal(Option<PrimitiveKind>),
    /// A reference to another node of the same graph.
    Node(NodeId),
}

/// One `property value` line. `props` holds every property the written name
/// may denote (see [`TypeIndex::props_named`]); the typing picks among them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Assertion {
    pub props: Vec<PropId>,
    pub value: AssertedValue,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConflictReason {
    CardinalityExceeded { prop: PropId, max: usize },
    ValueTypeMismatch { prop: PropId },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TypeConflict {
    /// Index into [`NodeTypeState::assertions`].
    pub assertion: usize,
    pub reason: ConflictReason,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NodeTypeState {
    pub alternatives: Vec<Typing>,
    pub assertions: Vec<Assertion>,
    pub conflicts: Vec<TypeConflict>,
}

impl Default for NodeTypeState {
    fn default() -> Self {
        NodeTypeState { alternatives: vec![Vec::new()], assertions: Vec::new(), conflicts: Vec::new() }
    }
}

/// Which of `candidates` (see [`TypeIndex::props_for`]) a `prop value` line
/// on `subject` means: the only candidate, else the only one that applies to
/// every alternative typing of the subject. `None` = still ambiguous (or no
/// candidate).
pub fn pick_prop(idx: &TypeIndex, subject: Option<&NodeTypeState>, candidates: &[PropId]) -> Option<PropId> {
    if let [p] = candidates {
        return Some(*p);
    }
    let alts = &subject?.alternatives;
    let mut fit = candidates
        .iter()
        .filter(|&&p| alts.iter().all(|t| t.iter().any(|&c| idx.applicable_props(c).contains(&p))));
    match (fit.next(), fit.next()) {
        (Some(&p), None) => Some(p),
        _ => None,
    }
}

/// The nodes being edited. Nodes are shared because typing one can retype a
/// neighbour through a property's range.
#[derive(Debug, Default, Clone)]
pub struct TypeGraph {
    nodes: Vec<NodeTypeState>,
}

impl TypeGraph {
    pub fn add_node(&mut self) -> NodeId {
        self.nodes.push(NodeTypeState::default());
        self.nodes.len() - 1
    }

    pub fn node(&self, n: NodeId) -> &NodeTypeState {
        &self.nodes[n]
    }

    pub fn nodes(&self) -> &[NodeTypeState] {
        &self.nodes
    }

    /// `a Foo` on a node. `classes` holds every class the written name may
    /// denote (see [`TypeIndex::classes_named`]).
    pub fn assert_type(&mut self, idx: &TypeIndex, n: NodeId, classes: &[ClassId]) {
        self.narrow(idx, n, classes);
    }

    /// `prop value` on a node.
    pub fn assert_prop(&mut self, idx: &TypeIndex, n: NodeId, props: &[PropId], value: AssertedValue) {
        self.nodes[n].assertions.push(Assertion { props: props.to_vec(), value });
        let domain: Vec<ClassId> = props.iter().flat_map(|&p| idx.domain(p).iter().copied()).collect();
        self.narrow(idx, n, &domain);
        if let AssertedValue::Node(m) = value {
            // ponytail: the union of every candidate property's declared
            // range, not the subclass-refined one of the chosen typing.
            let range: Vec<ClassId> = props
                .iter()
                .flat_map(|&p| idx.range(p))
                .filter_map(|v| match v {
                    ValueType::Class(c) => Some(*c),
                    ValueType::Primitive(_) | ValueType::Quantity => None,
                })
                .collect();
            self.narrow(idx, m, &range);
        }
    }

    /// Make every alternative of `n` fit at least one of `classes`, then
    /// re-check the node's own constraints. Only the least inventive outcome
    /// survives: alternatives that already fit, else ones narrowed to a
    /// common subclass, else (option B) ones that take `classes` on as an
    /// extra class of their conjunction.
    fn narrow(&mut self, idx: &TypeIndex, n: NodeId, classes: &[ClassId]) {
        if !classes.is_empty() {
            let mut best = Joined::Added;
            let mut out: Vec<Typing> = Vec::new();
            for t in std::mem::take(&mut self.nodes[n].alternatives) {
                let branches = if fits(idx, &t, classes) {
                    vec![(Joined::Fits, t)]
                } else {
                    classes.iter().flat_map(|&d| conj(idx, &t, d)).collect()
                };
                for (how, b) in branches {
                    if how < best {
                        best = how;
                        out.clear();
                    }
                    if how == best && !out.contains(&b) {
                        out.push(b);
                    }
                }
            }
            self.nodes[n].alternatives = out;
        }
        self.filter(idx, n);
    }

    /// Drop the alternatives the assertions rule out, one assertion at a
    /// time; an assertion that would rule out all of them is a conflict.
    fn filter(&mut self, idx: &TypeIndex, n: NodeId) {
        let node = &mut self.nodes[n];
        node.conflicts.clear();
        for (i, a) in node.assertions.iter().enumerate() {
            let mut reason = None;
            let keep: Vec<Typing> = node
                .alternatives
                .iter()
                .filter(|t| match allows(idx, t, a, &node.assertions) {
                    Ok(()) => true,
                    Err(r) => {
                        reason.get_or_insert(r);
                        false
                    }
                })
                .cloned()
                .collect();
            match (keep.is_empty(), reason) {
                (true, Some(reason)) => node.conflicts.push(TypeConflict { assertion: i, reason }),
                _ => node.alternatives = keep,
            }
        }
    }
}

/// Some member of `t` is (a subclass of) one of `classes`.
fn fits(idx: &TypeIndex, t: &Typing, classes: &[ClassId]) -> bool {
    t.iter().any(|&c| classes.iter().any(|&d| is_a(idx, c, d)))
}

fn is_a(idx: &TypeIndex, c: ClassId, d: ClassId) -> bool {
    c == d || idx.superclasses(c).contains(&d)
}

/// How a typing was made to fit, from least to most inventive.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Joined {
    Fits,
    Met,
    Added,
}

/// `t ∧ d`, as alternatives: the first member with a common subclass with `d`
/// is replaced by each class of their meet; with none, `d` joins the
/// conjunction.
fn conj(idx: &TypeIndex, t: &Typing, d: ClassId) -> Vec<(Joined, Typing)> {
    // ponytail: meets only the first compatible member; a typing of several
    // classes that each meet `d` differently narrows less than it could.
    for (i, &c) in t.iter().enumerate() {
        let meet = idx.meet(c, d);
        if !meet.is_empty() {
            return meet
                .into_iter()
                .map(|m| {
                    let mut u = t.clone();
                    u[i] = m;
                    (Joined::Met, normalize(idx, u))
                })
                .collect();
        }
    }
    let mut u = t.clone();
    u.push(d);
    // An untyped node taking its first class is not an invention.
    let how = if t.is_empty() { Joined::Met } else { Joined::Added };
    vec![(how, normalize(idx, u))]
}

fn normalize(idx: &TypeIndex, mut t: Typing) -> Typing {
    t.sort_unstable();
    t.dedup();
    let redundant = |c: ClassId| t.iter().any(|&e| e != c && idx.superclasses(e).contains(&c));
    t.iter().copied().filter(|&c| !redundant(c)).collect()
}

/// Whether typing `t` allows assertion `a`: some candidate property that
/// applies to `t` has room for one more value of the right type.
fn allows(idx: &TypeIndex, t: &Typing, a: &Assertion, all: &[Assertion]) -> Result<(), ConflictReason> {
    let mut reason = None;
    for &p in &a.props {
        if !t.iter().any(|&c| idx.applicable_props(c).contains(&p)) {
            continue;
        }
        match check(idx, t, p, a.value, all) {
            Ok(()) => return Ok(()),
            Err(r) => reason = Some(r),
        }
    }
    reason.map_or(Ok(()), Err)
}

fn check(idx: &TypeIndex, t: &Typing, p: PropId, value: AssertedValue, all: &[Assertion]) -> Result<(), ConflictReason> {
    let count = all.iter().filter(|a| a.props.contains(&p)).count();
    for &c in t {
        let Some(k) = idx.constraint(c, p) else { continue };
        if let Some(max) = k.max
            && count > max
        {
            return Err(ConflictReason::CardinalityExceeded { prop: p, max });
        }
        if !k.ranges.iter().all(|r| value_fits(value, r)) {
            return Err(ConflictReason::ValueTypeMismatch { prop: p });
        }
    }
    Ok(())
}

fn value_fits(value: AssertedValue, range: &[ValueType]) -> bool {
    // ponytail: a quantity range accepts anything, as it did while unresolved;
    // check literal kinds against it once facts carry a quantity kind.
    if range.contains(&ValueType::Quantity) {
        return true;
    }
    match value {
        AssertedValue::Literal(None) => true,
        AssertedValue::Literal(Some(k)) => {
            range.contains(&ValueType::Primitive(k))
                || (k == PrimitiveKind::Int && range.contains(&ValueType::Primitive(PrimitiveKind::Float)))
        }
        AssertedValue::Node(_) => range.iter().any(|v| matches!(v, ValueType::Class(_))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rowl::{OntologyFile, QualifiedName, parser::parse_ontology};

    const FIXTURE: &str = "\
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
  has team: 1..3 Employee

concept Director:
  sub Employee, Leader
  has budget: optional float
";

    fn index(files: &[(&str, &str)]) -> TypeIndex {
        let parsed: Vec<(QualifiedName, OntologyFile)> = files
            .iter()
            .map(|(ns, src)| {
                let parts = ns.split('.').filter(|s| !s.is_empty()).map(str::to_owned).collect();
                (QualifiedName::new(parts, None), parse_ontology(src).ontology.expect("parse failed"))
            })
            .collect();
        TypeIndex::build(parsed.iter().map(|(ns, f)| (ns, f)))
    }

    /// Alternatives as sorted lists of class names, for readable asserts.
    fn alts(idx: &TypeIndex, g: &TypeGraph, n: NodeId) -> Vec<Vec<String>> {
        let mut out: Vec<Vec<String>> = g
            .node(n)
            .alternatives
            .iter()
            .map(|t| {
                let mut names: Vec<String> = t.iter().map(|&c| idx.class_name(c).to_owned()).collect();
                names.sort();
                names
            })
            .collect();
        out.sort();
        out
    }

    fn one(names: &[&str]) -> Vec<Vec<String>> {
        let mut out: Vec<Vec<String>> = names.iter().map(|n| vec![n.to_string()]).collect();
        out.sort();
        out
    }

    const STR: AssertedValue = AssertedValue::Literal(Some(PrimitiveKind::String));

    #[test]
    fn domain_and_range_type_both_ends() {
        let idx = index(&[("", FIXTURE)]);
        let mut g = TypeGraph::default();
        let (n, m) = (g.add_node(), g.add_node());

        g.assert_prop(&idx, n, idx.props_named("employer"), AssertedValue::Node(m));
        assert_eq!(alts(&idx, &g, n), one(&["Employee"]));
        assert_eq!(alts(&idx, &g, m), one(&["Company"]));
    }

    #[test]
    fn meet_with_several_answers_stays_ambiguous_until_disambiguated() {
        let idx = index(&[("", FIXTURE)]);
        let mut g = TypeGraph::default();
        let (n, m) = (g.add_node(), g.add_node());

        g.assert_prop(&idx, n, idx.props_named("employer"), AssertedValue::Node(m));
        g.assert_prop(&idx, n, idx.props_named("team"), AssertedValue::Node(m));
        assert_eq!(alts(&idx, &g, n), one(&["Manager", "Director"]));

        g.assert_prop(&idx, n, idx.props_named("budget"), AssertedValue::Literal(Some(PrimitiveKind::Int)));
        assert_eq!(alts(&idx, &g, n), one(&["Director"]));
        assert!(g.node(n).conflicts.is_empty());
    }

    #[test]
    fn unrelated_domain_joins_the_typing_without_conflict() {
        let idx = index(&[("", FIXTURE)]);
        let mut g = TypeGraph::default();
        let n = g.add_node();

        g.assert_type(&idx, n, idx.classes_named("Employee"));
        g.assert_prop(&idx, n, idx.props_named("vat"), STR);
        assert_eq!(alts(&idx, &g, n), vec![vec!["Company".to_string(), "Employee".to_string()]]);
        assert!(g.node(n).conflicts.is_empty());
    }

    #[test]
    fn cardinality_is_evidence_against_an_alternative() {
        let idx = index(&[("", FIXTURE)]);
        let mut g = TypeGraph::default();
        let n = g.add_node();
        let team: Vec<NodeId> = (0..4).map(|_| g.add_node()).collect();

        g.assert_type(&idx, n, idx.classes_named("Employee"));
        for &m in &team {
            g.assert_prop(&idx, n, idx.props_named("team"), AssertedValue::Node(m));
        }
        // Manager allows at most 3 team members.
        assert_eq!(alts(&idx, &g, n), one(&["Director"]));
        assert!(g.node(n).conflicts.is_empty());
    }

    #[test]
    fn exhausting_every_alternative_records_a_conflict_and_keeps_going() {
        let idx = index(&[("", FIXTURE)]);
        let mut g = TypeGraph::default();
        let n = g.add_node();
        let name = idx.prop_id("name").unwrap();

        g.assert_prop(&idx, n, &[name], STR);
        g.assert_prop(&idx, n, &[name], STR);
        g.assert_prop(&idx, n, &[name], AssertedValue::Literal(Some(PrimitiveKind::Int)));
        assert_eq!(alts(&idx, &g, n), one(&["Agent"]));
        assert_eq!(
            g.node(n).conflicts,
            vec![
                TypeConflict { assertion: 0, reason: ConflictReason::CardinalityExceeded { prop: name, max: 1 } },
                TypeConflict { assertion: 1, reason: ConflictReason::CardinalityExceeded { prop: name, max: 1 } },
                TypeConflict { assertion: 2, reason: ConflictReason::CardinalityExceeded { prop: name, max: 1 } },
            ]
        );
    }

    #[test]
    fn literal_of_the_wrong_type_is_a_conflict() {
        let idx = index(&[("", FIXTURE)]);
        let mut g = TypeGraph::default();
        let n = g.add_node();
        let vat = idx.prop_id("vat").unwrap();

        g.assert_prop(&idx, n, &[vat], AssertedValue::Literal(Some(PrimitiveKind::Boolean)));
        assert_eq!(
            g.node(n).conflicts,
            vec![TypeConflict { assertion: 0, reason: ConflictReason::ValueTypeMismatch { prop: vat } }]
        );
    }

    #[test]
    fn bare_property_name_picks_its_namespace_from_context() {
        let idx = index(&[
            ("hr", "concept Person:\n  has name: string\n  has age: int\n"),
            ("crm", "concept Customer:\n  has name: string\n"),
        ]);
        let mut g = TypeGraph::default();
        let n = g.add_node();

        g.assert_prop(&idx, n, idx.props_named("name"), STR);
        assert_eq!(alts(&idx, &g, n), one(&["crm.Customer", "hr.Person"]));

        g.assert_prop(&idx, n, idx.props_named("age"), AssertedValue::Literal(Some(PrimitiveKind::Int)));
        assert_eq!(alts(&idx, &g, n), one(&["hr.Person"]));
    }

    #[test]
    fn range_narrows_an_already_typed_neighbour() {
        let idx = index(&[("", FIXTURE)]);
        let mut g = TypeGraph::default();
        let (boss, m) = (g.add_node(), g.add_node());

        g.assert_type(&idx, m, idx.classes_named("Agent"));
        g.assert_prop(&idx, boss, idx.props_named("team"), AssertedValue::Node(m));
        assert_eq!(alts(&idx, &g, m), one(&["Employee"]));
    }
}
