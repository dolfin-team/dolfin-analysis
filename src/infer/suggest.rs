//! What to suggest next on a node: the properties its alternatives allow that
//! still have room for a value, ranked for completion.

use std::collections::HashMap;

use super::node::NodeTypeState;
use super::{ClassId, PropId, TypeIndex};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Suggestion {
    pub prop: PropId,
    /// Its minimum count is not reached yet.
    pub required: bool,
    /// The most general class that introduces the property (where it is
    /// declared, not where it is inherited).
    pub introduced_by: ClassId,
    /// Ancestor count of `introduced_by`: deeper = more specific.
    pub depth: usize,
    pub frequency: u32,
}

impl Suggestion {
    /// Smaller sorts first.
    fn rank(&self) -> (bool, std::cmp::Reverse<usize>, std::cmp::Reverse<u32>) {
        (!self.required, std::cmp::Reverse(self.depth), std::cmp::Reverse(self.frequency))
    }
}

/// Ranked suggestions for `node`: required first, then properties introduced
/// by more specific classes, then by `frequency(class, prop)` (how often the
/// property is used on that class elsewhere; pass `&|_, _| 0` when unknown),
/// then by name. A property is suggested while it is below its minimum count,
/// or unasserted with room left. An untyped node gets nothing: the caller
/// falls back to plain name completion.
pub fn suggest(idx: &TypeIndex, node: &NodeTypeState, frequency: &dyn Fn(ClassId, PropId) -> u32) -> Vec<Suggestion> {
    let count = |p: PropId| node.assertions.iter().filter(|a| a.props.contains(&p)).count();
    let mut best: HashMap<PropId, Suggestion> = HashMap::new();

    for &c in node.alternatives.iter().flatten() {
        for &p in idx.applicable_props(c) {
            let n = count(p);
            let (min, max) = idx.constraint(c, p).map_or((0, None), |k| (k.min, k.max));
            if max.is_some_and(|m| n >= m) || (n > 0 && n >= min) {
                continue;
            }
            let introduced_by = introducer(idx, c, p);
            let s = Suggestion {
                prop: p,
                required: n < min,
                introduced_by,
                depth: idx.superclasses(introduced_by).len(),
                frequency: frequency(c, p),
            };
            best.entry(p).and_modify(|b| if s.rank() < b.rank() { *b = s }).or_insert(s);
        }
    }

    let mut out: Vec<Suggestion> = best.into_values().collect();
    out.sort_by(|a, b| a.rank().cmp(&b.rank()).then_with(|| idx.prop_name(a.prop).cmp(idx.prop_name(b.prop))));
    out
}

/// Among `c` and its ancestors that have `p`, the one with the fewest ancestors.
fn introducer(idx: &TypeIndex, c: ClassId, p: PropId) -> ClassId {
    std::iter::once(c)
        .chain(idx.superclasses(c).iter().copied())
        .filter(|&d| idx.applicable_props(d).contains(&p))
        .min_by_key(|&d| (idx.superclasses(d).len(), d))
        .unwrap_or(c)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::infer::node::{AssertedValue, NodeId, TypeGraph};
    use rowl::{OntologyFile, PrimitiveKind, QualifiedName, parser::parse_ontology};

    const FIXTURE: &str = "\
concept Agent:
  has name: one string

concept Employee:
  sub Agent
  has employer: optional Agent
  has badge: string

concept Manager:
  sub Employee
  has reports: some Employee
  has deputies: 2 Employee

concept Director:
  sub Employee
  has budget: optional float
";

    fn index() -> TypeIndex {
        let file: OntologyFile = parse_ontology(FIXTURE).ontology.expect("parse failed");
        let ns = QualifiedName::new(Vec::new(), None);
        TypeIndex::build([(&ns, &file)])
    }

    fn names(idx: &TypeIndex, s: &[Suggestion]) -> Vec<String> {
        s.iter().map(|s| idx.prop_name(s.prop).to_owned()).collect()
    }

    fn typed(idx: &TypeIndex, g: &mut TypeGraph, classes: &[&str]) -> NodeId {
        let n = g.add_node();
        for c in classes {
            g.assert_type(idx, n, idx.classes_named(c));
        }
        n
    }

    #[test]
    fn required_then_specific_then_frequent() {
        let idx = index();
        let mut g = TypeGraph::default();
        let n = typed(&idx, &mut g, &["Manager"]);
        let badge = idx.prop_id("badge").unwrap();
        let freq = |_: ClassId, p: PropId| if p == badge { 5 } else { 0 };

        let s = suggest(&idx, g.node(n), &freq);
        // Required: deputies, reports (Manager, depth 2; by name), name (Agent, depth 0).
        // Optional, from Employee (depth 1): badge more frequent than employer.
        assert_eq!(names(&idx, &s), ["deputies", "reports", "name", "badge", "employer"]);
        assert!(s[..3].iter().all(|s| s.required));
        assert_eq!(s[2].introduced_by, idx.class_id("Agent").unwrap());
    }

    #[test]
    fn asserted_props_drop_out_once_satisfied() {
        let idx = index();
        let mut g = TypeGraph::default();
        let n = typed(&idx, &mut g, &["Manager"]);
        let (e1, e2) = (g.add_node(), g.add_node());
        let str_ = AssertedValue::Literal(Some(PrimitiveKind::String));

        g.assert_prop(&idx, n, idx.props_named("name"), str_);
        g.assert_prop(&idx, n, idx.props_named("reports"), AssertedValue::Node(e1));
        g.assert_prop(&idx, n, idx.props_named("deputies"), AssertedValue::Node(e2));

        let s = suggest(&idx, g.node(n), &|_, _| 0);
        // One deputy of two: still required. `reports` has one, its minimum.
        assert_eq!(names(&idx, &s), ["deputies", "badge", "employer"]);
        assert!(s[0].required);
    }

    #[test]
    fn ambiguous_node_gets_the_union() {
        let idx = index();
        let mut g = TypeGraph::default();
        let n = typed(&idx, &mut g, &["Employee"]);
        // Two alternatives by hand: the node is a Manager or a Director.
        let (m, d) = (idx.class_id("Manager").unwrap(), idx.class_id("Director").unwrap());
        let mut state = g.node(n).clone();
        state.alternatives = vec![vec![m], vec![d]];

        let s = suggest(&idx, &state, &|_, _| 0);
        assert_eq!(names(&idx, &s), ["deputies", "reports", "name", "budget", "badge", "employer"]);
    }

    #[test]
    fn untyped_node_gets_nothing() {
        let idx = index();
        let mut g = TypeGraph::default();
        let n = g.add_node();
        assert!(suggest(&idx, g.node(n), &|_, _| 0).is_empty());
    }
}
