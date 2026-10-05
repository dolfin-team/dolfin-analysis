//! Type-inference index for editor-time completion.
//!
//! A closed-world, advisory view of the ontology: the transitive `sub`
//! hierarchy, which properties apply to each concept (own + inherited), and
//! the cardinality / value-type constraints on each (concept, property) pair.
//! It is derived from the same declarations the Turtle compiler reads and
//! never feeds back into validation.
//!
//! Sources, in priority order:
//! 1. `has` declarations inside a concept (the closed-world shape),
//! 2. top-level `property p: Domain -> Range` declarations (RDFS-like fallback).
//!
//! Concepts and properties are identified by their fully qualified name
//! (`<file namespace>.<Name>`, the same identity the Turtle output gives them)
//! and interned to `u32` ids, so the per-keystroke queries built on top of
//! this never compare strings. `a.Foo` and `b.Foo` are distinct classes;
//! [`TypeIndex::classes_named`] lists every candidate for a bare `Foo`, which
//! is what inference later chooses between.

use std::collections::{HashMap, HashSet};

pub mod node;
pub mod facts;
pub mod suggest;
pub mod rules;

use rowl::{Cardinality, Declaration, OntologyFile, PrimitiveKind, QualifiedName, TypeRef};

pub type ClassId = u32;
pub type PropId = u32;

/// What a property value may be.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ValueType {
    Class(ClassId),
    Primitive(PrimitiveKind),
    /// A `quantity(...)` literal: a range naming a well-known dimension
    /// (`unit.Length`, `Mass`, …) that no concept in the package declares.
    Quantity,
}

/// Constraint on how a concept's instances use one property, merged over the
/// concept and all its ancestors (a subclass can only narrow).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PropConstraint {
    /// Bounds on the number of values per subject.
    pub min: usize,
    pub max: Option<usize>,
    /// Conjunction of unions: a value must match at least one member of
    /// *every* entry (`has pet: Animal` on a parent + `has pet: Dog` on the
    /// child gives `[[Animal], [Dog]]`).
    pub ranges: Vec<Vec<ValueType>>,
}

/// Qualified-name interner with a reverse index on the last segment.
#[derive(Debug, Default, Clone)]
struct Names {
    full: Vec<String>,
    ids: HashMap<String, u32>,
    by_last: HashMap<String, Vec<u32>>,
}

impl Names {
    fn intern(&mut self, ns: &str, name: &str) -> u32 {
        let full = if ns.is_empty() { name.to_owned() } else { format!("{ns}.{name}") };
        if let Some(&id) = self.ids.get(&full) {
            return id;
        }
        let id = self.full.len() as u32;
        self.full.push(full.clone());
        self.ids.insert(full, id);
        self.by_last.entry(name.to_owned()).or_default().push(id);
        id
    }

    fn named(&self, last: &str) -> &[u32] {
        self.by_last.get(last).map_or(&[], Vec::as_slice)
    }
}

#[derive(Debug, Default, Clone)]
pub struct TypeIndex {
    classes: Names,
    props: Names,
    /// Strict ancestors / descendants, transitive. Indexed by `ClassId`.
    superclasses: Vec<HashSet<ClassId>>,
    subclasses: Vec<HashSet<ClassId>>,
    /// Own + inherited properties. Indexed by `ClassId`.
    applicable: Vec<HashSet<PropId>>,
    /// For every `(c, p)` with `p ∈ applicable[c]`.
    constraints: HashMap<(ClassId, PropId), PropConstraint>,
    /// Union of the classes that declare the property. Indexed by `PropId`.
    domain: Vec<Vec<ClassId>>,
    /// Union of every declared range. Indexed by `PropId`.
    range: Vec<Vec<ValueType>>,
}

impl TypeIndex {
    /// Build the index from every `(namespace, file)` of the workspace. The
    /// namespace is the file's package namespace (`Package::iter_ontologies`,
    /// or the LSP document's derived namespace); an empty one is allowed.
    pub fn build<'a>(files: impl IntoIterator<Item = (&'a QualifiedName, &'a OntologyFile)>) -> Self {
        let files: Vec<(String, &OntologyFile)> = files.into_iter().map(|(ns, f)| (ns.full(), f)).collect();
        let mut idx = TypeIndex::default();

        // Pass 1: every declared concept, so references can resolve across files.
        for (ns, file) in &files {
            for decl in &file.declarations {
                if let Declaration::Concept(c) = decl {
                    idx.classes.intern(ns, c.name.get());
                }
            }
        }

        let n = idx.classes.full.len();
        let mut parents: Vec<Vec<ClassId>> = vec![Vec::new(); n];
        // Constraints as declared on each class, before inheritance.
        let mut own: HashMap<(ClassId, PropId), PropConstraint> = HashMap::new();

        // Pass 2: hierarchy and properties.
        for (ns, file) in &files {
            let scope = Scope::new(ns, file);
            for decl in &file.declarations {
                match decl {
                    Declaration::Concept(c) => {
                        let id = idx.classes.intern(ns, c.name.get());
                        for p in &c.parents {
                            // ponytail: an ambiguous `sub Foo` is dropped, not
                            // guessed; surface it once disambiguation UX exists.
                            if let [parent] = scope.classes(&idx.classes, p)[..] {
                                parents[id as usize].push(parent);
                            }
                        }
                        for has in &c.has_declarations {
                            let pid = idx.intern_prop(ns, &has.name);
                            let (min, max) = bounds(has.cardinality.as_ref());
                            let values = scope.values(&idx.classes, &has.type_ref);
                            idx.add_domain_range(pid, &[id], &values);
                            merge(&mut own, (id, pid), min, max, values);
                        }
                    }
                    Declaration::Property(p) => {
                        let pid = idx.intern_prop(ns, p.name.get());
                        let domain = scope.classes(&idx.classes, &p.domain);
                        let values = scope.values(&idx.classes, &p.range);
                        // The range cardinality bounds values per subject
                        // (`mother: Human -> one Human`: one mother each). The
                        // domain cardinality bounds the inverse direction.
                        let (min, max) = bounds(p.range_cardinality.as_ref());
                        idx.add_domain_range(pid, &domain, &values);
                        for c in domain {
                            merge(&mut own, (c, pid), min, max, values.clone());
                        }
                    }
                    _ => {}
                }
            }
        }

        idx.superclasses = (0..n).map(|c| ancestors(c as ClassId, &parents)).collect();
        idx.subclasses = vec![HashSet::new(); n];
        for (c, sups) in idx.superclasses.iter().enumerate() {
            for &s in sups {
                idx.subclasses[s as usize].insert(c as ClassId);
            }
        }

        idx.applicable = vec![HashSet::new(); n];
        for (&(declaring, pid), decl) in &own {
            let heirs = idx.subclasses[declaring as usize].iter().copied();
            for c in std::iter::once(declaring).chain(heirs) {
                idx.applicable[c as usize].insert(pid);
                merge(&mut idx.constraints, (c, pid), decl.min, decl.max, Vec::new());
                let merged = idx.constraints.get_mut(&(c, pid)).unwrap();
                for r in &decl.ranges {
                    if !merged.ranges.contains(r) {
                        merged.ranges.push(r.clone());
                    }
                }
            }
        }
        idx
    }

    // ── Queries ──────────────────────────────────────────────────────────────

    /// Id of a class by fully qualified name (`hr.Manager`).
    pub fn class_id(&self, full_name: &str) -> Option<ClassId> {
        self.classes.ids.get(full_name).copied()
    }

    /// Id of a property by fully qualified name (`hr.employer`).
    pub fn prop_id(&self, full_name: &str) -> Option<PropId> {
        self.props.ids.get(full_name).copied()
    }

    /// Every class whose last name segment is `name`, across namespaces.
    pub fn classes_named(&self, name: &str) -> &[ClassId] {
        self.classes.named(name)
    }

    /// Every property whose last name segment is `name`, across namespaces.
    pub fn props_named(&self, name: &str) -> &[PropId] {
        self.props.named(name)
    }

    /// Every property `name`, written in `file` (namespace `ns`), may denote:
    /// the one declared in `file`, else through a prefix alias, else any
    /// property whose qualified name ends with the written segments.
    pub fn props_for(&self, ns: &QualifiedName, file: &OntologyFile, name: &QualifiedName) -> Vec<PropId> {
        Scope::new(&ns.full(), file).resolve(&self.props, name)
    }

    /// Every class `name`, written in `file` (namespace `ns`), may denote;
    /// same resolution order as [`TypeIndex::props_for`].
    pub fn classes_for(&self, ns: &QualifiedName, file: &OntologyFile, name: &QualifiedName) -> Vec<ClassId> {
        Scope::new(&ns.full(), file).resolve(&self.classes, name)
    }

    /// Fully qualified name of a class.
    pub fn class_name(&self, id: ClassId) -> &str {
        &self.classes.full[id as usize]
    }

    /// Fully qualified name of a property.
    pub fn prop_name(&self, id: PropId) -> &str {
        &self.props.full[id as usize]
    }

    /// Strict, transitive ancestors.
    pub fn superclasses(&self, c: ClassId) -> &HashSet<ClassId> {
        &self.superclasses[c as usize]
    }

    /// Strict, transitive descendants.
    pub fn subclasses(&self, c: ClassId) -> &HashSet<ClassId> {
        &self.subclasses[c as usize]
    }

    /// Own and inherited properties of `c`.
    pub fn applicable_props(&self, c: ClassId) -> &HashSet<PropId> {
        &self.applicable[c as usize]
    }

    pub fn constraint(&self, c: ClassId, p: PropId) -> Option<&PropConstraint> {
        self.constraints.get(&(c, p))
    }

    /// Classes that declare `p` (a subject of `p` is one of them, or a subclass).
    pub fn domain(&self, p: PropId) -> &[ClassId] {
        &self.domain[p as usize]
    }

    /// Every value type `p` was declared with, across all declarations.
    pub fn range(&self, p: PropId) -> &[ValueType] {
        &self.range[p as usize]
    }

    /// Greatest lower bound of `a` and `b`: the most general classes that are
    /// both an `a` and a `b` (`a` itself when `a ⊑ b`). More than one = the
    /// hierarchy does not decide yet (e.g. two classes both `sub A, B`); empty =
    /// no declared class is both, which the caller reports as a conflict.
    /// Sorted by id. Costs O(size of the smaller subtree).
    pub fn meet(&self, a: ClassId, b: ClassId) -> Vec<ClassId> {
        let below = |c: ClassId| std::iter::once(c).chain(self.subclasses[c as usize].iter().copied());
        let (small, big) = if self.subclasses[a as usize].len() <= self.subclasses[b as usize].len() { (a, b) } else { (b, a) };
        let common: HashSet<ClassId> = below(small)
            .filter(|&c| c == big || self.superclasses[c as usize].contains(&big))
            .collect();
        // Keep a class unless another common one sits strictly above it
        // (strictly: members of a `sub` cycle are equivalent, keep them all).
        let mut out: Vec<ClassId> = common
            .iter()
            .copied()
            .filter(|&c| {
                !self.superclasses[c as usize]
                    .iter()
                    .any(|d| common.contains(d) && !self.superclasses[*d as usize].contains(&c))
            })
            .collect();
        out.sort_unstable();
        out
    }

    // ── Build helpers ────────────────────────────────────────────────────────

    fn intern_prop(&mut self, ns: &str, name: &str) -> PropId {
        let id = self.props.intern(ns, name);
        if id as usize == self.domain.len() {
            self.domain.push(Vec::new());
            self.range.push(Vec::new());
        }
        id
    }

    fn add_domain_range(&mut self, p: PropId, domain: &[ClassId], values: &[ValueType]) {
        let (d, r) = (&mut self.domain[p as usize], &mut self.range[p as usize]);
        d.extend(domain.iter().filter(|c| !d.contains(c)).copied().collect::<Vec<_>>());
        r.extend(values.iter().filter(|v| !r.contains(v)).copied().collect::<Vec<_>>());
    }
}

/// How one file sees class names.
struct Scope<'a> {
    ns: &'a str,
    prefixes: HashMap<&'a str, &'a QualifiedName>,
}

impl<'a> Scope<'a> {
    fn new(ns: &'a str, file: &'a OntologyFile) -> Self {
        Scope { ns, prefixes: file.prefixes.iter().map(|p| (p.alias.as_str(), &p.path)).collect() }
    }

    /// Every class a reference may denote. More than one = ambiguous, none =
    /// undeclared or external. Order: a bare name declared in this file, then
    /// a prefix alias on the first segment, then any class whose qualified
    /// name ends with the written segments.
    fn classes(&self, classes: &Names, t: &TypeRef) -> Vec<ClassId> {
        self.values(classes, t)
            .into_iter()
            .filter_map(|v| match v {
                ValueType::Class(c) => Some(c),
                ValueType::Primitive(_) | ValueType::Quantity => None,
            })
            .collect()
    }

    fn values(&self, classes: &Names, t: &TypeRef) -> Vec<ValueType> {
        match t {
            TypeRef::Named { name, .. } => {
                let ids = self.resolve(classes, name);
                if ids.is_empty() && dolfin_units::named_dimension(&name.last()).is_some() {
                    return vec![ValueType::Quantity];
                }
                ids.into_iter().map(ValueType::Class).collect()
            }
            TypeRef::Primitive { kind, .. } => vec![ValueType::Primitive(*kind)],
            TypeRef::Union { members, .. } => members.iter().flat_map(|m| self.values(classes, m)).collect(),
        }
    }

    /// Every id of `names` (classes or properties) a written name may denote.
    fn resolve(&self, names: &Names, name: &QualifiedName) -> Vec<u32> {
        let mut parts = name.parts.clone();
        if let [single] = &parts[..] {
            let local = if self.ns.is_empty() { single.clone() } else { format!("{}.{single}", self.ns) };
            if let Some(&id) = names.ids.get(&local) {
                return vec![id];
            }
        }
        if let Some(prefix) = parts.first().and_then(|p| self.prefixes.get(p.as_str())) {
            parts.splice(0..1, prefix.parts.iter().cloned());
        }
        let key = parts.join(".");
        let suffix = format!(".{key}");
        let Some(last) = parts.last() else { return Vec::new() };
        names
            .named(last)
            .iter()
            .copied()
            .filter(|&c| {
                let full = &names.full[c as usize];
                *full == key || full.ends_with(&suffix)
            })
            .collect()
    }
}

/// `(min, max)` a cardinality allows; no modifier means `any`.
fn bounds(card: Option<&Cardinality>) -> (usize, Option<usize>) {
    match card {
        None | Some(Cardinality::Any { .. }) => (0, None),
        Some(Cardinality::One { .. }) => (1, Some(1)),
        Some(Cardinality::Optional { .. }) => (0, Some(1)),
        Some(Cardinality::Some { .. }) => (1, None),
        Some(Cardinality::Exact { value, .. }) => (*value, Some(*value)),
        Some(Cardinality::Range { min, max, .. }) => (*min, *max),
    }
}

/// Intersect a new declaration into the constraint at `key`.
fn merge(
    map: &mut HashMap<(ClassId, PropId), PropConstraint>,
    key: (ClassId, PropId),
    min: usize,
    max: Option<usize>,
    values: Vec<ValueType>,
) {
    let c = map.entry(key).or_insert(PropConstraint { min: 0, max: None, ranges: Vec::new() });
    c.min = c.min.max(min);
    c.max = match (c.max, max) {
        (Some(a), Some(b)) => Some(a.min(b)),
        (a, b) => a.or(b),
    };
    if !values.is_empty() && !c.ranges.contains(&values) {
        c.ranges.push(values);
    }
}

/// Transitive parents of `c`, excluding `c` itself (cycle-safe).
fn ancestors(c: ClassId, parents: &[Vec<ClassId>]) -> HashSet<ClassId> {
    let mut seen = HashSet::new();
    let mut stack = parents[c as usize].clone();
    while let Some(p) = stack.pop() {
        if p != c && seen.insert(p) {
            stack.extend(&parents[p as usize]);
        }
    }
    seen
}

#[cfg(test)]
mod tests {
    use super::*;
    use rowl::parser::parse_ontology;

    fn build(files: &[(&str, &str)]) -> TypeIndex {
        let parsed: Vec<(QualifiedName, OntologyFile)> = files
            .iter()
            .map(|(ns, src)| {
                let parts = ns.split('.').filter(|s| !s.is_empty()).map(str::to_owned).collect();
                let file = parse_ontology(src).ontology.expect("parse failed");
                (QualifiedName::new(parts, None), file)
            })
            .collect();
        TypeIndex::build(parsed.iter().map(|(ns, f)| (ns, f)))
    }

    const FIXTURE: &str = "\
concept Agent:
  has name: one string

concept Company:
  has name: string

concept Employee:
  sub Agent
  has employer: Company
  has salary: optional float

concept Leader:
  sub Agent
  has team: some Employee

concept Manager:
  sub Employee, Leader
  has employer: one Company

concept Human:
  sub Agent

property mother: Human -> one Human
property badge: at most 2 Employee -> string
";

    fn names(idx: &TypeIndex, ids: impl IntoIterator<Item = ClassId>) -> HashSet<String> {
        ids.into_iter().map(|c| idx.class_name(c).to_owned()).collect()
    }

    fn set(xs: &[&str]) -> HashSet<String> {
        xs.iter().map(|s| s.to_string()).collect()
    }

    #[test]
    fn hierarchy_is_transitive_with_multiple_inheritance() {
        let idx = build(&[("hr", FIXTURE)]);
        let c = |n| idx.class_id(n).unwrap();

        assert_eq!(names(&idx, idx.superclasses(c("hr.Manager")).iter().copied()), set(&["hr.Employee", "hr.Leader", "hr.Agent"]));
        assert_eq!(
            names(&idx, idx.subclasses(c("hr.Agent")).iter().copied()),
            set(&["hr.Employee", "hr.Leader", "hr.Manager", "hr.Human"])
        );
        assert!(idx.superclasses(c("hr.Company")).is_empty());
    }

    #[test]
    fn applicable_props_include_inherited_and_standalone() {
        let idx = build(&[("hr", FIXTURE)]);
        let props = |n| -> HashSet<String> {
            idx.applicable_props(idx.class_id(n).unwrap())
                .iter()
                .map(|&p| idx.prop_name(p).to_owned())
                .collect()
        };

        assert_eq!(props("hr.Manager"), set(&["hr.name", "hr.employer", "hr.salary", "hr.team", "hr.badge"]));
        assert_eq!(props("hr.Leader"), set(&["hr.name", "hr.team"]));
        assert_eq!(props("hr.Company"), set(&["hr.name"]));
    }

    #[test]
    fn subclass_narrows_inherited_constraint() {
        let idx = build(&[("hr", FIXTURE)]);
        let c = |n| idx.class_id(n).unwrap();
        let employer = idx.prop_id("hr.employer").unwrap();

        // No modifier = any: the domain alone gives no restriction.
        let on_employee = idx.constraint(c("hr.Employee"), employer).unwrap();
        assert_eq!((on_employee.min, on_employee.max), (0, None));
        // Manager adds `one`.
        let on_manager = idx.constraint(c("hr.Manager"), employer).unwrap();
        assert_eq!((on_manager.min, on_manager.max), (1, Some(1)));
        assert_eq!(on_manager.ranges, vec![vec![ValueType::Class(c("hr.Company"))]]);
        assert!(idx.constraint(c("hr.Leader"), employer).is_none());
    }

    #[test]
    fn standalone_range_cardinality_bounds_values_per_subject() {
        let idx = build(&[("hr", FIXTURE)]);
        let c = |n| idx.class_id(n).unwrap();

        // `Human -> one Human`: exactly one mother each.
        let mother = idx.constraint(c("hr.Human"), idx.prop_id("hr.mother").unwrap()).unwrap();
        assert_eq!((mother.min, mother.max), (1, Some(1)));
        // `at most 2 Employee -> string`: the domain side bounds the inverse, not badges per employee.
        let badge = idx.constraint(c("hr.Manager"), idx.prop_id("hr.badge").unwrap()).unwrap();
        assert_eq!((badge.min, badge.max), (0, None));
    }

    #[test]
    fn same_name_in_two_namespaces_are_distinct() {
        let idx = build(&[("hr", FIXTURE), ("crm", "concept Company:\n  has vat: string\n")]);
        let hr_name = idx.prop_id("hr.name").unwrap();

        assert_eq!(names(&idx, idx.classes_named("Company").iter().copied()), set(&["hr.Company", "crm.Company"]));
        assert_eq!(names(&idx, idx.domain(hr_name).iter().copied()), set(&["hr.Agent", "hr.Company"]));
        assert_eq!(idx.range(hr_name), &[ValueType::Primitive(PrimitiveKind::String)]);
        assert!(!idx.applicable_props(idx.class_id("crm.Company").unwrap()).contains(&hr_name));
    }

    #[test]
    fn references_resolve_local_then_prefix_then_suffix() {
        let idx = build(&[
            ("lib.alpha", "concept Foo\nconcept OnlyA\n"),
            ("lib.beta", "concept Foo\n"),
            (
                "lib.c",
                "prefix lib.beta as bee\n\
                 concept Local:\n  has x: Foo\n  has y: alpha.Foo\n  has z: bee:Foo\n  has w: OnlyA\n\
                 concept Ambiguous:\n  sub Foo\n\
                 concept Picked:\n  sub alpha.Foo\n",
            ),
            ("lib.d", "concept Foo\nconcept Near:\n  has x: Foo\n"),
        ]);
        let c = |n| idx.class_id(n).unwrap();
        let range = |p| names(&idx, idx.range(idx.prop_id(p).unwrap()).iter().map(|v| match v {
            ValueType::Class(c) => *c,
            _ => unreachable!(),
        }));

        // Bare, not local: every `Foo` is a candidate.
        assert_eq!(range("lib.c.x"), set(&["lib.alpha.Foo", "lib.beta.Foo", "lib.d.Foo"]));
        assert_eq!(range("lib.c.y"), set(&["lib.alpha.Foo"]));
        assert_eq!(range("lib.c.z"), set(&["lib.beta.Foo"]));
        assert_eq!(range("lib.c.w"), set(&["lib.alpha.OnlyA"]));
        // Bare and local: the local one wins.
        assert_eq!(range("lib.d.x"), set(&["lib.d.Foo"]));
        // An ambiguous parent is not guessed.
        assert!(idx.superclasses(c("lib.c.Ambiguous")).is_empty());
        assert_eq!(idx.superclasses(c("lib.c.Picked")), &HashSet::from([c("lib.alpha.Foo")]));
    }

    const LATTICE: &str = "\
concept Agent
concept Company
concept Employee:
  sub Agent
concept Leader:
  sub Agent
concept Manager:
  sub Employee, Leader
concept Senior:
  sub Manager
concept Director:
  sub Employee, Leader
concept Intern:
  sub Employee
";

    #[test]
    fn meet_of_related_classes_is_the_more_specific() {
        let idx = build(&[("", LATTICE)]);
        let c = |n| idx.class_id(n).unwrap();

        assert_eq!(idx.meet(c("Manager"), c("Manager")), vec![c("Manager")]);
        assert_eq!(idx.meet(c("Agent"), c("Manager")), vec![c("Manager")]);
        assert_eq!(idx.meet(c("Senior"), c("Employee")), vec![c("Senior")]);
    }

    #[test]
    fn meet_keeps_most_general_common_subclasses() {
        let idx = build(&[("", LATTICE)]);
        let c = |n| idx.class_id(n).unwrap();

        // Manager and Director are both `sub Employee, Leader`; Senior is below Manager.
        let mut expected = vec![c("Manager"), c("Director")];
        expected.sort_unstable();
        assert_eq!(idx.meet(c("Employee"), c("Leader")), expected);
        assert!(idx.meet(c("Intern"), c("Leader")).is_empty());
    }

    #[test]
    fn meet_of_unrelated_classes_is_empty() {
        let idx = build(&[("", LATTICE)]);
        let c = |n| idx.class_id(n).unwrap();
        assert!(idx.meet(c("Company"), c("Agent")).is_empty());
    }

    #[test]
    fn meet_inside_a_sub_cycle_keeps_equivalents() {
        let idx = build(&[("", "concept A:\n  sub B\n\nconcept B:\n  sub A\n")]);
        let (a, b) = (idx.class_id("A").unwrap(), idx.class_id("B").unwrap());
        assert_eq!(idx.meet(a, b), vec![a.min(b), a.max(b)]);
    }

    #[test]
    fn sub_cycle_terminates() {
        let idx = build(&[("", "concept A:\n  sub B\n\nconcept B:\n  sub A\n")]);
        let (a, b) = (idx.class_id("A").unwrap(), idx.class_id("B").unwrap());
        assert_eq!(idx.superclasses(a), &HashSet::from([b]));
        assert_eq!(idx.subclasses(a), &HashSet::from([b]));
    }
}
