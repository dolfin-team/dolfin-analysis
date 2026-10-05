//! Semantic validation.
//!
//! Produces [`dolfin_diagnostic::Diagnostic`]s for structural problems:
//!
//! - **S001** Unresolved type reference
//! - **S002** Duplicate declaration name within the same file
//! - **S003** Circular inheritance (`concept A sub A`)
//! - **S004** Unknown property reference in a query, rule, or fact
//! - **S006** Unbound variable in a rule `then` block (not bound by `match`)
//! - **S008** Dimension mismatch: error on a fact value, warning on a query
//!   comparison (which can only match nothing)
//! - **S009** Bare fact value that is not a fact, enum member or concept
//! - **S010** Fact missing a required field (`one`, `some`, `exactly n`, `at least n`)

use std::cmp::Reverse;
use std::collections::{HashMap, HashSet};

use nucleo_matcher::pattern::{CaseMatching, Normalization, Pattern as FuzzyPattern};
use nucleo_matcher::{Config, Matcher, Utf32Str};

use dolfin_units::UnitRegistry;
use dolfin_diagnostic::{edit_distance, Diagnostic, DiagnosticBuilder, DiagnosticCode, FixSuggestion};
use rowl::{
    Constraint, ConstraintBlock, Declaration, Expr, FactAssertion, FactValue,
    Literal, Object, OntologyFile, Pattern, PropertyPattern, QualifiedName, QueryArg, QueryClause,
    Subject, ThenItem,
};

use crate::{index::{SymbolIndex, SymbolKind}, resolve::ResolvedFile};

// ── Validation entry point ────────────────────────────────────────────────────

/// Run all structural validation checks and return every diagnostic found.
pub fn validate(
    file: &OntologyFile,
    index: &SymbolIndex,
    resolved: &ResolvedFile,
) -> Vec<Diagnostic> {
    let mut diags = Vec::new();
    check_unresolved(file, resolved, &mut diags);
    check_duplicates(file, &mut diags);
    check_circular(file, &mut diags);
    // Quantities resolve against every `unitdef` in the indexed package.
    let (units, _) = crate::units::build_registry_from_units(index.units());
    validate_facts(file, index, &mut diags);
    validate_queries(file, index, &units, &mut diags);
    validate_rules(file, index, &mut diags);
    check_temporals(file, &units, &mut diags);
    check_dimensions(file, index, &units, &mut diags);
    diags
}

/// **S008** — a `quantity(...)` value assigned to a dimension-typed property
/// (e.g. `has weight: unit.Mass`) must have a compatible dimension; a bare
/// number on such a property is also an error. Properties with no known
/// dimension (an ordinary `float`, or a `TypeRef::Named` that isn't a
/// recognised dimension) are not checked here.
fn check_dimensions(
    file: &OntologyFile,
    index: &SymbolIndex,
    units: &UnitRegistry,
    diags: &mut Vec<Diagnostic>,
) {
    for decl in &file.declarations {
        if let Declaration::Fact(f) = decl {
            check_dimension_assertions(&f.assertions, index, units, diags);
        }
    }
}

fn check_dimension_assertions(
    assertions: &[FactAssertion],
    index: &SymbolIndex,
    units: &UnitRegistry,
    diags: &mut Vec<Diagnostic>,
) {
    for assertion in assertions {
        match assertion {
            FactAssertion::Property { property, values, .. } => {
                let expected = index.get(&property.last()).and_then(|s| s.dimension.as_ref());
                for v in values {
                    if let Some(expected) = expected {
                        check_dimension_value(v, &property.last(), expected, units, diags);
                    }
                    if let FactValue::Block { assertions, .. } = v {
                        check_dimension_assertions(assertions, index, units, diags);
                    }
                }
            }
            FactAssertion::Inverse { property, value, .. } => {
                let expected = index.get(&property.last()).and_then(|s| s.dimension.as_ref());
                if let Some(expected) = expected {
                    check_dimension_value(value, &property.last(), expected, units, diags);
                }
                if let FactValue::Block { assertions, .. } = value {
                    check_dimension_assertions(assertions, index, units, diags);
                }
            }
            FactAssertion::TypeHint { .. } => {}
        }
    }
}

fn check_dimension_value(
    value: &FactValue,
    property_name: &str,
    expected: &dolfin_units::Dimensions,
    units: &UnitRegistry,
    diags: &mut Vec<Diagnostic>,
) {
    let FactValue::Literal { value: lit, span } = value else {
        return;
    };
    let expected_label = dimension_label(expected);
    match lit {
        Literal::Quantity { .. } => {
            // A malformed quantity is already reported as S007 (INVALID_QUANTITY);
            // don't pile on a second diagnostic for the same literal.
            let Some(Ok(q)) = lit.resolve_quantity_with(units) else { return };
            if !q.dimensions.is_compatible_with(expected) {
                let found_label = dimension_label(&q.dimensions);
                diags.push(
                    DiagnosticBuilder::error(
                        DiagnosticCode::DIMENSION_MISMATCH,
                        format!(
                            "dimension mismatch: `{property_name}` expects a {expected_label} quantity, found {found_label}"
                        ),
                    )
                    .span_opt(span.map(Into::into))
                    .build(),
                );
            }
        }
        Literal::Int { .. } | Literal::Float { .. } => {
            diags.push(
                DiagnosticBuilder::error(
                    DiagnosticCode::DIMENSION_MISMATCH,
                    format!(
                        "dimension mismatch: `{property_name}` expects a {expected_label} quantity, found a bare number"
                    ),
                )
                .span_opt(span.map(Into::into))
                .build(),
            );
        }
        _ => {}
    }
}

/// `Mass` for a well-known dimension, else the canonical string (`L1.M1.T-2`).
fn dimension_label(dim: &dolfin_units::Dimensions) -> String {
    dolfin_units::dimension_label(dim)
        .map(str::to_string)
        .unwrap_or_else(|| dim.canonical_string())
}

/// **S005** — validate temporal smart literals (`date(...)`, `time(...)`,
/// `date_time(...)`, `duration(...)`) in fact values against the file-level
/// `@locale` / `@timezone` context.
///
/// Catches malformed values, ambiguous numeric dates with no mask or locale,
/// unknown timezones, and kind mismatches (e.g. `date(7d)`). Only fact values
/// are walked today; temporal literals embedded in query/rule expressions are
/// not yet validated here (they still resolve at render time).
fn check_temporals(file: &OntologyFile, units: &UnitRegistry, diags: &mut Vec<Diagnostic>) {
    // Build the context from @locale / @timezone; a malformed directive is
    // itself a diagnostic (on its own line) and is left unset, without
    // disabling the other directive.
    let (ctx, errors) = file.temporal_context_lenient();
    for (msg, span) in errors {
        diags.push(
            DiagnosticBuilder::error(
                DiagnosticCode::INVALID_TEMPORAL,
                format!("invalid temporal directive: {msg}"),
            )
            .span_opt(span.map(Into::into))
            .build(),
        );
    }

    // Iterative walk over every fact value, descending into anonymous blocks.
    let mut stack: Vec<&FactValue> = Vec::new();
    for decl in &file.declarations {
        if let Declaration::Fact(f) = decl {
            push_assertions(&f.assertions, &mut stack);
        }
    }
    while let Some(value) = stack.pop() {
        match value {
            FactValue::Literal { value: lit, .. } => {
                if let Some(Err(msg)) = lit.resolve_temporal(&ctx) {
                    let span = match lit {
                        Literal::Temporal { span, .. } => *span,
                        _ => None,
                    };
                    diags.push(
                        DiagnosticBuilder::error(
                            DiagnosticCode::INVALID_TEMPORAL,
                            format!("invalid temporal literal: {msg}"),
                        )
                        .span_opt(span.map(Into::into))
                        .build(),
                    );
                }
                if let Some(Err(msg)) = lit.resolve_quantity_with(units) {
                    let span = match lit {
                        Literal::Quantity { span, .. } => *span,
                        _ => None,
                    };
                    diags.push(
                        DiagnosticBuilder::error(
                            DiagnosticCode::INVALID_QUANTITY,
                            format!("invalid quantity literal: {msg}"),
                        )
                        .span_opt(span.map(Into::into))
                        .build(),
                    );
                }
            }
            FactValue::Block { assertions, .. } => push_assertions(assertions, &mut stack),
            _ => {}
        }
    }
}

fn push_assertions<'a>(assertions: &'a [FactAssertion], stack: &mut Vec<&'a FactValue>) {
    for a in assertions {
        match a {
            FactAssertion::Property { values, .. } => stack.extend(values.iter()),
            FactAssertion::Inverse { value, .. } => stack.push(value),
            FactAssertion::TypeHint { .. } => {}
        }
    }
}

// ── Checks ────────────────────────────────────────────────────────────────────

fn check_unresolved(_file: &OntologyFile, resolved: &ResolvedFile, diags: &mut Vec<Diagnostic>) {
    for r in resolved.unresolved() {
        // The "Declare concept" quick-fix is produced by the lint rule
        // `semantic/unresolved-type` (dolfin-lint), which has the package-wide
        // knowledge needed to choose the right file for a prefixed reference
        // (see `rowl::resolve_concept_file`). This pass only flags the error.
        diags.push(
            DiagnosticBuilder::error(
                DiagnosticCode::UNRESOLVED_TYPE,
                format!("type `{}` is not declared", r.name),
            )
            .span_opt(r.source_span.map(Into::into))
            .build(),
        );
    }
}

fn check_duplicates(file: &OntologyFile, diags: &mut Vec<Diagnostic>) {
    let mut seen: HashMap<&str, Option<rowl::error::Span>> = HashMap::new();
    for decl in &file.declarations {
        let (name, span) = decl_name_span(decl);
        if let Some(prev_span) = seen.get(name) {
            diags.push(
                DiagnosticBuilder::error(
                    DiagnosticCode::DUPLICATE_DECLARATION,
                    format!("duplicate declaration `{name}`"),
                )
                .span_opt(prev_span.map(Into::into))
                .build(),
            );
        } else {
            seen.insert(name, span);
        }
    }
}

fn check_circular(file: &OntologyFile, diags: &mut Vec<Diagnostic>) {
    let mut parents: HashMap<&str, Vec<String>> = HashMap::new();
    for decl in &file.declarations {
        if let Declaration::Concept(c) = decl {
            let ps = c
                .parents
                .iter()
                .filter_map(|p| match p {
                    rowl::TypeRef::Named { name, .. } => Some(name.full()),
                    _ => None,
                })
                .collect();
            parents.insert(c.name.get().as_str(), ps);
        }
    }

    for &start in parents.keys() {
        let mut visited = HashSet::new();
        let mut stack = vec![start];
        while let Some(node) = stack.pop() {
            if !visited.insert(node) {
                if node == start {
                    let span = file.declarations.iter().find_map(|d| {
                        if let Declaration::Concept(c) = d {
                            if c.name.get().as_str() == start {
                                c.span
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    });
                    diags.push(
                        DiagnosticBuilder::error(
                            DiagnosticCode::CIRCULAR_INHERITANCE,
                            format!("concept `{start}` has circular inheritance"),
                        )
                        .span_opt(span.map(Into::into))
                        .build(),
                    );
                }
                break;
            }
            if let Some(ps) = parents.get(node) {
                stack.extend(ps.iter().map(String::as_str));
            }
        }
    }
}

// ── Fact validation ───────────────────────────────────────────────────────────

fn validate_facts(file: &OntologyFile, index: &SymbolIndex, diags: &mut Vec<Diagnostic>) {
    // Collect all fact IDs defined in this file for forward-reference checking.
    let fact_ids: HashSet<&str> = file
        .declarations
        .iter()
        .filter_map(|d| {
            if let Declaration::Fact(f) = d {
                Some(f.id.as_str())
            } else {
                None
            }
        })
        .collect();
    let types = index.type_index();

    for decl in &file.declarations {
        let Declaration::Fact(f) = decl else { continue };
        check_required_fields(f, file, &types, diags);

        // §7.1 — each type name must resolve to a known concept.
        for type_qn in &f.types {
            let name = type_qn.last();
            if index.get(&name).is_none() && index.get(&type_qn.full()).is_none() {
                diags.push(
                    DiagnosticBuilder::error(
                        DiagnosticCode::UNRESOLVED_TYPE,
                        format!("unknown type `{}` in fact `{}`", name, f.id),
                    )
                    .span_opt(type_qn.span.map(Into::into))
                    .build(),
                );
            }
        }

        // §8 — forward/unknown fact references (`:name` with no qualifier)
        // and unknown property names (S004).
        let ctx = format!("fact `{}`", f.id);
        check_fact_assertions(&f.assertions, f, &fact_ids, index, &ctx, diags);
    }
}

/// **S010** — every field whose merged cardinality (own + inherited, see
/// [`crate::infer::TypeIndex`]) has a minimum above zero must be set by one of
/// the fact's own assertions. A type that does not resolve to exactly one
/// concept is skipped (S001 reports unknown ones). `is p of x` sets the
/// inverse property, not `p`, so it does not count.
fn check_required_fields(
    f: &rowl::ast::FactDef,
    file: &OntologyFile,
    types: &crate::infer::TypeIndex,
    diags: &mut Vec<Diagnostic>,
) {
    let set: HashSet<String> = f
        .assertions
        .iter()
        .filter_map(|a| match a {
            FactAssertion::Property { property, .. } => Some(property.last()),
            _ => None,
        })
        .collect();
    // Field name → first fact type requiring it, sorted for stable output.
    let mut missing: std::collections::BTreeMap<String, String> = Default::default();
    let ns = QualifiedName::default();
    for type_qn in &f.types {
        let [class] = types.classes_for(&ns, file, type_qn)[..] else { continue };
        for &p in types.applicable_props(class) {
            if types.constraint(class, p).is_none_or(|k| k.min == 0) {
                continue;
            }
            let name = types.prop_name(p).rsplit('.').next().unwrap_or_default();
            if !set.contains(name) {
                missing.entry(name.to_owned()).or_insert_with(|| type_qn.full());
            }
        }
    }
    for (field, ty) in missing {
        diags.push(
            DiagnosticBuilder::error(
                DiagnosticCode::MISSING_REQUIRED_VALUE,
                format!("missing required field `{field}` in fact `{}` (type `{ty}`)", f.id),
            )
            .span_opt(f.id_span.or(f.span).map(Into::into))
            .build(),
        );
    }
}

fn check_fact_assertions(
    assertions: &[FactAssertion],
    fact: &rowl::ast::FactDef,
    known_ids: &HashSet<&str>,
    index: &SymbolIndex,
    ctx: &str,
    diags: &mut Vec<Diagnostic>,
) {
    for assertion in assertions {
        match assertion {
            FactAssertion::Property { property, values, .. } => {
                check_property_qname(property, index, ctx, diags);
                for v in values {
                    check_fact_value_ref(v, fact, known_ids, index, ctx, diags);
                }
            }
            FactAssertion::Inverse { property, value, .. } => {
                check_property_qname(property, index, ctx, diags);
                check_fact_value_ref(value, fact, known_ids, index, ctx, diags);
            }
            FactAssertion::TypeHint { .. } => {}
        }
    }
}

fn check_fact_value_ref(
    value: &FactValue,
    fact: &rowl::ast::FactDef,
    known_ids: &HashSet<&str>,
    index: &SymbolIndex,
    ctx: &str,
    diags: &mut Vec<Diagnostic>,
) {
    match value {
        // `:Name` is the package-default prefix, as in Turtle. `package.dlf`
        // only holds the manifest, so no fact is declared there: `:Name` is
        // unresolved, and most likely a slip for the bare `Name`.
        FactValue::Reference { qualifier: None, name, span } => {
            let help = if known_ids.contains(name.as_str()) {
                format!("write `{name}` for the fact `{name}` of this file")
            } else {
                format!("write `{name}` for a fact of this package")
            };
            diags.push(
                DiagnosticBuilder::warning(
                    DiagnosticCode::UNRESOLVED_REFERENCE,
                    format!(
                        "`:{name}` in fact `{}` points at the package namespace, where `{name}` is not declared",
                        fact.id
                    ),
                )
                .help(help)
                .span_opt(span.map(Into::into))
                .build(),
            );
        }
        FactValue::Block { assertions, .. } => {
            check_fact_assertions(assertions, fact, known_ids, index, ctx, diags);
        }
        // A bare name is a fact, an enum member or a concept, from any file of
        // the package. ponytail: qualified names (`a.b.x`) are not checked yet.
        FactValue::Named { name, span } if name.parts.len() == 1 => {
            let known = index.get(&name.last()).is_some_and(|s| {
                matches!(
                    s.kind,
                    SymbolKind::FactInstance | SymbolKind::Individual { .. } | SymbolKind::Concept
                )
            });
            if !known {
                diags.push(
                    DiagnosticBuilder::error(
                        DiagnosticCode::UNRESOLVED_REFERENCE,
                        format!(
                            "`{}` in {} is not a fact, enum member or concept of this package",
                            name.last(),
                            ctx
                        ),
                    )
                    .span_opt(span.map(Into::into))
                    .build(),
                );
            }
        }
        _ => {}
    }
}

fn decl_name_span(decl: &Declaration) -> (&str, Option<rowl::error::Span>) {
    match decl {
        Declaration::Concept(c) => (c.name.get().as_str(), c.span),
        Declaration::Property(p) => (p.name.get(), p.span),
        Declaration::Rule(r) => (&r.name, r.span),
        Declaration::Fact(f) => (&f.id, f.span),
        Declaration::Query(q) => (&q.name, q.span),
        Declaration::Unit(u) => (u.name.get().as_str(), u.span),
    }
}

// ── Query property validation (S004, S008) ──────────────────────────────────

fn validate_queries(
    file: &OntologyFile,
    index: &SymbolIndex,
    units: &UnitRegistry,
    diags: &mut Vec<Diagnostic>,
) {
    for decl in &file.declarations {
        let Declaration::Query(q) = decl else { continue };
        let ctx = format!("query `{}`", q.name);
        check_query_clauses(&q.body.clauses, index, units, &ctx, diags);
    }
}

fn check_query_clauses(
    clauses: &[QueryClause],
    index: &SymbolIndex,
    units: &UnitRegistry,
    ctx: &str,
    diags: &mut Vec<Diagnostic>,
) {
    for clause in clauses {
        match clause {
            QueryClause::SubjectPattern(sp) => {
                check_property_patterns(&sp.properties, index, units, ctx, diags);
            }
            QueryClause::InverseTriple(it) => {
                check_property_qname(&it.property, index, ctx, diags);
            }
            QueryClause::ExistenceBlock(eb) => {
                check_query_clauses(&eb.clauses, index, units, ctx, diags);
            }
            QueryClause::AggregationQuery(aq) => {
                check_query_clauses(&aq.sub_clauses, index, units, ctx, diags);
            }
            QueryClause::Composition(_) | QueryClause::BooleanFilter(_) => {}
        }
    }
}

fn check_property_patterns(
    patterns: &[PropertyPattern],
    index: &SymbolIndex,
    units: &UnitRegistry,
    ctx: &str,
    diags: &mut Vec<Diagnostic>,
) {
    for pattern in patterns {
        match pattern {
            PropertyPattern::Value { property, .. }
            | PropertyPattern::Optional { property, .. }
            | PropertyPattern::Inverse { property, .. } => {
                check_property_qname(property, index, ctx, diags);
            }
            PropertyPattern::Constrained { property, block, .. } => {
                check_property_qname(property, index, ctx, diags);
                check_comparison_dimensions(Some(property), block, index, units, diags);
            }
            PropertyPattern::InverseNested { property, block, .. } => {
                check_property_qname(property, index, ctx, diags);
                check_comparison_dimensions(None, block, index, units, diags);
            }
            PropertyPattern::Nested { property, block, .. } => {
                check_property_qname(property, index, ctx, diags);
                check_property_patterns(&block.properties, index, units, ctx, diags);
            }
            PropertyPattern::Disjunction { either_branch, or_branches, .. } => {
                for branch in std::iter::once(either_branch).chain(or_branches) {
                    check_property_qname(&branch.property, index, ctx, diags);
                    check_comparison_dimensions(
                        Some(&branch.property),
                        &branch.block,
                        index,
                        units,
                        diags,
                    );
                }
            }
        }
    }
}

/// **S008** (warning) — in a query, `weight [ > quantity(40 m) ]` on a
/// dimension-typed property (`has weight: unit.Mass`) can never match: the
/// generated SPARQL guards on `dq:dimension`. `property` is the property whose
/// values `block` constrains (`None` for an inverse block, whose node is the
/// subject). Properties with no known dimension (a plain `float`) are silent.
fn check_comparison_dimensions(
    property: Option<&QualifiedName>,
    block: &ConstraintBlock,
    index: &SymbolIndex,
    units: &UnitRegistry,
    diags: &mut Vec<Diagnostic>,
) {
    let expected = property
        .and_then(|p| index.get(&p.last()))
        .and_then(|s| s.dimension.as_ref());
    for constraint in &block.constraints {
        match constraint {
            Constraint::Comparison { value: Expr::Literal { value: lit, .. }, span, .. } => {
                let (Some(expected), Some(property)) = (expected, property) else { continue };
                if !matches!(lit, Literal::Quantity { .. }) {
                    continue;
                }
                // Malformed quantities are already S007.
                let Some(Ok(q)) = lit.resolve_quantity_with(units) else { continue };
                if q.dimensions.is_compatible_with(expected) {
                    continue;
                }
                diags.push(
                    DiagnosticBuilder::warning(
                        DiagnosticCode::DIMENSION_MISMATCH,
                        format!(
                            "dimension mismatch: `{}` is a {} but is compared with a {} quantity, this query matches nothing",
                            property.last(),
                            dimension_label(expected),
                            dimension_label(&q.dimensions),
                        ),
                    )
                    .span_opt(span.map(Into::into))
                    .build(),
                );
            }
            Constraint::PropertyConstraint { property, block, .. } => {
                check_comparison_dimensions(Some(property), block, index, units, diags);
            }
            Constraint::InverseNested { block, .. } => {
                check_comparison_dimensions(None, block, index, units, diags);
            }
            Constraint::Comparison { .. }
            | Constraint::TypeIs { .. }
            | Constraint::PropertyValue { .. }
            | Constraint::Inverse { .. } => {}
        }
    }
}

// ── Rule property validation (S004) ──────────────────────────────────────────

fn validate_rules(file: &OntologyFile, index: &SymbolIndex, diags: &mut Vec<Diagnostic>) {
    for decl in &file.declarations {
        let Declaration::Rule(r) = decl else { continue };
        let ctx = format!("rule `{}`", r.name);
        check_rule(r, index, &ctx, &HashSet::new(), diags);
    }
}

fn check_rule(
    r: &rowl::ast::RuleDef,
    index: &SymbolIndex,
    ctx: &str,
    outer_bound: &HashSet<String>,
    diags: &mut Vec<Diagnostic>,
) {
    // Variables a `then` assertion may reference are those introduced by this
    // rule's `match` block plus any inherited from an enclosing rule. We
    // over-collect every variable appearing anywhere in `match` (subjects,
    // objects, expression operands, constraint bindings, quantified variables,
    // query-call args) rather than distinguishing binding from reference
    // positions — a conservative set that avoids false positives on valid rules.
    let mut bound = outer_bound.clone();
    for pattern in &r.match_block.patterns {
        collect_pattern_vars(pattern, &mut bound);
    }

    for pattern in &r.match_block.patterns {
        check_rule_pattern(pattern, index, ctx, diags);
    }
    for item in &r.then_block.items {
        match item {
            ThenItem::AssertionTriple { assertion, .. } => {
                check_property_qname(&assertion.property, index, ctx, diags);
                check_then_subject(&assertion.subject, &bound, ctx, diags);
                check_then_object(&assertion.object, &bound, ctx, diags);
            }
            ThenItem::AssertionTyping { subject, .. } => {
                check_then_subject(subject, &bound, ctx, diags);
            }
            ThenItem::NestedRule { rule } => {
                check_rule(rule, index, ctx, &bound, diags);
            }
        }
    }
}

// ── Rule variable binding: collect every variable a `match` block introduces ───

fn collect_pattern_vars(pattern: &Pattern, out: &mut HashSet<String>) {
    match pattern {
        Pattern::Triple { subject, object, .. } | Pattern::Inverse { subject, object, .. } => {
            collect_subject_vars(subject, out);
            collect_object_vars(object, out);
        }
        Pattern::Type { subject, .. } => collect_subject_vars(subject, out),
        Pattern::Quantified { variable, constraint, patterns, .. } => {
            out.insert(variable.clone());
            if let Some(block) = constraint {
                collect_block_vars(block, out);
            }
            for nested in patterns {
                collect_pattern_vars(nested, out);
            }
        }
        Pattern::QueryCall { args, .. } => {
            for arg in args {
                collect_query_arg_vars(arg, out);
            }
        }
    }
}

fn collect_subject_vars(subject: &Subject, out: &mut HashSet<String>) {
    match subject {
        Subject::Variable { name, .. } => {
            out.insert(name.clone());
        }
        Subject::Constraint { block, .. } => collect_block_vars(block, out),
        Subject::Constant { .. } => {}
    }
}

fn collect_object_vars(object: &Object, out: &mut HashSet<String>) {
    match object {
        Object::Variable { name, .. } => {
            out.insert(name.clone());
        }
        Object::Literal { value, .. } => collect_expr_vars(value, out),
        Object::Constraint { block } => collect_block_vars(block, out),
        Object::Constant { .. } => {}
    }
}

fn collect_expr_vars(expr: &Expr, out: &mut HashSet<String>) {
    match expr {
        Expr::Variable { name, .. } => {
            out.insert(name.clone());
        }
        Expr::BinaryOp { left, right, .. } => {
            collect_expr_vars(left, out);
            collect_expr_vars(right, out);
        }
        Expr::UnaryOp { operand, .. } => collect_expr_vars(operand, out),
        Expr::Literal { .. } => {}
    }
}

fn collect_block_vars(block: &ConstraintBlock, out: &mut HashSet<String>) {
    for constraint in &block.constraints {
        match constraint {
            Constraint::Comparison { binding, value, .. } => {
                if let Some(b) = binding {
                    out.insert(b.clone());
                }
                collect_expr_vars(value, out);
            }
            Constraint::PropertyValue { value, .. } | Constraint::Inverse { value, .. } => {
                collect_object_vars(value, out);
            }
            Constraint::PropertyConstraint { block, .. }
            | Constraint::InverseNested { block, .. } => collect_block_vars(block, out),
            Constraint::TypeIs { .. } => {}
        }
    }
}

fn collect_query_arg_vars(arg: &QueryArg, out: &mut HashSet<String>) {
    match arg {
        // `?var` shorthand binds `?var` into the rule scope.
        QueryArg::Var { name, .. } => {
            out.insert(name.clone());
        }
        // `?param = <value>`: `param` names the query's own parameter, not a
        // rule variable; only the value expression carries rule-scope bindings.
        QueryArg::Binding { value, .. } => collect_object_vars(value, out),
    }
}

// ── Rule variable binding: flag `then`-side variables not bound by `match` ─────

fn check_then_subject(
    subject: &Subject,
    bound: &HashSet<String>,
    ctx: &str,
    diags: &mut Vec<Diagnostic>,
) {
    match subject {
        Subject::Variable { name, span } => report_if_unbound(name, *span, bound, ctx, diags),
        Subject::Constraint { block, .. } => check_then_block(block, bound, ctx, diags),
        Subject::Constant { .. } => {}
    }
}

fn check_then_object(
    object: &Object,
    bound: &HashSet<String>,
    ctx: &str,
    diags: &mut Vec<Diagnostic>,
) {
    match object {
        Object::Variable { name, span } => report_if_unbound(name, *span, bound, ctx, diags),
        Object::Literal { value, .. } => check_then_expr(value, bound, ctx, diags),
        Object::Constraint { block } => check_then_block(block, bound, ctx, diags),
        Object::Constant { .. } => {}
    }
}

fn check_then_expr(expr: &Expr, bound: &HashSet<String>, ctx: &str, diags: &mut Vec<Diagnostic>) {
    match expr {
        Expr::Variable { name, span } => report_if_unbound(name, *span, bound, ctx, diags),
        Expr::BinaryOp { left, right, .. } => {
            check_then_expr(left, bound, ctx, diags);
            check_then_expr(right, bound, ctx, diags);
        }
        Expr::UnaryOp { operand, .. } => check_then_expr(operand, bound, ctx, diags),
        Expr::Literal { .. } => {}
    }
}

fn check_then_block(
    block: &ConstraintBlock,
    bound: &HashSet<String>,
    ctx: &str,
    diags: &mut Vec<Diagnostic>,
) {
    for constraint in &block.constraints {
        match constraint {
            Constraint::Comparison { binding, value, span, .. } => {
                if let Some(b) = binding {
                    report_if_unbound(b, *span, bound, ctx, diags);
                }
                check_then_expr(value, bound, ctx, diags);
            }
            Constraint::PropertyValue { value, .. } | Constraint::Inverse { value, .. } => {
                check_then_object(value, bound, ctx, diags);
            }
            Constraint::PropertyConstraint { block, .. }
            | Constraint::InverseNested { block, .. } => check_then_block(block, bound, ctx, diags),
            Constraint::TypeIs { .. } => {}
        }
    }
}

fn report_if_unbound(
    name: &str,
    span: Option<rowl::error::Span>,
    bound: &HashSet<String>,
    ctx: &str,
    diags: &mut Vec<Diagnostic>,
) {
    if bound.contains(name) {
        return;
    }
    diags.push(
        DiagnosticBuilder::error(
            DiagnosticCode::UNBOUND_VARIABLE,
            format!(
                "unbound variable `{}` in the `then` block of {} — it is not bound by the `match` block",
                name, ctx
            ),
        )
        .span_opt(span.map(Into::into))
        .build(),
    );
}

fn check_rule_pattern(
    pattern: &Pattern,
    index: &SymbolIndex,
    ctx: &str,
    diags: &mut Vec<Diagnostic>,
) {
    match pattern {
        Pattern::Triple { property, .. } => {
            check_property_qname(property, index, ctx, diags);
        }
        Pattern::Quantified { constraint, patterns, .. } => {
            if let Some(block) = constraint {
                check_constraint_block(block, index, ctx, diags);
            }
            for p in patterns {
                check_rule_pattern(p, index, ctx, diags);
            }
        }
        Pattern::Inverse { property, object, .. } => {
            check_property_qname(property, index, ctx, diags);
            if let Object::Constraint { block } = object {
                check_constraint_block(block, index, ctx, diags);
            }
        }
        Pattern::Type { .. } | Pattern::QueryCall { .. } => {}
    }
}

fn check_constraint_block(
    block: &ConstraintBlock,
    index: &SymbolIndex,
    ctx: &str,
    diags: &mut Vec<Diagnostic>,
) {
    for constraint in &block.constraints {
        match constraint {
            Constraint::PropertyValue { property, .. } => {
                check_property_qname(property, index, ctx, diags);
            }
            Constraint::PropertyConstraint { property, block, .. } => {
                check_property_qname(property, index, ctx, diags);
                check_constraint_block(block, index, ctx, diags);
            }
            Constraint::Inverse { property, .. } => {
                check_property_qname(property, index, ctx, diags);
            }
            Constraint::InverseNested { property, block, .. } => {
                check_property_qname(property, index, ctx, diags);
                check_constraint_block(block, index, ctx, diags);
            }
            Constraint::TypeIs { .. } | Constraint::Comparison { .. } => {}
        }
    }
}

// ── Shared property-reference check ───────────────────────────────────────────

fn check_property_qname(
    property: &QualifiedName,
    index: &SymbolIndex,
    ctx: &str,
    diags: &mut Vec<Diagnostic>,
) {
    let is_property = |name: &str| {
        matches!(index.get(name).map(|s| &s.kind), Some(SymbolKind::Property))
    };
    if is_property(&property.last()) || is_property(&property.full()) {
        return;
    }
    // Skip prefixed names (e.g. `rdfs:label`) — may reference external vocabularies.
    if property.is_prefixed {
        return;
    }
    let name = property.last();
    let mut builder = DiagnosticBuilder::error(
        DiagnosticCode::UNKNOWN_PROPERTY,
        format!("unknown property `{}` in {}", name, ctx),
    )
    .span_opt(property.span.map(Into::into));
    if let Some(suggestion) = suggest_property(&name, index) {
        builder = builder.help(format!("did you mean `{}`?", suggestion));
        if let Some(span) = property.span {
            builder = builder.fix(FixSuggestion::single(
                format!("Replace with `{}`", suggestion),
                span.into(),
                suggestion,
            ));
        }
    }
    diags.push(builder.build());
}

/// Find the closest known property name to `name`, for a "did you mean …?"
/// hint. Mirrors concept/type suggestions by using the same nucleo fuzzy
/// matcher as the primary signal (catches dropped chars, prefixes, reordered
/// words), then falls back to a bounded edit-distance pass so transposition typos
/// like `wieght` → `weight` — which nucleo's subsequence match misses — still
/// surface. Returns `None` when nothing is close on either signal.
fn suggest_property(name: &str, index: &SymbolIndex) -> Option<String> {
    let candidates = index.property_names();

    let mut matcher = Matcher::new(Config::DEFAULT);
    let pattern = FuzzyPattern::parse(name, CaseMatching::Ignore, Normalization::Smart);
    let mut buf = Vec::new();
    let fuzzy = candidates
        .iter()
        .filter_map(|cand| {
            let haystack = Utf32Str::new(cand, &mut buf);
            pattern.score(haystack, &mut matcher).map(|score| (score, *cand))
        })
        // Highest fuzzy score wins; tie-break toward the shorter candidate.
        .max_by_key(|(score, cand)| (*score, Reverse(cand.len())))
        .map(|(_, cand)| cand.to_owned());
    if fuzzy.is_some() {
        return fuzzy;
    }

    // Fallback: allow at most a third of the typed name (min 1) to differ,
    // capped at 3 edits. Covers transpositions nucleo cannot subsequence-match.
    let max_dist = (name.chars().count() / 3).clamp(1, 3);
    candidates
        .into_iter()
        .map(|cand| (cand, edit_distance(name, cand)))
        .filter(|(_, d)| *d <= max_dist)
        .min_by_key(|(cand, d)| (*d, cand.len()))
        .map(|(cand, _)| cand.to_owned())
}

// ── Re-export for downstream crates that still import from here ───────────────
pub use dolfin_diagnostic::Severity;

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use rowl::parser::parse_ontology;

    fn parse(src: &str) -> OntologyFile {
        parse_ontology(src).ontology.expect("parse failed")
    }

    fn make_index(file: &OntologyFile) -> SymbolIndex {
        SymbolIndex::from_file(file)
    }

    fn make_resolved(file: &OntologyFile, index: &SymbolIndex) -> crate::resolve::ResolvedFile {
        crate::resolve::resolve_file(file, index)
    }

    #[test]
    fn known_property_no_diagnostic() {
        let src = "\
concept Animal
property age: Animal -> int
query find_animals:
  ?x a Animal
    age ?y
";
        let file = parse(src);
        let index = make_index(&file);
        let resolved = make_resolved(&file, &index);
        let diags = validate(&file, &index, &resolved);
        let prop_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.code == DiagnosticCode::UNKNOWN_PROPERTY)
            .collect();
        assert!(prop_diags.is_empty(), "unexpected S004 diagnostics: {:?}", prop_diags);
    }

    #[test]
    fn unknown_property_emits_s004() {
        let src = "\
concept Animal
query find_animals:
  ?x a Animal
    ghost_prop ?y
";
        let file = parse(src);
        let index = make_index(&file);
        let resolved = make_resolved(&file, &index);
        let diags = validate(&file, &index, &resolved);
        let prop_diags: Vec<_> = diags
            .iter()
            .filter(|d| d.code == DiagnosticCode::UNKNOWN_PROPERTY)
            .collect();
        assert_eq!(prop_diags.len(), 1, "expected exactly one S004, got: {:?}", prop_diags);
        assert!(prop_diags[0].message.contains("ghost_prop"));
    }

    fn s004(src: &str) -> Vec<Diagnostic> {
        let file = parse(src);
        let index = make_index(&file);
        let resolved = make_resolved(&file, &index);
        validate(&file, &index, &resolved)
            .into_iter()
            .filter(|d| d.code == DiagnosticCode::UNKNOWN_PROPERTY)
            .collect()
    }

    // ── S009 unresolved bare fact value ──────────────────────────────────────

    /// S009 for `src`, with `other` indexed as a second file of the package.
    fn s009(src: &str, other: &str) -> Vec<Diagnostic> {
        let file = parse(src);
        let mut index = SymbolIndex::default();
        index.add_file("a.dlf", &file);
        index.add_file("b.dlf", &parse(other));
        let resolved = make_resolved(&file, &index);
        validate(&file, &index, &resolved)
            .into_iter()
            .filter(|d| d.code == DiagnosticCode::UNRESOLVED_REFERENCE)
            .collect()
    }

    #[test]
    fn bare_fact_value_resolves_across_files() {
        let other = "concept Plan:\n  one of:\n    Monthly\n\nconcept Customer\n\nfact alice a Customer\n";
        let src = "concept Rental:\n  has customer: one Customer\n  has plan: one Plan\n\n\
                   fact r1 a Rental\n  customer alice\n  plan Monthly\n\n\
                   fact r2 a Rental\n  customer r1\n";
        assert!(s009(src, other).is_empty(), "unexpected S009: {:?}", s009(src, other));
    }

    #[test]
    fn unknown_bare_fact_value_emits_s009() {
        let src = "concept Rental:\n  has customer: one Rental\n\nfact r1 a Rental\n  customer nobody\n";
        let diags = s009(src, "concept Other\n");
        assert_eq!(diags.len(), 1, "expected one S009, got: {diags:?}");
        assert!(diags[0].message.contains("nobody"));
    }

    /// `:Name` is the package namespace, never the fact `Name` of this file.
    #[test]
    fn colon_fact_reference_warns_package_namespace() {
        let src = "concept Owner\n\nconcept Dog:\n  has owner: one Owner\n\n\
                   fact JohnSmith a Owner\n\nfact Biscuit a Dog\n  owner :JohnSmith\n";
        let diags = s009(src, "concept Other\n");
        assert_eq!(diags.len(), 1, "expected one S009, got: {diags:?}");
        assert_eq!(diags[0].severity, Severity::Warning);
        assert!(diags[0].message.contains("package namespace"), "{}", diags[0].message);
        assert!(diags[0].message.contains("`:JohnSmith`"), "{}", diags[0].message);

        let bare = src.replace("owner :JohnSmith", "owner JohnSmith");
        assert!(s009(&bare, "concept Other\n").is_empty());
    }

    #[test]
    fn unknown_property_in_rule_emits_s004() {
        let src = "\
concept Animal
rule tag_old:
  match:
    ?x a Animal
    ?x ghost_prop ?y
  then:
    ?x other_ghost ?y
";
        let diags = s004(src);
        assert_eq!(diags.len(), 2, "expected two S004, got: {:?}", diags);
        assert!(diags.iter().any(|d| d.message.contains("ghost_prop")));
        assert!(diags.iter().any(|d| d.message.contains("other_ghost")));
        assert!(diags.iter().all(|d| d.message.contains("rule `tag_old`")));
    }

    // ── S006 unbound variable in `then` ──────────────────────────────────────

    fn unbound(src: &str) -> Vec<Diagnostic> {
        let file = parse(src);
        let index = make_index(&file);
        let resolved = make_resolved(&file, &index);
        validate(&file, &index, &resolved)
            .into_iter()
            .filter(|d| d.code == DiagnosticCode::UNBOUND_VARIABLE)
            .collect()
    }

    #[test]
    fn unbound_bare_object_variable_in_then_emits_s006() {
        let src = "\
concept Animal
property tag: Animal -> int
rule r:
  match:
    ?x a Animal
  then:
    ?x tag ?y
";
        let diags = unbound(src);
        assert_eq!(diags.len(), 1, "expected one S006, got: {:?}", diags);
        assert!(diags[0].message.contains("?y"));
        assert!(diags[0].message.contains("rule `r`"));
    }

    #[test]
    fn unbound_variable_inside_math_expression_in_then_emits_s006() {
        // `?y` appears only inside the math expression `?y + 1`.
        let src = "\
concept Animal
property tag: Animal -> int
rule r:
  match:
    ?x a Animal
  then:
    ?x tag ?y + 1
";
        let diags = unbound(src);
        assert_eq!(diags.len(), 1, "expected one S006, got: {:?}", diags);
        assert!(diags[0].message.contains("?y"));
    }

    #[test]
    fn bound_variable_used_in_then_expression_is_clean() {
        // `?y` is bound by the match block, so `?y + 1` in `then` is fine.
        let src = "\
concept Animal
property value: Animal -> int
property tag: Animal -> int
rule r:
  match:
    ?x a Animal
    ?x value ?y
  then:
    ?x tag ?y + 1
";
        let diags = unbound(src);
        assert!(diags.is_empty(), "unexpected S006: {:?}", diags);
    }

    #[test]
    fn unbound_subject_variable_in_then_emits_s006() {
        let src = "\
concept Animal
property tag: Animal -> int
rule r:
  match:
    ?x a Animal
  then:
    ?z tag ?x
";
        let diags = unbound(src);
        assert_eq!(diags.len(), 1, "expected one S006, got: {:?}", diags);
        assert!(diags[0].message.contains("?z"));
    }

    #[test]
    fn variable_bound_by_match_constraint_comparison_is_clean() {
        // `?y` is introduced as a comparison binding in the match block.
        let src = "\
concept Animal
property value: Animal -> int
property tag: Animal -> int
rule r:
  match:
    ?x a Animal
    ?x value [ ?y >= 0 ]
  then:
    ?x tag ?y
";
        let diags = unbound(src);
        assert!(diags.is_empty(), "unexpected S006: {:?}", diags);
    }

    #[test]
    fn unknown_property_in_fact_emits_s004() {
        let src = "\
concept Animal
fact rex a Animal
  ghost_prop 3
";
        let diags = s004(src);
        assert_eq!(diags.len(), 1, "expected one S004, got: {:?}", diags);
        assert!(diags[0].message.contains("ghost_prop"));
        assert!(diags[0].message.contains("fact `rex`"));
    }

    #[test]
    fn known_property_in_rule_and_fact_no_diagnostic() {
        let src = "\
concept Animal
property age: Animal -> int
rule r:
  match:
    ?x age ?y
  then:
    ?x age ?y
fact rex a Animal
  age 3
";
        assert!(s004(src).is_empty());
    }

    #[test]
    fn has_block_property_no_diagnostic() {
        // A property declared inline in a concept's `has` block must be
        // recognised everywhere a top-level `property` would be (no S004).
        let src = "\
concept Animal:
  has age: int
query find_animals:
  ?x a Animal
    age ?y
fact rex a Animal
  age 3
";
        assert!(s004(src).is_empty(), "unexpected S004: {:?}", s004(src));
    }

    #[test]
    fn unknown_property_suggests_close_match() {
        let src = "\
concept Animal
property weight: Animal -> int
query q:
  ?x a Animal
    wieght ?y
";
        let diags = s004(src);
        assert_eq!(diags.len(), 1, "got: {:?}", diags);
        let help = diags[0].help.as_deref().unwrap_or("");
        assert!(help.contains("weight"), "expected suggestion `weight`, got help: {:?}", help);

        // The suggestion must also be an applyable fix (Quick Fix / apply button),
        // not just a help string.
        let fix = diags[0].fix.as_ref().expect("expected a FixSuggestion on S004");
        assert_eq!(fix.edits.len(), 1, "expected single-edit fix, got: {:?}", fix);
        assert_eq!(fix.edits[0].replacement, "weight");
    }

    fn s001(src: &str) -> Vec<Diagnostic> {
        let file = parse(src);
        let index = make_index(&file);
        let resolved = make_resolved(&file, &index);
        validate(&file, &index, &resolved)
            .into_iter()
            .filter(|d| d.code == DiagnosticCode::UNRESOLVED_TYPE)
            .collect()
    }

    #[test]
    fn undeclared_type_is_flagged_without_fix() {
        // `Owner` is referenced as a property domain but never declared. This
        // pass flags the error; the "Declare concept" quick-fix now lives in
        // the `semantic/unresolved-type` lint rule (which knows the package
        // layout and can target the right file for a prefixed reference).
        let src = "\
concept Animal
property owns: Owner -> Animal
";
        let diags = s001(src);
        assert_eq!(diags.len(), 1, "expected one S001, got: {:?}", diags);
        assert!(diags[0].message.contains("Owner"));
        assert!(
            diags[0].fix.is_none(),
            "S001 no longer carries a fix — lint owns it, got: {:?}",
            diags[0].fix
        );
    }

    #[test]
    fn well_known_dimension_name_is_not_flagged_without_units_dlf() {
        // `Mass` is a built-in physical dimension name (dolfin_units::named_dimension);
        // it must resolve even with no `concept Mass` declared anywhere in the
        // package (i.e. without dropping `units.dlf` into the project).
        let src = "\
concept Animal:
  has weight: Mass
";
        let diags = s001(src);
        assert!(diags.is_empty(), "expected no S001 for a well-known dimension name, got: {:?}", diags);
    }

    // ── temporal literal validation (S005) ─────────────────────────────────

    fn temporal_diags(src: &str) -> Vec<Diagnostic> {
        let file = parse(src);
        let index = make_index(&file);
        let resolved = make_resolved(&file, &index);
        validate(&file, &index, &resolved)
            .into_iter()
            .filter(|d| d.code == DiagnosticCode::INVALID_TEMPORAL)
            .collect()
    }

    #[test]
    fn valid_temporal_no_diagnostic() {
        let src = "\
concept Person
fact bob a Person
  birthDate date(June 1st 2026)
";
        assert!(temporal_diags(src).is_empty());
    }

    #[test]
    fn kind_mismatch_flagged() {
        // date(7d) parses as a duration → mismatch.
        let src = "\
concept Person
fact bob a Person
  birthDate date(7d)
";
        let diags = temporal_diags(src);
        assert_eq!(diags.len(), 1, "expected one S005, got: {diags:?}");
    }

    #[test]
    fn ambiguous_numeric_date_flagged_without_locale() {
        let src = "\
concept Person
fact bob a Person
  birthDate date(01/06/2026)
";
        assert_eq!(temporal_diags(src).len(), 1);
    }

    #[test]
    fn locale_directive_resolves_numeric_date() {
        let src = "\
@locale d/m/y
concept Person
fact bob a Person
  birthDate date(01/06/2026)
";
        assert!(temporal_diags(src).is_empty());
    }

    #[test]
    fn bad_locale_directive_flagged() {
        let src = "\
@locale nonsense
concept Person
fact bob a Person
  birthDate date(June 1st 2026)
";
        let diags = temporal_diags(src);
        assert!(!diags.is_empty(), "expected a directive diagnostic");
    }

    #[test]
    fn unknown_timezone_directive_flagged() {
        let src = "\
@timezone Mars/Base
concept Person
fact bob a Person
  seenAt time(14:30)
";
        assert!(!temporal_diags(src).is_empty());
    }

    #[test]
    fn iana_timezone_accepted_and_bad_timezone_keeps_locale() {
        // BUGS.md #5: IANA names resolve; a bad @timezone is reported on its
        // own line and does not switch @locale off.
        let ok = "\
@locale d/m/y
@timezone Europe/Paris
concept Person
fact bob a Person
  birthDate date(15/03/2025)
";
        assert!(temporal_diags(ok).is_empty(), "{:?}", temporal_diags(ok));
        let bad = ok.replace("Europe/Paris", "Mars/Base");
        let diags = temporal_diags(&bad);
        assert_eq!(diags.len(), 1, "only the directive is flagged: {diags:?}");
        assert_eq!(diags[0].span.as_ref().map(|s| s.start.line), Some(2));
    }

    // ── quantity literal validation (S007) ─────────────────────────────────

    fn quantity_diags(src: &str) -> Vec<Diagnostic> {
        let file = parse(src);
        let index = make_index(&file);
        let resolved = make_resolved(&file, &index);
        validate(&file, &index, &resolved)
            .into_iter()
            .filter(|d| d.code == DiagnosticCode::INVALID_QUANTITY)
            .collect()
    }

    #[test]
    fn valid_quantity_no_diagnostic() {
        let src = "\
concept Vehicle
fact car a Vehicle
  topSpeed quantity(42 km/h)
";
        assert!(quantity_diags(src).is_empty());
    }

    #[test]
    fn unknown_unit_flagged() {
        let src = "\
concept Vehicle
fact car a Vehicle
  topSpeed quantity(42 zonks)
";
        let diags = quantity_diags(src);
        assert_eq!(diags.len(), 1, "expected one S007, got: {diags:?}");
        assert!(diags[0].message.contains("quantity"));
    }

    #[test]
    fn package_unitdef_resolves_across_files() {
        // `USD` is declared in one file and used in another.
        let units = parse("unitdef USD: scale 0.92 EUR\n");
        let facts = parse(
            "concept Account\nfact acct a Account\n  total quantity(1200 USD)\n  other quantity(3 zonks)\n",
        );
        let mut index = SymbolIndex::default();
        index.add_file("units.dlf", &units);
        index.add_file("facts.dlf", &facts);
        let resolved = make_resolved(&facts, &index);
        let diags: Vec<_> = validate(&facts, &index, &resolved)
            .into_iter()
            .filter(|d| d.code == DiagnosticCode::INVALID_QUANTITY)
            .collect();
        assert_eq!(diags.len(), 1, "only `zonks` should be unknown, got: {diags:?}");
        assert!(diags[0].message.contains("zonks"));
    }

    #[test]
    fn incompatible_as_conversion_flagged() {
        // Converting a length to a time is dimensionally impossible.
        let src = "\
concept Vehicle
fact car a Vehicle
  odo quantity(5 km as s)
";
        assert_eq!(quantity_diags(src).len(), 1);
    }

    #[test]
    fn valid_as_conversion_no_diagnostic() {
        let src = "\
concept Vehicle
fact car a Vehicle
  topSpeed quantity(42 km/h as m/s)
";
        assert!(quantity_diags(src).is_empty());
    }

    fn dimension_diags(src: &str) -> Vec<Diagnostic> {
        let file = parse(src);
        let index = make_index(&file);
        let resolved = make_resolved(&file, &index);
        validate(&file, &index, &resolved)
            .into_iter()
            .filter(|d| d.code == DiagnosticCode::DIMENSION_MISMATCH)
            .collect()
    }

    #[test]
    fn matching_dimension_no_diagnostic() {
        let src = "\
concept Mass
concept Animal:
  has weight: unit.Mass
fact rex a Animal
  weight quantity(45 kg)
";
        assert!(dimension_diags(src).is_empty());
    }

    #[test]
    fn mismatched_dimension_flagged() {
        let src = "\
concept Mass
concept Animal:
  has weight: unit.Mass
fact rex a Animal
  weight quantity(3 m)
";
        let diags = dimension_diags(src);
        assert_eq!(diags.len(), 1, "expected exactly one S008, got: {:?}", diags);
        assert!(diags[0].message.contains("weight"));
    }

    #[test]
    fn bare_number_on_dimension_typed_property_flagged() {
        let src = "\
concept Mass
concept Animal:
  has weight: unit.Mass
fact rex a Animal
  weight 45
";
        assert_eq!(dimension_diags(src).len(), 1);
    }

    #[test]
    fn untyped_float_property_not_checked() {
        let src = "\
concept Animal:
  has weight: optional float
fact rex a Animal
  weight quantity(3 m)
";
        assert!(dimension_diags(src).is_empty());
    }

    // ── S008 in queries (warning) ────────────────────────────────────────────

    const MASS_ANIMAL: &str = "\
concept Mass
concept Animal:
  has weight: unit.Mass
  has friend: Animal
";

    fn query_dimension_diags(query: &str) -> Vec<Diagnostic> {
        dimension_diags(&format!("{MASS_ANIMAL}{query}"))
    }

    #[test]
    fn query_mismatched_quantity_warns() {
        let src = format!("{MASS_ANIMAL}query heavy:\n  ?dog a Animal\n    weight [ > quantity(40 m) ]\n");
        let diags = dimension_diags(&src);
        assert_eq!(diags.len(), 1, "{diags:?}");
        assert_eq!(diags[0].severity, dolfin_diagnostic::Severity::Warning);
        assert_eq!(
            diags[0].message,
            "dimension mismatch: `weight` is a Mass but is compared with a Length quantity, this query matches nothing"
        );
        let span = diags[0].span.as_ref().expect("span");
        assert!(src[span.start.offset..span.end.offset].contains("quantity(40 m)"));
    }

    #[test]
    fn query_compatible_quantity_no_warning() {
        for unit in ["kg", "lb"] {
            let q = format!("query heavy:\n  ?dog a Animal\n    weight [ > quantity(40 {unit}) ]\n");
            assert!(query_dimension_diags(&q).is_empty(), "{unit}");
        }
    }

    #[test]
    fn query_bound_comparison_still_checked() {
        let q = "query heavy:\n  ?dog a Animal\n    weight [ ?w > quantity(40 m) ]\n";
        assert_eq!(query_dimension_diags(q).len(), 1);
    }

    #[test]
    fn query_untyped_float_property_not_checked() {
        let src = "\
concept Animal:
  has weight: optional float
query heavy:
  ?dog a Animal
    weight [ > quantity(40 m) ]
";
        assert!(dimension_diags(src).is_empty());
    }

    #[test]
    fn query_nested_and_existence_blocks_checked() {
        let nested = "query q:\n  ?dog a Animal\n    friend [ weight [ > quantity(40 m) ] ]\n";
        assert_eq!(query_dimension_diags(nested).len(), 1, "nested");
        let some = "query q:\n  ?dog a Animal\n  some:\n    ?dog weight [ > quantity(40 m) ]\n";
        assert_eq!(query_dimension_diags(some).len(), 1, "some:");
    }

    #[test]
    fn query_malformed_quantity_no_s008() {
        let q = "query q:\n  ?dog a Animal\n    weight [ > quantity(40 bogusunit) ]\n";
        assert!(query_dimension_diags(q).is_empty());
    }

    #[test]
    fn fact_dimension_mismatch_stays_error() {
        let diags = dimension_diags(&format!("{MASS_ANIMAL}fact rex a Animal\n  weight quantity(3 m)\n"));
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].severity, dolfin_diagnostic::Severity::Error);
    }

    // ── S010 missing required field ──────────────────────────────────────────

    const CLINIC: &str = "\
concept Clinic
concept Animal:
  has name: one string
  has nickname: optional string
  has toys: string
  has tags: any string
concept Dog:
  sub Animal
  has neutered: one boolean
concept Appointment:
  has clinic: one Clinic
  has notes: some string
  has vets: at least 2 string
concept Booking:
  has clinic: one Clinic
  has paid: one boolean
";

    /// S010 for `src`, with `other` indexed as a second file of the package.
    fn s010(src: &str, other: &str) -> Vec<Diagnostic> {
        let file = parse(src);
        let mut index = SymbolIndex::default();
        index.add_file("a.dlf", &file);
        index.add_file("b.dlf", &parse(other));
        let resolved = make_resolved(&file, &index);
        validate(&file, &index, &resolved)
            .into_iter()
            .filter(|d| d.code == DiagnosticCode::MISSING_REQUIRED_VALUE)
            .collect()
    }

    fn messages(diags: &[Diagnostic]) -> Vec<&str> {
        diags.iter().map(|d| d.message.as_str()).collect()
    }

    #[test]
    fn missing_one_field_emits_s010_on_fact_id() {
        let src = "fact c1 a Clinic\n\nfact visit a Appointment\n  notes \"x\"\n  vets \"a\", \"b\"\n";
        let diags = s010(src, CLINIC);
        assert_eq!(
            messages(&diags),
            ["missing required field `clinic` in fact `visit` (type `Appointment`)"]
        );
        let span = diags[0].span.as_ref().expect("span");
        assert_eq!(&src[span.start.offset..span.end.offset], "visit");
    }

    #[test]
    fn some_and_at_least_fields_are_required() {
        let src = "fact c1 a Clinic\n\nfact visit a Appointment\n  clinic c1\n";
        let diags = s010(src, CLINIC);
        assert_eq!(messages(&diags).len(), 2, "{diags:?}");
        assert!(diags[0].message.contains("`notes`") && diags[1].message.contains("`vets`"));
    }

    #[test]
    fn satisfied_fields_no_s010() {
        let src = "fact c1 a Clinic\n\nfact visit a Appointment\n  clinic c1\n  notes \"x\"\n  vets \"a\", \"b\"\n";
        assert!(s010(src, CLINIC).is_empty(), "{:?}", s010(src, CLINIC));
    }

    #[test]
    fn dog_without_neutered_and_inherited_name() {
        let src = "fact rex a Dog\n  toys \"ball\"\n";
        assert_eq!(
            messages(&s010(src, CLINIC)),
            [
                "missing required field `name` in fact `rex` (type `Dog`)",
                "missing required field `neutered` in fact `rex` (type `Dog`)",
            ]
        );
        let ok = "fact rex a Dog\n  name \"Rex\"\n  neutered true\n";
        assert!(s010(ok, CLINIC).is_empty(), "{:?}", s010(ok, CLINIC));
    }

    #[test]
    fn optional_any_and_bare_fields_not_required() {
        // nickname (optional), tags (any), toys (no cardinality = any).
        let src = "fact tom a Animal\n  name \"Tom\"\n";
        assert!(s010(src, CLINIC).is_empty(), "{:?}", s010(src, CLINIC));
    }

    #[test]
    fn several_types_each_contribute_and_share_a_field() {
        let src = "fact c1 a Clinic\n\nfact v a Appointment, Booking\n  notes \"x\"\n  vets \"a\", \"b\"\n";
        assert_eq!(
            messages(&s010(src, CLINIC)),
            [
                "missing required field `clinic` in fact `v` (type `Appointment`)",
                "missing required field `paid` in fact `v` (type `Booking`)",
            ]
        );
    }

    #[test]
    fn nested_block_and_inverse_do_not_satisfy_the_fact() {
        let src = "\
fact c1 a Clinic
fact b a Booking
  paid true
  meta [
    clinic c1
  ]
fact b2 a Booking
  paid true
  is clinic of c1
";
        let diags = s010(src, CLINIC);
        assert_eq!(diags.len(), 2, "{diags:?}");
        assert!(diags.iter().all(|d| d.message.contains("`clinic`")));
    }

    #[test]
    fn qualified_property_satisfies_field() {
        let src = "fact c1 a Clinic\nfact b a Booking\n  b.paid true\n  b.clinic c1\n";
        assert!(s010(src, CLINIC).is_empty(), "{:?}", s010(src, CLINIC));
    }

    #[test]
    fn unresolved_type_gets_no_s010() {
        let src = "fact x a Ghost\n";
        assert!(s010(src, CLINIC).is_empty());
    }

    #[test]
    fn subtype_cannot_relax_inherited_one() {
        // Restrictions intersect down the hierarchy (clarification.md).
        let src = "concept Puppy:\n  sub Dog\n  has neutered: optional boolean\n\nfact p a Puppy\n  name \"P\"\n";
        assert_eq!(messages(&s010(src, CLINIC)).len(), 1);
    }
}
