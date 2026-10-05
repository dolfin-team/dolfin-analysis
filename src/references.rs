//! Find all references to a named symbol within an ontology file.
//!
//! Given a target name (simple like `"Far"` or qualified like `"there.Far"`),
//! this module walks every place a name can appear as a type reference and
//! collects the source spans.

use rowl::{
    Declaration, OntologyFile,
    ast::{
        AggregationQuery, Constraint, ConstraintBlock, DisjBranch, ExistenceBlock, FactAssertion,
        FactDef, FactValue, HasDeclaration, InverseTriple, Object, Pattern, PropertyPattern,
        QueryClause, QueryComposition, QueryDef, RuleDef, SubjectBlock, SubjectPattern, ThenBlock,
        ThenItem, TypeRef,
    },
    error::Span,
};

/// Return every span in `file` where `target` is referenced by name.
///
/// `target` may be a simple name (`"Far"`) or a qualified name (`"there.Far"`).
/// A [`TypeRef::Named`] matches when either its `full()` or its `last()` part
/// equals `target`.
pub fn find_references_in_file(file: &OntologyFile, target: &str) -> Vec<Span> {
    let mut out = Vec::new();
    for decl in &file.declarations {
        match decl {
            Declaration::Concept(c) => {
                for parent in &c.parents {
                    collect_type_ref(parent, target, &mut out);
                }
                for has in &c.has_declarations {
                    collect_has(has, target, &mut out);
                }
            }
            Declaration::Property(p) => {
                collect_type_ref(&p.domain, target, &mut out);
                collect_type_ref(&p.range, target, &mut out);
            }
            Declaration::Rule(r) => {
                collect_rule(r, target, &mut out);
            }
            Declaration::Query(q) => {
                collect_query(q, target, &mut out);
            }
            Declaration::Fact(f) => collect_fact(f, target, &mut out),
            Declaration::Unit(_) => {}
        }
    }
    out
}

// ── Helpers ───────────────────────────────────────────────────────────────────

fn collect_fact(f: &FactDef, target: &str, out: &mut Vec<Span>) {
    for type_qn in &f.types {
        if name_matches(type_qn, target)
            && let Some(s) = type_qn.span {
                out.push(s);
            }
    }
    for assertion in &f.assertions {
        collect_fact_assertion(assertion, target, out);
    }
}

fn collect_fact_assertion(assertion: &FactAssertion, target: &str, out: &mut Vec<Span>) {
    match assertion {
        FactAssertion::Property { property, values, .. } => {
            if name_matches(property, target)
                && let Some(s) = property.span {
                    out.push(s);
                }
            for v in values {
                collect_fact_value(v, target, out);
            }
        }
        FactAssertion::Inverse { property, value, .. } => {
            if name_matches(property, target)
                && let Some(s) = property.span {
                    out.push(s);
                }
            collect_fact_value(value, target, out);
        }
        FactAssertion::TypeHint { type_ref, .. } => {
            if name_matches(type_ref, target)
                && let Some(s) = type_ref.span {
                    out.push(s);
                }
        }
    }
}

fn collect_fact_value(value: &FactValue, target: &str, out: &mut Vec<Span>) {
    match value {
        // `:Name` is the package namespace, which declares nothing.
        FactValue::Reference { qualifier: None, .. } => {}
        FactValue::Reference { name, span, .. } => {
            if name == target
                && let Some(s) = span {
                    out.push(*s);
                }
        }
        FactValue::Named { name, .. } => {
            if name_matches(name, target)
                && let Some(s) = name.span {
                    out.push(s);
                }
        }
        FactValue::Block { assertions, .. } => {
            for a in assertions {
                collect_fact_assertion(a, target, out);
            }
        }
        FactValue::Literal { .. } => {}
    }
}

fn name_matches(name: &rowl::ast::QualifiedName, target: &str) -> bool {
    name.full() == target || name.last() == target
}

fn collect_type_ref(tr: &TypeRef, target: &str, out: &mut Vec<Span>) {
    match tr {
        TypeRef::Named { name, span } => {
            if name_matches(name, target)
                && let Some(s) = span {
                    out.push(*s);
                }
        }
        TypeRef::Union { members, .. } => {
            for m in members {
                collect_type_ref(m, target, out);
            }
        }
        TypeRef::Primitive { .. } => {}
    }
}

fn collect_has(has: &HasDeclaration, target: &str, out: &mut Vec<Span>) {
    collect_type_ref(&has.type_ref, target, out);
}

fn collect_rule(r: &RuleDef, target: &str, out: &mut Vec<Span>) {
    for pattern in &r.match_block.patterns {
        collect_pattern(pattern, target, out);
    }
    collect_then(&r.then_block, target, out);
}

fn collect_pattern(p: &Pattern, target: &str, out: &mut Vec<Span>) {
    match p {
        Pattern::Type { type_ref, .. } => {
            collect_type_ref(type_ref, target, out);
        }
        Pattern::Quantified { patterns, constraint, .. } => {
            for inner in patterns {
                collect_pattern(inner, target, out);
            }
            if let Some(cb) = constraint {
                collect_constraint_block(cb, target, out);
            }
        }
        Pattern::Triple { property, object, .. } => {
            if name_matches(property, target)
                && let Some(s) = property.span {
                    out.push(s);
                }
            collect_object(object, target, out);
        }
        Pattern::QueryCall { name, args: _, .. } => {
            if name_matches(name, target)
                && let Some(s) = name.span {
                    out.push(s);
                }
        }
        Pattern::Inverse { property, object, .. } => {
            if name_matches(property, target)
                && let Some(s) = property.span {
                    out.push(s);
                }
            collect_object(object, target, out);
        }
    }
}

fn collect_constraint_block(cb: &ConstraintBlock, target: &str, out: &mut Vec<Span>) {
    for c in &cb.constraints {
        match c {
            Constraint::TypeIs { type_ref, .. } => {
                collect_type_ref(type_ref, target, out);
            }
            Constraint::PropertyValue { property, value, .. } => {
                if name_matches(property, target)
                    && let Some(s) = property.span {
                        out.push(s);
                    }
                collect_object(value, target, out);
            }
            Constraint::PropertyConstraint { property, block, .. } => {
                if name_matches(property, target)
                    && let Some(s) = property.span {
                        out.push(s);
                    }
                collect_constraint_block(block, target, out);
            }
            Constraint::Comparison { .. } => {}
            Constraint::Inverse { property, value, .. } => {
                if name_matches(property, target)
                    && let Some(s) = property.span {
                        out.push(s);
                    }
                collect_object(value, target, out);
            }
            Constraint::InverseNested { property, block, .. } => {
                if name_matches(property, target)
                    && let Some(s) = property.span {
                        out.push(s);
                    }
                collect_constraint_block(block, target, out);
            }
        }
    }
}

fn collect_query(q: &QueryDef, target: &str, out: &mut Vec<Span>) {
    collect_query_clauses(&q.body.clauses, target, out);
}

fn collect_query_clauses(clauses: &[QueryClause], target: &str, out: &mut Vec<Span>) {
    for clause in clauses {
        match clause {
            QueryClause::Composition(qc) => collect_composition(qc, target, out),
            QueryClause::SubjectPattern(sp) => collect_subject_pattern(sp, target, out),
            QueryClause::ExistenceBlock(eb) => collect_existence_block(eb, target, out),
            QueryClause::InverseTriple(it) => collect_inverse_triple(it, target, out),
            QueryClause::AggregationQuery(aq) => collect_aggregation(aq, target, out),
            // Boolean filters compare variables and literals — no named symbols.
            QueryClause::BooleanFilter(_) => {}
        }
    }
}

fn collect_subject_pattern(sp: &SubjectPattern, target: &str, out: &mut Vec<Span>) {
    if let Some(tr) = &sp.type_ref {
        collect_type_ref(tr, target, out);
    }
    for pp in &sp.properties {
        collect_property_pattern(pp, target, out);
    }
}

fn collect_subject_block(sb: &SubjectBlock, target: &str, out: &mut Vec<Span>) {
    for pp in &sb.properties {
        collect_property_pattern(pp, target, out);
    }
}

fn collect_existence_block(eb: &ExistenceBlock, target: &str, out: &mut Vec<Span>) {
    collect_query_clauses(&eb.clauses, target, out);
}

fn collect_aggregation(aq: &AggregationQuery, target: &str, out: &mut Vec<Span>) {
    collect_query_clauses(&aq.sub_clauses, target, out);
}

fn collect_inverse_triple(it: &InverseTriple, target: &str, out: &mut Vec<Span>) {
    if name_matches(&it.property, target)
        && let Some(s) = it.property.span {
            out.push(s);
        }
    collect_object(&it.object, target, out);
}

fn collect_property_pattern(pp: &PropertyPattern, target: &str, out: &mut Vec<Span>) {
    let push_property = |property: &rowl::ast::QualifiedName, out: &mut Vec<Span>| {
        if name_matches(property, target)
            && let Some(s) = property.span {
                out.push(s);
            }
    };
    match pp {
        PropertyPattern::Value { property, object, .. }
        | PropertyPattern::Optional { property, object, .. } => {
            push_property(property, out);
            collect_object(object, target, out);
        }
        PropertyPattern::Constrained { property, block, .. }
        | PropertyPattern::InverseNested { property, block, .. } => {
            push_property(property, out);
            collect_constraint_block(block, target, out);
        }
        PropertyPattern::Inverse { property, .. } => push_property(property, out),
        PropertyPattern::Nested { property, block, .. } => {
            push_property(property, out);
            collect_subject_block(block, target, out);
        }
        PropertyPattern::Disjunction { either_branch, or_branches, .. } => {
            collect_disj_branch(either_branch, target, out);
            for b in or_branches {
                collect_disj_branch(b, target, out);
            }
        }
    }
}

fn collect_disj_branch(b: &DisjBranch, target: &str, out: &mut Vec<Span>) {
    if name_matches(&b.property, target)
        && let Some(s) = b.property.span {
            out.push(s);
        }
    collect_constraint_block(&b.block, target, out);
}

/// An object position can hold a nested constraint block *or* a named constant
/// (`status OVERDUE`) — the latter is how `one of:` individuals are referenced.
fn collect_object(o: &Object, target: &str, out: &mut Vec<Span>) {
    match o {
        Object::Constraint { block } => collect_constraint_block(block, target, out),
        Object::Constant { value, span } => {
            if name_matches(value, target)
                && let Some(s) = value.span.or(*span) {
                    out.push(s);
                }
        }
        Object::Variable { .. } | Object::Literal { .. } => {}
    }
}

fn collect_composition(qc: &QueryComposition, target: &str, out: &mut Vec<Span>) {
    if name_matches(&qc.query_name, target)
        && let Some(s) = qc.span {
            out.push(s);
        }
}

fn collect_then(then: &ThenBlock, target: &str, out: &mut Vec<Span>) {
    for item in &then.items {
        match item {
            ThenItem::AssertionTyping { typing, span, .. } => {
                if name_matches(typing, target)
                    && let Some(s) = span {
                        out.push(*s);
                    }
            }
            ThenItem::NestedRule { rule } => {
                collect_rule(rule, target, out);
            }
            ThenItem::AssertionTriple { assertion, .. } => {
                if name_matches(&assertion.property, target)
                    && let Some(s) = assertion.property.span {
                        out.push(s);
                    }
                collect_object(&assertion.object, target, out);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rowl::parser::parse_ontology;

    fn parse(src: &str) -> OntologyFile {
        let result = parse_ontology(src);
        result.ontology.expect("parse failed")
    }

    #[test]
    fn finds_property_in_rule_match_triple() {
        // Triple pattern: ?subject property_name ?object  (no colon after property)
        let src = "concept Animal\nproperty has_owner: Animal -> Animal\nrule owns:\n  match:\n    ?x has_owner ?y\n  then:\n    ?x has_owner ?y\n";
        let file = parse(src);
        let refs = find_references_in_file(&file, "has_owner");
        // Two references: one in match triple, one in then assertion triple
        assert_eq!(
            refs.len(),
            2,
            "expected 2 refs to has_owner in rule, got {}: {:?}",
            refs.len(),
            refs
        );
    }

    #[test]
    fn finds_property_in_rule_then_triple() {
        let src = "concept Animal\nproperty has_owner: Animal -> Animal\nrule set_owner:\n  match:\n    ?x a Animal\n  then:\n    ?x has_owner ?x\n";
        let file = parse(src);
        let refs = find_references_in_file(&file, "has_owner");
        assert!(
            !refs.is_empty(),
            "expected at least one ref to has_owner in then block"
        );
    }

    #[test]
    fn does_not_match_other_properties() {
        let src = "concept Animal\nproperty has_owner: Animal -> Animal\nproperty has_age: Animal -> string\nrule test_rule:\n  match:\n    ?x has_age ?y\n  then:\n    ?x has_age ?y\n";
        let file = parse(src);
        let refs = find_references_in_file(&file, "has_owner");
        assert!(
            refs.is_empty(),
            "should not find has_owner refs in a rule using has_age"
        );
    }
}
