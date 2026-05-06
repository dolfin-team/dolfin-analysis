//! Find all references to a named symbol within an ontology file.
//!
//! Given a target name (simple like `"Far"` or qualified like `"there.Far"`),
//! this module walks every place a name can appear as a type reference and
//! collects the source spans.

use rowl::{
    Declaration, OntologyFile,
    ast::{
        HasDeclaration, Pattern, RuleDef, ThenBlock, ThenItem, TypeRef,
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
        }
    }
    out
}

// ── Helpers ───────────────────────────────────────────────────────────────────

fn name_matches(name: &rowl::ast::QualifiedName, target: &str) -> bool {
    name.full() == target || name.last() == target
}

fn collect_type_ref(tr: &TypeRef, target: &str, out: &mut Vec<Span>) {
    if let TypeRef::Named { name, span } = tr {
        if name_matches(name, target) {
            if let Some(s) = span {
                out.push(*s);
            }
        }
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
        Pattern::Quantified { patterns, .. } => {
            for inner in patterns {
                collect_pattern(inner, target, out);
            }
        }
        Pattern::Triple { property, .. } => {
            if name_matches(property, target) {
                if let Some(s) = property.span {
                    out.push(s);
                }
            }
        }
    }
}

fn collect_then(then: &ThenBlock, target: &str, out: &mut Vec<Span>) {
    for item in &then.items {
        match item {
            ThenItem::AssertionTyping { typing, span, .. } => {
                if name_matches(typing, target) {
                    if let Some(s) = span {
                        out.push(*s);
                    }
                }
            }
            ThenItem::NestedRule { rule } => {
                collect_rule(rule, target, out);
            }
            ThenItem::AssertionTriple { assertion, .. } => {
                if name_matches(&assertion.property, target) {
                    if let Some(s) = assertion.property.span {
                        out.push(s);
                    }
                }
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
        assert_eq!(refs.len(), 2, "expected 2 refs to has_owner in rule, got {}: {:?}", refs.len(), refs);
    }

    #[test]
    fn finds_property_in_rule_then_triple() {
        let src = "concept Animal\nproperty has_owner: Animal -> Animal\nrule set_owner:\n  match:\n    ?x a Animal\n  then:\n    ?x has_owner ?x\n";
        let file = parse(src);
        let refs = find_references_in_file(&file, "has_owner");
        assert!(!refs.is_empty(), "expected at least one ref to has_owner in then block");
    }

    #[test]
    fn does_not_match_other_properties() {
        let src = "concept Animal\nproperty has_owner: Animal -> Animal\nproperty has_age: Animal -> string\nrule test_rule:\n  match:\n    ?x has_age ?y\n  then:\n    ?x has_age ?y\n";
        let file = parse(src);
        let refs = find_references_in_file(&file, "has_owner");
        assert!(refs.is_empty(), "should not find has_owner refs in a rule using has_age");
    }
}
