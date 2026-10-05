//! The tutorial's shared code fragments (docs/src/language/code/*.dlf) must stay valid
//! Dolfin: they are `{{#include}}`d verbatim into the mdBook chapters, so a
//! parse/analysis regression here would ship broken code in the docs. Each test
//! assembles the fragments the way a chapter's "story so far" composes them.

use dolfin_analysis::{analyze, Severity};
use rowl::parser::parse_ontology;

const SCHEMA: &str = include_str!("../../docs/src/language/code/clinic-schema.dlf");
const INFERENCE: &str = include_str!("../../docs/src/language/code/rules-inference.dlf");
const WEIGHT: &str = include_str!("../../docs/src/language/code/rules-weight.dlf");
const FACTS: &str = include_str!("../../docs/src/language/code/facts-weight.dlf");
const GUARD: &str = include_str!("../../docs/src/language/code/rules-guard.dlf");

// Chapters 13/epilogue prefix the model with these; they must not break parsing.
const PREFIXES: &str = "\
prefix <http://naho.gov/ontology/> as naho
prefix <http://fao.org/species/> as fao
prefix <http://schema.org/> as schema
";

/// Parse + analyze the concatenation; assert no parse errors and no
/// **error-severity** analysis diagnostics. Catching every error (not just
/// invalid quantities) is what guards against cross-fragment breakage — a rule
/// referencing a concept/property that a schema edit renamed or dropped shows up
/// as an unknown-reference error, which is precisely the propagation risk the
/// externalized fragments are meant to prevent. (The `package` block lives in
/// package.dlf and is rejected by the ontology-file parser, so it is excluded.)
fn check(label: &str, parts: &[&str]) {
    let src = parts.join("\n\n");
    let parsed = parse_ontology(&src);
    let parse_errs: Vec<_> = parsed
        .diagnostics
        .iter()
        .filter(|d| d.severity == rowl::error::Severity::HardError)
        .map(|d| format!("{:?}: {}", d.code, d.message))
        .collect();
    assert!(parse_errs.is_empty(), "[{label}] parse errors: {parse_errs:#?}");
    let file = parsed.ontology.expect("no ontology");
    let errs: Vec<_> = analyze(file)
        .diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .map(|d| format!("{:?}: {}", d.code, d.message))
        .collect();
    assert!(errs.is_empty(), "[{label}] analysis errors: {errs:#?}");
}

#[test]
fn ch11_a_matter_of_weight() {
    check("ch11 story-so-far", &[SCHEMA, INFERENCE, WEIGHT]);
    check("ch11 worked example", &[SCHEMA, INFERENCE, WEIGHT, FACTS]);
}

#[test]
fn ch12_guard_rails() {
    check("ch12 story-so-far", &[SCHEMA, INFERENCE, WEIGHT, GUARD]);
}

#[test]
fn ch13_and_epilogue() {
    check("ch13/epilogue story-so-far", &[PREFIXES, SCHEMA, INFERENCE, WEIGHT, GUARD]);
}
