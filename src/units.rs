//! Builds a project-scoped [`dolfin_units::UnitRegistry`] from `unitdef`
//! declarations (`unitdef USD: scale 0.92 EUR`, `unitdef family vegetables`,
//! ...) found across a set of ontology files.
//!
//! `unitdef` declarations are project-wide, not per-file (matching how
//! multi-file dolfin projects already merge `concept`/`property`
//! declarations) — pass every currently-loaded [`OntologyFile`] in the
//! project, not just one.

use dolfin_units::UnitRegistry;
use rowl::{Declaration, OntologyFile, UnitDef, UnitKind};

/// Build a [`UnitRegistry`] from every `unit` declaration across `files`.
///
/// Declaration order across files doesn't matter for `family`/`nominal`
/// declarations, but a `scale <factor> <reference>` derived unit needs its
/// `reference` already resolvable. This runs repeated passes over the
/// not-yet-resolved derived units until a pass makes no further progress, so
/// declaration order (even across files) never matters. Any derived unit
/// whose reference never resolves (e.g. a typo, or a reference to another
/// never-resolving unit) is returned as an error message, one per such unit.
pub fn build_registry<'a>(files: impl IntoIterator<Item = &'a OntologyFile>) -> (UnitRegistry, Vec<String>) {
    build_registry_from_units(files.into_iter().flat_map(|file| {
        file.declarations.iter().filter_map(|decl| match decl {
            Declaration::Unit(u) => Some(u),
            _ => None,
        })
    }))
}

/// Same as [`build_registry`], from the `unitdef` declarations themselves
/// (e.g. the ones a [`crate::SymbolIndex`] collected across a package).
pub fn build_registry_from_units<'a>(units: impl IntoIterator<Item = &'a UnitDef>) -> (UnitRegistry, Vec<String>) {
    let mut registry = UnitRegistry::with_defaults();
    let mut pending: Vec<(&str, f64, &str)> = Vec::new();

    for u in units {
        match &u.kind {
            UnitKind::Family() => {
                registry.add_family(u.name.get());
            }
            UnitKind::Nominal { family, scale } => {
                registry.add_nominal(u.name.get(), &family.full(), *scale);
            }
            UnitKind::Derived { scale, reference } => {
                pending.push((u.name.get(), *scale, reference));
            }
        }
    }

    let mut errors = Vec::new();
    loop {
        let mut made_progress = false;
        let mut still_pending = Vec::new();
        for (token, scale, reference) in pending {
            match registry.add_scaled(token, scale, reference) {
                Ok(_) => made_progress = true,
                Err(_) => still_pending.push((token, scale, reference)),
            }
        }
        let stalled = still_pending.len();
        pending = still_pending;
        if pending.is_empty() {
            break;
        }
        if !made_progress {
            for (token, _, reference) in &pending {
                errors.push(format!(
                    "unit `{token}` could not be resolved: reference unit `{reference}` is unknown"
                ));
            }
            let _ = stalled;
            break;
        }
    }

    (registry, errors)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rowl::parser::parse_ontology;

    fn parse(src: &str) -> OntologyFile {
        parse_ontology(src).ontology.expect("parse failed")
    }

    #[test]
    fn builds_currency_and_nominal_units_from_declarations() {
        let file = parse(
            "unitdef USD: scale 0.92 EUR\n\
             unitdef family vegetables\n\
             unitdef bunch_of_carrots: nominal of vegetables scale 2\n\
             unitdef cabbages: nominal of vegetables scale 1\n",
        );
        let (registry, errors) = build_registry([&file]);
        assert!(errors.is_empty(), "unexpected errors: {errors:?}");

        let q = dolfin_units::parse_quantity_with("100 USD", &registry).unwrap();
        assert!((q.si_value() - 92.0).abs() < 1e-9);

        let widened = dolfin_units::parse_quantity_with(
            "2 bunch_of_carrots + 3 cabbages as vegetables",
            &registry,
        )
        .unwrap();
        assert!((widened.qty - 7.0).abs() < 1e-9);
    }

    #[test]
    fn declaration_order_across_files_does_not_matter() {
        // `GBP` derived from `USD`, declared *before* `USD` exists.
        let a = parse("unitdef GBP: scale 1.08 USD\n");
        let b = parse("unitdef USD: scale 0.92 EUR\n");
        let (registry, errors) = build_registry([&a, &b]);
        assert!(errors.is_empty(), "unexpected errors: {errors:?}");
        let q = dolfin_units::parse_quantity_with("1 GBP", &registry).unwrap();
        assert!((q.si_value() - 1.08 * 0.92).abs() < 1e-9);
    }

    #[test]
    fn unresolvable_reference_is_reported() {
        let file = parse("unitdef XYZ: scale 2 NOSUCHUNIT\n");
        let (_registry, errors) = build_registry([&file]);
        assert_eq!(errors.len(), 1);
        assert!(errors[0].contains("XYZ"));
    }
}
