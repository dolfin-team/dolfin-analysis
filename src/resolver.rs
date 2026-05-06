//! Type resolution pass: walks the AST and emits diagnostics for any
//! `TypeRef::Named` references that do not resolve to a symbol.

use rowl::{
    Declaration, HasDeclaration, OntologyFile, TypeRef,
    error::Span,
};

use crate::{
    diagnostics::{Diagnostic, DiagnosticCode},
    symbols::SymbolTable,
};

/// Run the resolution pass and return all unresolved-type diagnostics.
pub fn resolve(file: &OntologyFile, table: &SymbolTable) -> Vec<Diagnostic> {
    let mut diags = Vec::new();

    // Check for duplicate declaration names.
    let mut seen: std::collections::HashMap<&str, Option<Span>> = std::collections::HashMap::new();
    for decl in &file.declarations {
        let (name, span) = decl_name_span(decl);
        if let Some(prev_span) = seen.get(name) {
            diags.push(Diagnostic::error(
                DiagnosticCode::DuplicateDeclaration,
                format!("duplicate declaration `{name}`"),
                *prev_span,
            ));
        } else {
            seen.insert(name, span);
        }
    }

    // Check type references.
    for decl in &file.declarations {
        match decl {
            Declaration::Concept(c) => {
                for parent in &c.parents {
                    check_type_ref(parent, table, &mut diags);
                }
                for has in &c.has_declarations {
                    check_has(has, table, &mut diags);
                }
            }
            Declaration::Property(p) => {
                check_type_ref(&p.domain, table, &mut diags);
                check_type_ref(&p.range, table, &mut diags);
            }
            Declaration::Rule(_) => {}
        }
    }

    // Circular inheritance check.
    check_circular_inheritance(file, table, &mut diags);

    diags
}

fn decl_name_span(decl: &Declaration) -> (&str, Option<Span>) {
    match decl {
        Declaration::Concept(c) => (&c.name, c.span),
        Declaration::Property(p) => (&p.name, p.span),
        Declaration::Rule(r) => (&r.name, r.span),
    }
}

fn check_has(has: &HasDeclaration, table: &SymbolTable, diags: &mut Vec<Diagnostic>) {
    check_type_ref(&has.type_ref, table, diags);
}

fn check_type_ref(type_ref: &TypeRef, table: &SymbolTable, diags: &mut Vec<Diagnostic>) {
    if let TypeRef::Named { name, span } = type_ref {
        let full = name.full();
        let last = name.last();
        // Accept primitives-by-name defensively, then try last segment first
        // (unqualified reference) then the full qualified name.
        if !table.is_declared_type(&last) && !table.is_declared_type(&full) {
            diags.push(Diagnostic::error(
                DiagnosticCode::UnresolvedType,
                format!("type `{full}` is not declared"),
                *span,
            ));
        }
    }
    // Primitive refs are always valid.
}

fn check_circular_inheritance(
    file: &OntologyFile,
    _table: &SymbolTable,
    diags: &mut Vec<Diagnostic>,
) {
    use std::collections::{HashMap, HashSet};

    // Build adjacency: concept -> its direct parent names.
    let mut parents: HashMap<&str, Vec<String>> = HashMap::new();
    for decl in &file.declarations {
        if let Declaration::Concept(c) = decl {
            let ps: Vec<String> = c
                .parents
                .iter()
                .filter_map(|p| match p {
                    TypeRef::Named { name, .. } => Some(name.last()),
                    _ => None,
                })
                .collect();
            parents.insert(&c.name, ps);
        }
    }

    for start in parents.keys().copied() {
        let mut visited = HashSet::new();
        let mut stack = vec![start];
        while let Some(node) = stack.pop() {
            if !visited.insert(node) {
                // Already visited -> cycle detected.
                if node == start {
                    // Find the definition span for the starting concept.
                    let span = file.declarations.iter().find_map(|d| {
                        if let Declaration::Concept(c) = d {
                            if c.name == start { c.span } else { None }
                        } else {
                            None
                        }
                    });
                    diags.push(Diagnostic::error(
                        DiagnosticCode::CircularInheritance,
                        format!("concept `{start}` has circular inheritance"),
                        span,
                    ));
                }
                break;
            }
            if let Some(ps) = parents.get(node) {
                for p in ps {
                    stack.push(p.as_str());
                }
            }
        }
    }
}
