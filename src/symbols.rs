//! Symbol table built from a parsed `OntologyFile`.

use std::collections::HashMap;

use rowl::{
    ConceptDef, Declaration, OntologyFile, PrefixDecl, PropertyDef, RuleDef,
    error::Span,
};

/// What kind of entity a symbol represents.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SymbolKind {
    Concept,
    Property,
    Rule,
    Prefix,
    /// A named individual declared in a concept's 'one of:' block.
    Individual { parent: String },
}

/// A resolved symbol with its definition site.
#[derive(Debug, Clone)]
pub struct Symbol {
    /// The canonical name as written in source.
    pub name: String,
    pub kind: SymbolKind,
    /// Where in the source this symbol was *defined*.
    pub definition_span: Option<Span>,
    /// Human-readable description for hover display.
    pub detail: String,
}

/// A flat table of all symbols visible within a single ontology file.
#[derive(Debug, Default)]
pub struct SymbolTable {
    symbols: HashMap<String, Symbol>,
}

impl SymbolTable {
    /// Build a symbol table from a parsed ontology file.
    pub fn build(file: &OntologyFile) -> Self {
        let mut table = SymbolTable::default();

        for prefix in &file.prefixes {
            table.insert_prefix(prefix);
        }

        for decl in &file.declarations {
            match decl {
                Declaration::Concept(c) => table.insert_concept(c),
                Declaration::Property(p) => table.insert_property(p),
                Declaration::Rule(r) => table.insert_rule(r),
            }
        }

        table
    }

    fn insert_prefix(&mut self, prefix: &PrefixDecl) {
        let name = prefix.alias.clone();
        self.symbols.insert(
            name.clone(),
            Symbol {
                name: name.clone(),
                kind: SymbolKind::Prefix,
                definition_span: prefix.span,
                detail: format!("prefix {} → {}", prefix.alias, prefix.path),
            },
        );
    }

    fn insert_concept(&mut self, c: &ConceptDef) {
        let parents: Vec<String> = c.parents.iter().map(|p| p.to_string()).collect();
        let detail = if parents.is_empty() {
            format!("concept {}", c.name)
        } else {
            format!("concept {} sub {}", c.name, parents.join(", "))
        };
        self.symbols.insert(
            c.name.clone(),
            Symbol {
                name: c.name.clone(),
                kind: SymbolKind::Concept,
                definition_span: c.span,
                detail,
            },
        );
        if let Some(variants) = &c.one_of {
            for variant in variants {
                self.symbols.insert(
                    variant.name.clone(),
                    Symbol {
                        name: variant.name.clone(),
                        kind: SymbolKind::Individual { parent: c.name.clone() },
                        definition_span: variant.span,
                        detail: format!("individual {} of {}", variant.name, c.name),
                    },
                );
            }
        }
    }

    fn insert_property(&mut self, p: &PropertyDef) {
        let detail = format!("property {}: {} → {}", p.name, p.domain, p.range);
        self.symbols.insert(
            p.name.clone(),
            Symbol {
                name: p.name.clone(),
                kind: SymbolKind::Property,
                definition_span: p.span,
                detail,
            },
        );
    }

    fn insert_rule(&mut self, r: &RuleDef) {
        self.symbols.insert(
            r.name.clone(),
            Symbol {
                name: r.name.clone(),
                kind: SymbolKind::Rule,
                definition_span: r.span,
                detail: format!("rule {}", r.name),
            },
        );
    }

    /// Look up a symbol by its source name.
    pub fn get(&self, name: &str) -> Option<&Symbol> {
        self.symbols.get(name)
    }

    /// Iterate over all symbols.
    pub fn iter(&self) -> impl Iterator<Item = &Symbol> {
        self.symbols.values()
    }

    /// All type names (concepts) defined in this file.
    pub fn type_names(&self) -> Vec<&str> {
        self.symbols
            .values()
            .filter(|s| s.kind == SymbolKind::Concept)
            .map(|s| s.name.as_str())
            .collect()
    }

    /// Returns true if the given name resolves to a declared type.
    pub fn is_declared_type(&self, name: &str) -> bool {
        matches!(
            self.symbols.get(name).map(|s| &s.kind),
            Some(SymbolKind::Concept)
        )
    }
}
