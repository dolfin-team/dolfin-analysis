# dolfin-analysis

Semantic analysis for the [Dolfin](https://github.com/dolfin-team) ontology language.

This crate takes a parsed `OntologyFile` from the `rowl` parser and produces a
symbol index, resolved type references, and diagnostics — the core of any
Dolfin language tool (language server, linter, IDE plugin).

## Architecture

```
rowl::parse_ontology(source)
        │
        ▼
SymbolIndex::from_file(file)   ← all declared symbols
        │
        ▼
resolve::resolve_file(file, &index)   ← every TypeRef resolved or flagged
        │
        ├─▶ validate::validate(...)   ← structural errors (S001–S003)
        │
        └─▶ types::check_types(...)   ← type-level errors (S004–S006)
```

## Quick start

```rust
use rowl::parser::parse_ontology;
use dolfin_analysis::analyze;

let result = parse_ontology("concept Person:\n  has name: string\n");
if let Some(file) = result.ontology {
    let analysis = analyze(file);
    for diag in &analysis.diagnostics {
        eprintln!("[{}] {}", diag.code.code_str(), diag.message);
    }
}
```

### Workspace-aware analysis

For multi-file workspaces, build a shared `SymbolIndex` across all files so
cross-file references resolve correctly:

```rust
use dolfin_analysis::{SymbolIndex, analyze_with_index};
use rowl::parser::parse_ontology;

let mut index = SymbolIndex::default();

// Add every file in the workspace.
for (path, source) in workspace_files {
    if let Some(file) = parse_ontology(&source).ontology {
        index.add_file(&path, &file);
    }
}

// Analyse one file against the shared index.
if let Some(file) = parse_ontology(&target_source).ontology {
    let analysis = analyze_with_index(file, index);
}
```

The index supports incremental updates: call `add_file` again with the same
path to re-index after an edit, or `remove_file` when a file is deleted.

## Diagnostics

| Code | Category  | Description                                      |
|------|-----------|--------------------------------------------------|
| S001 | Structural | Unresolved type reference                        |
| S002 | Structural | Duplicate declaration within the same file       |
| S003 | Structural | Circular inheritance (`concept A sub A`)         |
| S004 | Type       | `sub` parent is not a concept                    |
| S005 | Type       | Property domain is not a concept                 |
| S006 | Type       | Cardinality range has `min > max`                |

## Modules

| Module        | Purpose                                                     |
|---------------|-------------------------------------------------------------|
| `index`       | Multi-file `SymbolIndex` with incremental add/remove        |
| `resolve`     | Resolves every `TypeRef` to a known symbol or flags it      |
| `validate`    | Structural checks (S001–S003)                               |
| `types`       | Type-level checks (S004–S006)                               |
| `references`  | Finds all in-file spans that reference a given symbol name  |
| `diagnostics` | Re-exports `Diagnostic`, `DiagnosticCode`, `Severity`       |

## License

MIT — see [LICENSE](LICENSE).
