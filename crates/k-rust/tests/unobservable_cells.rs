//! The `unobservable` cell property and the configuration reader `declared_cells`
//! (`docs/compatibility.md`, "Unobservable cells").
//!
//! The property states that a cell holds state no use of the definition may observe. It changes
//! nothing the definition computes, so the compiled KORE of a definition that writes it is the
//! KORE of the same definition without it, up to the source locations the shifted text moves.
//! `declared_cells` reads what the configuration declares about each cell, with the KORE names
//! compilation gives the cell's symbol and sorts, so a tool can find a cell in a compiled
//! definition's configurations.

use std::collections::BTreeMap;

use k_rust::builtin::embedded;
use k_rust::definition::{
    CellMultiplicity, DeclaredCell, ResolvedDefinition, check_definition, declared_cells,
};
use k_rust::kompile::{CompilationBackend, CompileOptions, compile_loaded_definition};
use k_rust::kore::ast::{Sentence as KoreSentence, Sort as KoreSort};
use k_rust::kore::parser::parse_definition;
use k_rust::outer::{LoadOptions, LoadedDefinition, ResolvedSource, load_with_options};

/// Nested cells, an optional cell, a `Map` collection cell, and two unobservable cells (one at a
/// fixed position, one inside the collection's elements).
const MARKED: &str = r#"module CELLS
  imports INT
  imports MAP

  configuration <k> $PGM:K </k>
                <regs>
                  <w unobservable=""> 0 </w>
                  <z> 0 </z>
                </regs>
                <opt multiplicity="?"> 0 </opt>
                <threads>
                  <thread multiplicity="*" type="Map">
                    <id> 0 </id>
                    <scratch unobservable=""> 0 </scratch>
                  </thread>
                </threads>

  syntax KItem ::= "bump" [symbol(bump)]
  rule <k> bump => .K ... </k> <w> W => W +Int 1 </w> <z> Z => Z +Int 2 </z>
endmodule
"#;

fn load(source: &str) -> Result<LoadedDefinition, String> {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    load_with_options(
        ResolvedSource::new("cells.k", source),
        "CELLS",
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").unwrap()],
            excluded_module_attributes: vec![
                CompilationBackend::Rust.excluded_module_attribute().into(),
            ],
            ..LoadOptions::default()
        },
    )
    .map_err(|error| error.to_string())
}

fn definition_kore(loaded: &LoadedDefinition) -> String {
    compile_loaded_definition(loaded, CompileOptions::default())
        .unwrap()
        .definition_kore
}

/// `kore` with the value of every `Location` attribute removed: the positions of the sentences
/// after a cell property move when the property is removed.
fn without_locations(kore: &str) -> String {
    const LOCATION: &str = "org'Stop'kframework'Stop'attributes'Stop'Location{}(\"";
    let mut output = String::with_capacity(kore.len());
    let mut rest = kore;
    while let Some(start) = rest.find(LOCATION) {
        let value = start + LOCATION.len();
        output.push_str(&rest[..value]);
        let end = rest[value..]
            .find('"')
            .expect("a Location value is a closed string literal");
        rest = &rest[value + end..];
    }
    output.push_str(rest);
    output
}

fn cells_of(loaded: &LoadedDefinition) -> BTreeMap<String, DeclaredCell> {
    let resolved = loaded.resolved();
    declared_cells(resolved, resolved.main_module_id())
        .into_iter()
        .map(|cell| (cell.name.clone(), cell))
        .collect()
}

fn sort(name: &str) -> KoreSort {
    KoreSort::Application {
        name: name.to_owned(),
        arguments: Vec::new(),
    }
}

/// The argument and result sorts of every symbol `kore` declares.
fn symbol_signatures(kore: &str) -> BTreeMap<String, (Vec<KoreSort>, KoreSort)> {
    let definition = parse_definition(kore).unwrap();
    let mut signatures = BTreeMap::new();
    for module in definition.modules {
        for sentence in module.sentences {
            if let KoreSentence::SymbolDeclaration {
                symbol,
                argument_sorts,
                result_sort,
                ..
            } = sentence
            {
                signatures.insert(symbol.name, (argument_sorts, result_sort));
            }
        }
    }
    signatures
}

#[test]
fn an_unobservable_cell_compiles_to_the_kore_of_the_unmarked_definition() {
    let marked = load(MARKED).unwrap();
    let unmarked_source = MARKED.replace(r#" unobservable="""#, "");
    assert_ne!(unmarked_source, MARKED);
    let unmarked = load(&unmarked_source).unwrap();

    let cells = cells_of(&marked);
    assert!(cells["w"].unobservable && cells["scratch"].unobservable);
    assert!(cells_of(&unmarked).values().all(|cell| !cell.unobservable));

    let marked_kore = definition_kore(&marked);
    let unmarked_kore = definition_kore(&unmarked);
    assert!(!marked_kore.contains("unobservable"));
    assert_eq!(
        without_locations(&marked_kore),
        without_locations(&unmarked_kore)
    );
}

#[test]
fn unobservable_takes_no_value_and_is_refused_on_an_exit_or_a_stream_cell() {
    let refusals = [
        (
            r#"<k> $PGM:K </k> <w unobservable="x"> 0 </w>"#,
            r#"cell property "unobservable" does not accept a value"#,
        ),
        (
            r#"<k> $PGM:K </k> <status exit="" unobservable=""> 0 </status>"#,
            "cell <status> cannot be unobservable: its final value is the process exit status",
        ),
        (
            r#"<k> $PGM:K </k> <out stream="stdout" unobservable=""> .List </out>"#,
            "cell <out> cannot be unobservable: its content is console input or output",
        ),
        // A cell holding an exit or a stream cell holds content every run observes.
        (
            r#"<k> $PGM:K </k> <outer unobservable=""> <mid> <out stream="stdout"> .List </out> </mid> </outer>"#,
            "cell <outer> cannot be unobservable: it holds the stream cell <out>, whose content is console input or output",
        ),
        (
            r#"<k> $PGM:K </k> <outer unobservable=""> <z> 0 </z> <status exit=""> 0 </status> </outer>"#,
            "cell <outer> cannot be unobservable: it holds the exit cell <status>, whose final value is the process exit status",
        ),
        // On the declaration, the property would mark every cell it generates, the exit cell
        // and the top cell included.
        (
            r#"<k> $PGM:K </k> <status exit=""> 0 </status> [unobservable]"#,
            "`unobservable` is a cell property: write it on the cell it marks",
        ),
    ];
    for (configuration, expected) in refusals {
        let source = format!(
            "module CELLS\n  imports INT\n  imports LIST\n  configuration {configuration}\nendmodule\n"
        );
        let error = load(&source).map(|_| ()).unwrap_err();
        assert!(error.contains(expected), "{configuration}: {error}");
    }
}

#[test]
fn unobservable_is_refused_on_a_cell_holding_an_external_stream_cell() {
    // `<io/>` is the cell another configuration declaration declares, with its stream cell.
    let source = r#"module IO
  imports LIST
  configuration <io> <out stream="stdout"> .List </out> </io>
endmodule

module CELLS
  imports INT
  imports IO
  configuration <k> $PGM:K </k> <outer unobservable=""> <io/> </outer>
endmodule
"#;
    let error = load(source).map(|_| ()).unwrap_err();
    assert!(
        error.contains(
            "cell <outer> cannot be unobservable: it holds the stream cell <out>, whose content is console input or output"
        ),
        "{error}"
    );
    // The same configuration with `<outer>` observable is accepted.
    load(&source.replace(r#" unobservable="""#, "")).unwrap();
}

#[test]
fn unobservable_is_refused_on_a_production_that_declares_no_cell() {
    let source = "module CELLS\n  imports INT\n  configuration <k> $PGM:K </k>\n  syntax KItem ::= \"foo\" [unobservable]\nendmodule\n";
    let loaded = load(source).unwrap();
    let diagnostics = check_definition(loaded.resolved()).unwrap();
    assert!(
        diagnostics.iter().any(|diagnostic| diagnostic.message.starts_with(
            "The attribute 'unobservable' cannot be applied to a production that does not declare a cell"
        )),
        "{diagnostics:?}"
    );
    // A cell production carrying it declares a cell, so the check accepts it.
    let marked = load(MARKED).unwrap();
    let diagnostics = check_definition(marked.resolved()).unwrap();
    assert!(
        diagnostics
            .iter()
            .all(|diagnostic| !diagnostic.message.contains("unobservable")),
        "{diagnostics:?}"
    );
}

#[test]
fn declared_cells_name_the_symbols_and_sorts_of_the_compiled_configuration() {
    let loaded = load(MARKED).unwrap();
    let cells = cells_of(&loaded);
    let expected = [
        ("generatedTop", CellMultiplicity::One, false),
        ("k", CellMultiplicity::One, false),
        ("regs", CellMultiplicity::One, false),
        ("w", CellMultiplicity::One, true),
        ("z", CellMultiplicity::One, false),
        ("opt", CellMultiplicity::Optional, false),
        ("threads", CellMultiplicity::One, false),
        ("thread", CellMultiplicity::Star, false),
        ("id", CellMultiplicity::One, false),
        ("scratch", CellMultiplicity::One, true),
    ];
    assert_eq!(
        cells.keys().map(String::as_str).collect::<Vec<_>>(),
        {
            let mut names = expected.map(|(name, ..)| name).to_vec();
            names.sort_unstable();
            names
        },
        "the loaded definition declares exactly the configuration's cells and its top cell"
    );
    for (name, multiplicity, unobservable) in expected {
        let cell = &cells[name];
        assert_eq!(cell.multiplicity, multiplicity, "<{name}>");
        assert_eq!(cell.unobservable, unobservable, "<{name}>");
    }
    assert_eq!(cells["w"].kore_symbol, "Lbl'-LT-'w'-GT-'");
    assert_eq!(cells["w"].position_kore_sort, sort("SortWCell"));
    assert_eq!(cells["opt"].position_kore_sort, sort("SortOptCell"));
    assert_eq!(
        cells["thread"].position_kore_sort,
        sort("SortThreadCellMap")
    );
    assert_eq!(
        cells["regs"].child_kore_sorts,
        [sort("SortWCell"), sort("SortZCell")]
    );
    assert_eq!(
        cells["threads"].child_kore_sorts,
        [sort("SortThreadCellMap")]
    );
    assert_eq!(
        cells["thread"].child_kore_sorts,
        [sort("SortIdCell"), sort("SortScratchCell")]
    );
    // The top cell holds each top-level cell once, at the argument of its position sort.
    assert_eq!(
        cells["generatedTop"].child_kore_sorts,
        ["k", "regs", "opt", "threads"].map(|name| cells[name].position_kore_sort.clone())
    );

    let compiled = compile_loaded_definition(&loaded, CompileOptions::default()).unwrap();
    let signatures = symbol_signatures(&compiled.definition_kore);
    let assert_declared = |cell: &DeclaredCell, arguments: &[KoreSort]| {
        let (declared, result) = signatures
            .get(&cell.kore_symbol)
            .unwrap_or_else(|| panic!("{} is declared", cell.kore_symbol));
        assert_eq!(declared, arguments, "<{}>", cell.name);
        // A cell's application is of its cell sort; only a `*` cell sits in its parent inside
        // the collection that holds its instances.
        assert_eq!(
            result == &cell.position_kore_sort,
            cell.multiplicity != CellMultiplicity::Star,
            "<{}>: {result} at {}",
            cell.name,
            cell.position_kore_sort
        );
    };
    for cell in cells.values() {
        if cell.name == "generatedTop" {
            // Compilation adds the counter cell as the top cell's last child, after the cells
            // the configuration declares.
            let mut arguments = cell.child_kore_sorts.clone();
            arguments.push(sort("SortGeneratedCounterCell"));
            assert_declared(cell, &arguments);
        } else {
            assert_declared(cell, &cell.child_kore_sorts);
        }
    }

    // The compiled definition's view holds the same cells and the counter cell, each with the
    // signature `definition.kore` declares.
    let execution = ResolvedDefinition::resolve(&compiled.execution_definition).unwrap();
    let compiled_cells = declared_cells(&execution, execution.main_module_id())
        .into_iter()
        .map(|cell| (cell.name.clone(), cell))
        .collect::<BTreeMap<_, _>>();
    for cell in compiled_cells.values() {
        assert_declared(cell, &cell.child_kore_sorts);
    }
    assert!(compiled_cells.contains_key("generatedCounter"));
    for (name, cell) in &cells {
        if name != "generatedTop" {
            assert_eq!(compiled_cells.get(name), Some(cell), "<{name}>");
        }
    }
}
