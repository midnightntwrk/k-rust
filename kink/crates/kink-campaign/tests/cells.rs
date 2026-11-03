//! Where a compiled configuration's cells sit in its KORE terms (`CellLayout`), and the cell
//! projection that leaves out the cells a definition declares `unobservable`.
//!
//! A cell has a fixed position exactly when every strict ancestor has multiplicity `1`; the
//! projection of an unobservable cell that lies inside a `?` or `*` cell is refused, naming the
//! enclosing cell and what to do instead. A `?` or `*` cell can itself be unobservable: its own
//! position (the optional cell, the whole collection) is fixed.

#[path = "../../../testdata/k/support.rs"]
mod support;

use k_rust::builtin;
use k_rust::definition::configuration::CellMultiplicity;
use k_rust::kompile::CompileOptions;
use k_rust::kore::ast::Sort;
use k_rust::outer::ResolvedSource;
use kink_campaign::{CellLayout, CellLayoutRefusal, UnobservedPosition};
use kink_native::NativeValidator;
use kink_patch::Baseline;

const TOP: &str = "Lbl'-LT-'generatedTop'-GT-'";

/// The layout of the module `CELLS` declaring `configuration`.
fn layout(configuration: &str) -> Result<CellLayout, CellLayoutRefusal> {
    layout_with(configuration, "")
}

/// The layout of the module `CELLS` declaring `configuration` beside the sentences `written`.
fn layout_with(configuration: &str, written: &str) -> Result<CellLayout, CellLayoutRefusal> {
    let source = format!(
        "module CELLS\n  imports INT\n  imports MAP\n  configuration {configuration}\n  {written}\nendmodule\n"
    );
    let mut resolver = |_: &str, required: &str| {
        builtin::embedded(required).ok_or_else(|| format!("{required} is not embedded"))
    };
    let baseline = Baseline::load(
        ResolvedSource::new("cells.k", source),
        "CELLS",
        None,
        &mut resolver,
        &support::options(),
    )
    .unwrap();
    let compiled = NativeValidator::bind(baseline, CompileOptions::default())
        .compile_baseline()
        .unwrap();
    CellLayout::of(&compiled)
}

fn sort(name: &str) -> Sort {
    Sort::Application {
        name: name.to_owned(),
        arguments: Vec::new(),
    }
}

/// `regs` holds `w` and `z`; `opt` is optional; `thread` is a `Map` collection cell.
fn configuration(w: &str, opt: &str, thread: &str, id: &str) -> String {
    format!(
        "<k> $PGM:K </k>
         <regs> <w{w}> 0 </w> <z> 0 </z> </regs>
         <opt multiplicity=\"?\"{opt}> <inner> 0 </inner> </opt>
         <threads> <thread multiplicity=\"*\" type=\"Map\"{thread}> <id{id}> 0 </id> <tmp> 0 </tmp> </thread> </threads>"
    )
}

const MARK: &str = " unobservable=\"\"";

#[test]
fn the_layout_places_every_cell_at_its_argument_in_configuration_preorder() {
    let layout = layout(&configuration(MARK, "", "", "")).unwrap();
    let cells = layout
        .cells()
        .iter()
        .map(|cell| {
            (
                cell.name.as_str(),
                cell.parent
                    .map(|parent| layout.cells()[parent].name.as_str()),
                cell.index,
                cell.multiplicity,
                cell.unobservable,
            )
        })
        .collect::<Vec<_>>();
    use CellMultiplicity::{One, Optional, Star};
    assert_eq!(
        cells,
        [
            ("generatedTop", None, 0, One, false),
            ("k", Some("generatedTop"), 0, One, false),
            ("regs", Some("generatedTop"), 1, One, false),
            ("w", Some("regs"), 0, One, true),
            ("z", Some("regs"), 1, One, false),
            ("opt", Some("generatedTop"), 2, Optional, false),
            ("inner", Some("opt"), 0, One, false),
            ("threads", Some("generatedTop"), 3, One, false),
            ("thread", Some("threads"), 0, Star, false),
            ("id", Some("thread"), 0, One, false),
            ("tmp", Some("thread"), 1, One, false),
            // Compilation adds the counter cell as the top cell's last child.
            ("generatedCounter", Some("generatedTop"), 4, One, false),
        ]
    );
    let cell = |name| layout.cell(name).unwrap();
    assert_eq!(
        layout.position(cell("w")),
        Some(UnobservedPosition {
            path: vec![1, 0],
            symbols: vec![TOP.to_owned(), "Lbl'-LT-'regs'-GT-'".to_owned()],
            cell: "w".to_owned(),
            sort: sort("SortWCell"),
            heads: layout.cells()[cell("w")].heads.clone(),
        })
    );
    // The heads are the symbols of the position's sort: the cell's own symbol, its initializer
    // and its sort projection; for a `?` cell its unit too; for a `*` cell the collection's
    // symbols.
    let heads = |name| layout.cells()[cell(name)].heads.clone();
    assert_eq!(
        heads("w"),
        ["Lbl'-LT-'w'-GT-'", "LblinitWCell", "Lblproject'Coln'WCell"]
    );
    assert_eq!(
        heads("opt"),
        [
            "Lbl'-LT-'opt'-GT-'",
            "Lbl'Stop'OptCell",
            "LblinitOptCell",
            "Lblproject'Coln'OptCell"
        ]
    );
    assert_eq!(
        heads("thread"),
        [
            "Lbl'Stop'ThreadCellMap",
            "Lbl'Unds'ThreadCellMap'Unds'",
            "LblThreadCellMapItem",
            "LblinitThreadCell",
            "Lblproject'Coln'ThreadCellMap"
        ]
    );
    // A `?` or `*` cell's own position is fixed; a position inside one is not.
    assert_eq!(
        layout.position(cell("opt")).map(|p| (p.path, p.sort)),
        Some((vec![2], sort("SortOptCell")))
    );
    assert_eq!(
        layout.position(cell("thread")).map(|p| (p.path, p.sort)),
        Some((vec![3, 0], sort("SortThreadCellMap")))
    );
    for inside in ["inner", "id", "tmp"] {
        assert_eq!(layout.position(cell(inside)), None, "<{inside}>");
    }
    assert_eq!(layout.varying_ancestor(cell("id")), Some(cell("thread")));
    assert_eq!(layout.varying_ancestor(cell("inner")), Some(cell("opt")));
    assert_eq!(layout.position(cell("generatedTop")), None, "the whole end");

    let projection = layout.unobservable_projection().unwrap().unwrap();
    assert_eq!(
        projection.positions(),
        [layout.position(cell("w")).unwrap()]
    );
}

#[test]
fn no_unobservable_cell_is_no_cell_projection() {
    assert_eq!(
        layout(&configuration("", "", "", ""))
            .unwrap()
            .unobservable_projection(),
        Ok(None)
    );
}

/// The decision for an unobservable cell inside a `?` or `*` cell: refused, naming the enclosing
/// cell, with the next step.
#[test]
fn an_unobservable_cell_inside_an_optional_or_collection_cell_is_refused_with_the_next_step() {
    let refused = layout(&configuration("", "", "", MARK))
        .unwrap()
        .unobservable_projection()
        .unwrap_err();
    assert_eq!(
        refused,
        CellLayoutRefusal::UnobservableCellPosition {
            cell: "id".to_owned(),
            enclosing: "thread".to_owned(),
            multiplicity: CellMultiplicity::Star,
        }
    );
    assert_eq!(refused.reason(), "unobservable-cell-position");
    assert_eq!(
        refused.to_string(),
        "the unobservable cell <id> lies inside the * cell <thread>, so its position varies \
         between ends; mark <thread> unobservable, or move <id> out of it"
    );

    let optional = layout(
        "<k> $PGM:K </k> <opt multiplicity=\"?\"> <inner unobservable=\"\"> 0 </inner> </opt>",
    )
    .unwrap()
    .unobservable_projection()
    .unwrap_err();
    assert_eq!(
        optional,
        CellLayoutRefusal::UnobservableCellPosition {
            cell: "inner".to_owned(),
            enclosing: "opt".to_owned(),
            multiplicity: CellMultiplicity::Optional,
        }
    );

    // Nested varying cells: the outermost is named, since marking it is what suffices.
    let nested = layout(
        "<k> $PGM:K </k>
         <outer multiplicity=\"*\" type=\"Set\"> <mid multiplicity=\"?\"> <leaf unobservable=\"\"> 0 </leaf> </mid> </outer>",
    )
    .unwrap()
    .unobservable_projection()
    .unwrap_err();
    assert_eq!(
        nested,
        CellLayoutRefusal::UnobservableCellPosition {
            cell: "leaf".to_owned(),
            enclosing: "outer".to_owned(),
            multiplicity: CellMultiplicity::Star,
        }
    );
}

/// A `?` or `*` cell that is itself unobservable is left out whole, and an unobservable cell
/// inside it is covered by it, so nothing is refused.
#[test]
fn an_unobservable_optional_or_collection_cell_is_left_out_whole() {
    let layout = layout(&configuration(MARK, MARK, MARK, MARK)).unwrap();
    let projection = layout.unobservable_projection().unwrap().unwrap();
    assert_eq!(
        projection
            .positions()
            .iter()
            .map(|p| (p.cell.as_str(), p.path.clone(), p.sort.clone()))
            .collect::<Vec<_>>(),
        [
            ("w", vec![1, 0], sort("SortWCell")),
            ("opt", vec![2], sort("SortOptCell")),
            ("thread", vec![3, 0], sort("SortThreadCellMap")),
        ]
    );
}

/// A `cell` production written outside any configuration is not in the layout, which is the
/// configuration's. Declared unobservable, it is refused with the next step, since no end has its
/// position. (One that holds a cell of the configuration is refused by k-rust's definition checks,
/// "Cell <w> found twice in configuration"; the layout counts holders in the tree only anyway.)
#[test]
fn a_cell_production_outside_the_configuration_is_not_in_the_layout() {
    let configuration = "<k> $PGM:K </k> <regs> <w> 0 </w> </regs>";
    let wrap =
        |attributes: &str| format!("syntax WrapCell ::= \"<wrap>\" Int \"</wrap>\" [{attributes}]");
    let layout = layout_with(configuration, &wrap("cell")).unwrap();
    assert_eq!(
        layout
            .cells()
            .iter()
            .map(|cell| cell.name.as_str())
            .collect::<Vec<_>>(),
        ["generatedTop", "k", "regs", "w", "generatedCounter"]
    );
    let w = layout.cell("w").unwrap();
    assert_eq!(
        layout.cells()[layout.cells()[w].parent.unwrap()].name,
        "regs"
    );
    assert_eq!(layout.unobservable_projection(), Ok(None));

    let refused = layout_with(configuration, &wrap("cell, unobservable")).unwrap_err();
    assert_eq!(
        refused,
        CellLayoutRefusal::UnobservableCellOutsideConfiguration {
            cell: "<wrap>_</wrap>_CELLS_WrapCell_Int".to_owned()
        }
    );
    assert_eq!(refused.reason(), "unobservable-cell-outside-configuration");
    assert_eq!(
        refused.to_string(),
        "the unobservable cell production `<wrap>_</wrap>_CELLS_WrapCell_Int` is placed by no \
         configuration, so no end has its position; declare the cell in a configuration instead \
         of writing its production, or drop `unobservable`"
    );
}
