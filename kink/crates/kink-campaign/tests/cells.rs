//! Where a compiled configuration's cells sit in its KORE terms (`CellLayout`), and the cell
//! projection that leaves out the cells a definition declares `unobservable`.
//!
//! Through cells of multiplicity `1` a cell's position is one argument path; inside a `?` or `*`
//! cell it is that path relative to each instance, so the projection leaves the cell out of each
//! instance, and compares a Map's or a Set's instances as a multiset and a List's in order. A
//! Map's key is never left out: a projection that would leave it out is refused, naming the key
//! and what to do instead. A `?` or `*` cell can itself be unobservable: its own position (the
//! optional cell, the whole collection) is left out whole. The projection of executed ends runs on
//! `testdata/k/cells/harts.k`; the order of a collection's components, and the checks of a
//! projection's positions, run on hand-built configurations.

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::path::Path;
use std::time::Duration;

use k_rust::backend::{Backend, BackendOptions};
use k_rust::builtin;
use k_rust::definition::configuration::CellMultiplicity;
use k_rust::kast::Sort as KSort;
use k_rust::kompile::CompileOptions;
use k_rust::kompile::initial_configuration::{
    ConfigurationAssembler, ConfigurationError, ProgramGrammar,
};
use k_rust::kore::ast::{Pattern, Sort};
use k_rust::outer::ResolvedSource;
use kink_campaign::{
    CellLayout, CellLayoutRefusal, CellProjection, Collection, CollectionKind, Through,
    UnobservedPosition,
};
use kink_native::NativeValidator;
use kink_native::execution::{ExecutionAdapter, ExecutionBudget, SolverProfile};
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
        Ok(UnobservedPosition {
            path: vec![1, 0],
            symbols: vec![TOP.to_owned(), "Lbl'-LT-'regs'-GT-'".to_owned()],
            cell: "w".to_owned(),
            sort: sort("SortWCell"),
            heads: layout.cells()[cell("w")].heads.clone(),
            through: Vec::new(),
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
    // A `*` cell's collection is read from its sort's hooked symbols, and a Map's key is the
    // child at the sort of its element's first argument.
    let map = Collection {
        kind: CollectionKind::Map,
        element: "LblThreadCellMapItem".to_owned(),
        instance: 1,
        concat: "Lbl'Unds'ThreadCellMap'Unds'".to_owned(),
        unit: "Lbl'Stop'ThreadCellMap".to_owned(),
    };
    assert_eq!(layout.cells()[cell("thread")].collection, Some(map.clone()));
    assert_eq!(layout.cells()[cell("thread")].key, Some(cell("id")));
    for other in ["w", "opt", "inner", "threads", "id", "tmp"] {
        assert_eq!(layout.cells()[cell(other)].collection, None, "<{other}>");
        assert_eq!(layout.cells()[cell(other)].key, None, "<{other}>");
    }
    // A `?` or `*` cell's own position is fixed. Inside a `?` cell the path goes on through the
    // instance; inside a `*` cell it goes on from each element's instance.
    assert_eq!(
        layout
            .position(cell("opt"))
            .map(|p| (p.path, p.sort, p.through)),
        Ok((vec![2], sort("SortOptCell"), Vec::new()))
    );
    assert_eq!(
        layout
            .position(cell("thread"))
            .map(|p| (p.path, p.sort, p.through)),
        Ok((vec![3, 0], sort("SortThreadCellMap"), Vec::new()))
    );
    assert_eq!(
        layout
            .position(cell("inner"))
            .map(|p| (p.path, p.symbols, p.through)),
        Ok((
            vec![2, 0],
            vec![TOP.to_owned(), "Lbl'-LT-'opt'-GT-'".to_owned()],
            Vec::new()
        ))
    );
    assert_eq!(
        layout.position(cell("tmp")),
        Ok(UnobservedPosition {
            path: vec![3, 0, 1],
            symbols: vec![
                TOP.to_owned(),
                "Lbl'-LT-'threads'-GT-'".to_owned(),
                "Lbl'-LT-'thread'-GT-'".to_owned(),
            ],
            cell: "tmp".to_owned(),
            sort: sort("SortTmpCell"),
            heads: heads("tmp"),
            through: vec![Through {
                at: 2,
                cell: "thread".to_owned(),
                sort: sort("SortThreadCellMap"),
                heads: heads("thread"),
                collection: map,
            }],
        })
    );
    // The key and the top cell have no position a projection may leave out.
    assert_eq!(
        layout.position(cell("id")),
        Err(CellLayoutRefusal::MapKeyLeftOut {
            cell: "id".to_owned(),
            key: "id".to_owned(),
            collection: "thread".to_owned(),
        })
    );
    assert_eq!(
        layout.map_key(cell("id")),
        Some((cell("id"), cell("thread")))
    );
    assert_eq!(layout.map_key(cell("tmp")), None);
    assert!(matches!(
        layout.position(cell("generatedTop")),
        Err(CellLayoutRefusal::Layout { .. })
    ));

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

/// An unobservable cell inside a `?` or `*` cell is left out of each instance: its position is
/// its path relative to the instance, through each collection on the way.
#[test]
fn an_unobservable_cell_inside_an_optional_or_collection_cell_is_left_out_of_each_instance() {
    let marked = |configuration: &str| {
        let layout = layout(configuration).unwrap();
        layout
            .unobservable_projection()
            .unwrap()
            .unwrap()
            .positions()
            .iter()
            .map(|p| {
                (
                    p.cell.clone(),
                    p.path.clone(),
                    p.through
                        .iter()
                        .map(|t| (t.cell.clone(), t.at, t.collection.kind))
                        .collect::<Vec<_>>(),
                )
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(
        marked(
            "<k> $PGM:K </k>
             <threads> <thread multiplicity=\"*\" type=\"Map\"> <id> 0 </id> <tmp unobservable=\"\"> 0 </tmp> </thread> </threads>"
        ),
        [("tmp".to_owned(), vec![1, 0, 1], vec![("thread".to_owned(), 2, CollectionKind::Map)])]
    );
    assert_eq!(
        marked(
            "<k> $PGM:K </k> <opt multiplicity=\"?\"> <inner unobservable=\"\"> 0 </inner> </opt>"
        ),
        [("inner".to_owned(), vec![1, 0], Vec::new())]
    );
    // Nested: a Set of `?` cells, and a List inside a Map's instances inside a Set's.
    assert_eq!(
        marked(
            "<k> $PGM:K </k>
             <outer multiplicity=\"*\" type=\"Set\"> <mid multiplicity=\"?\"> <leaf unobservable=\"\"> 0 </leaf> </mid> </outer>"
        ),
        [("leaf".to_owned(), vec![1, 0, 0], vec![("outer".to_owned(), 1, CollectionKind::Set)])]
    );
    assert_eq!(
        marked(
            "<k> $PGM:K </k>
             <a multiplicity=\"*\" type=\"Set\"> <b multiplicity=\"*\" type=\"Map\"> <key> 0 </key>
               <c multiplicity=\"*\" type=\"List\"> <v> 0 </v> <w unobservable=\"\"> 0 </w> </c> </b> </a>"
        ),
        [(
            "w".to_owned(),
            vec![1, 0, 1, 1],
            vec![
                ("a".to_owned(), 1, CollectionKind::Set),
                ("b".to_owned(), 2, CollectionKind::Map),
                ("c".to_owned(), 3, CollectionKind::List),
            ]
        )]
    );
}

/// A Map's key is never left out: each element holds the key as its first argument beside the
/// instance, so the content left out would still be compared there. An unobservable key, or an
/// unobservable cell inside a key, is refused, naming the key and the Map, with the next steps.
#[test]
fn a_maps_key_left_out_is_refused_with_the_next_step() {
    let refused = layout(&configuration("", "", "", MARK))
        .unwrap()
        .unobservable_projection()
        .unwrap_err();
    assert_eq!(
        refused,
        CellLayoutRefusal::MapKeyLeftOut {
            cell: "id".to_owned(),
            key: "id".to_owned(),
            collection: "thread".to_owned(),
        }
    );
    assert_eq!(refused.reason(), "map-key-left-out");
    assert_eq!(
        refused.to_string(),
        "the cell <id> is left out, but it is the key by which the Map cell <thread> holds its \
         instances: each element holds the key as its first argument beside the instance, so its \
         content would still be compared there, and the projection cannot leave <id> out; drop \
         `unobservable` from <id>, or compare no cell inside <thread>, so that it is left out \
         whole: mark <thread> unobservable, or narrow the compared cells to cells outside it"
    );

    let inside = layout(
        "<k> $PGM:K </k>
         <ts> <t multiplicity=\"*\" type=\"Map\"> <key> <a> 0 </a> <b unobservable=\"\"> 0 </b> </key> <v> 0 </v> </t> </ts>",
    )
    .unwrap()
    .unobservable_projection()
    .unwrap_err();
    assert_eq!(
        inside,
        CellLayoutRefusal::MapKeyLeftOut {
            cell: "b".to_owned(),
            key: "key".to_owned(),
            collection: "t".to_owned(),
        }
    );
    assert_eq!(
        inside.to_string(),
        "the cell <b> is left out, but it lies inside <key>, the key by which the Map cell <t> \
         holds its instances: each element holds the key as its first argument beside the \
         instance, so its content would still be compared there, and the projection cannot leave \
         <b> out; drop `unobservable` from <b>, or compare no cell inside <t>, so that it is left \
         out whole: mark <t> unobservable, or narrow the compared cells to cells outside it"
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

/// `testdata/k/cells/harts.k`, compiled, with the end of each program run on it.
struct Harts {
    validator: NativeValidator,
    backend: Backend,
    projection: CellProjection,
}

impl Harts {
    fn new() -> Self {
        let validator = NativeValidator::bind(
            support::load_path(&Path::new(support::DIR).join("cells/harts.k"), "HARTS"),
            CompileOptions::default(),
        );
        let compiled = validator.compile_baseline().expect("harts.k compiles");
        let backend = Backend::new(
            &compiled.artifacts().definition_kore,
            k_rust::kast::identifier::encode(&compiled.definition().main_module),
            BackendOptions::default(),
        )
        .expect("backend");
        let projection = CellLayout::of(&compiled)
            .unwrap()
            .unobservable_projection()
            .unwrap()
            .expect("unobservable cells");
        Self {
            validator,
            backend,
            projection,
        }
    }

    /// The one end of `program`, a concrete program that runs to its end on one path.
    fn end(&mut self, program: &str) -> Pattern {
        let compiled = self.validator.compile_baseline().unwrap();
        let definition = self.validator.baseline().definition();
        let grammar = ProgramGrammar::new(definition).unwrap();
        let mut assembler = ConfigurationAssembler::new(
            &grammar,
            &definition.main_module,
            "HARTS-SYNTAX",
            &compiled.artifacts().configuration_variables,
        );
        assembler.program(&KSort::new("Prog"), program).unwrap();
        assembler
            .bind_stream_defaults::<ConfigurationError>(false, false, || Ok(Vec::new()))
            .unwrap();
        let initial = assembler.finish().unwrap();
        let execution = ExecutionAdapter::with_profile(SolverProfile::BUILD)
            .execute(
                &mut self.backend,
                &initial,
                ExecutionBudget {
                    time: Duration::from_secs(60),
                    max_simplification_iterations: 10_000,
                    max_depth: Some(100),
                    max_breadth: None,
                },
            )
            .expect("execution");
        let [leaf] = execution.leaves() else {
            panic!("{program}: one leaf, not {}", execution.leaves().len())
        };
        let state = leaf.branch.state.clone();
        assert!(
            matches!(&state, Pattern::Application { symbol, .. } if symbol.name == TOP),
            "{program}: {state:?}"
        );
        state
    }

    fn projected(&mut self, program: &str) -> Pattern {
        let end = self.end(program);
        let projected = self.projection.project(&end).into_owned();
        // The projection is idempotent: its value is already the projection of itself.
        assert_eq!(
            self.projection.project(&projected).into_owned(),
            projected,
            "{program}"
        );
        projected
    }
}

/// Whether `pattern` holds `\top` of the sort `name` somewhere.
fn holds_top(pattern: &Pattern, name: &str) -> bool {
    let mut found = false;
    k_rust::kore::walk::for_each_post_order(pattern, |node| {
        found |= matches!(node, Pattern::Top { sort } if *sort == self::sort(name));
    });
    found
}

/// The projection of executed ends through every kind of holder in `harts.k`: two ends have
/// equal projections exactly when they differ only in unobservable cells, each read in its own
/// instance. A Map's instances are compared by key, so the order the harts were created in does
/// not matter but a key or a compared cell does; a `?` cell's presence is compared; a Set's
/// instances are compared as a multiset, so two jobs the projection makes equal stay two; a
/// List's instances are compared in order. Every pair below differs as whole ends.
#[test]
fn the_projection_leaves_each_unobservable_cell_out_of_every_instance() {
    let mut harts = Harts::new();
    let one = "hart(1, 5, 7)";
    let two = "seq(hart(1, 5, 7), hart(2, 6, 8))";
    let set = "seq(hart(1, 5, 7), seq(job(1, 1, 1), job(1, 1, 2)))";
    let list = "seq(item(1, 1), item(2, 2))";
    let equal = [
        (one, "hart(1, 5, 9)"),
        (two, "seq(hart(2, 6, 1), hart(1, 5, 2))"),
        (
            "seq(hart(1, 5, 7), res(1, 3))",
            "seq(hart(1, 5, 7), res(1, 4))",
        ),
        (set, "seq(hart(1, 5, 7), seq(job(1, 1, 3), job(1, 1, 4)))"),
        (list, "seq(item(1, 3), item(2, 4))"),
    ];
    let differ = [
        (one, "hart(1, 6, 7)"),
        (one, "hart(2, 5, 7)"),
        (two, "seq(hart(2, 5, 1), hart(1, 6, 2))"),
        (
            "seq(hart(1, 5, 7), res(1, 3))",
            "seq(hart(1, 5, 7), free(1))",
        ),
        (set, "seq(hart(1, 5, 7), job(1, 1, 1))"),
        (set, "seq(hart(1, 5, 7), seq(job(1, 2, 1), job(1, 1, 2)))"),
        (list, "seq(item(2, 1), item(1, 2))"),
    ];
    for (verdict, pairs) in [(true, &equal[..]), (false, &differ[..])] {
        for &(left, right) in pairs {
            assert_ne!(
                harts.end(left),
                harts.end(right),
                "{left} / {right}: whole ends"
            );
            assert_eq!(
                harts.projected(left) == harts.projected(right),
                verdict,
                "{left} / {right}"
            );
        }
    }
    // Each unobservable cell's placeholder stands in its instance, and the compared cells stay.
    let projected = harts.projected("seq(hart(1, 5, 7), seq(job(1, 1, 1), item(1, 1)))");
    for sort in ["SortTmpCell", "SortRvCell", "SortJtCell", "SortItCell"] {
        assert!(holds_top(&projected, sort), "{sort}: {projected:?}");
    }
    assert!(!holds_top(&projected, "SortPcCell"), "{projected:?}");
    // A position the walk does not reach is left alone: an end without instances.
    let empty = harts.end("free(1)");
    assert_eq!(harts.projection.project(&empty).into_owned(), empty);
}

/// The application of the parameterless symbol `name` to `arguments`.
fn app(name: &str, arguments: Vec<Pattern>) -> Pattern {
    Pattern::Application {
        symbol: k_rust::kore::ast::Symbol {
            name: name.to_owned(),
            sort_parameters: Vec::new(),
        },
        arguments,
    }
}

/// A constant, the content of a hand-built cell.
fn constant(name: &str) -> Pattern {
    app(name, Vec::new())
}

/// A hand-built configuration `<generatedTop>(C)` whose one argument is a `*` cell's collection
/// of `kind` holding `<job>(<a>(_), <b>(_))` instances (a Map's keyed by `<a>`), and the position
/// of `<job>`'s argument `left_out` inside each instance.
struct Jobs {
    kind: CollectionKind,
    position: UnobservedPosition,
}

impl Jobs {
    const ELEMENT: &str = "LblJobCellItem";
    const CONCAT: &str = "Lbl'Unds'JobCellCollection'Unds'";
    const UNIT: &str = "Lbl'Stop'JobCellCollection";
    const JOB: &str = "Lbl'-LT-'job'-GT-'";

    fn new(kind: CollectionKind, left_out: u32) -> Self {
        let cell = if left_out == 0 { "a" } else { "b" };
        let position = UnobservedPosition {
            path: vec![0, left_out],
            symbols: vec![TOP.to_owned(), Self::JOB.to_owned()],
            cell: cell.to_owned(),
            sort: sort(&format!("Sort{}Cell", cell.to_uppercase())),
            heads: vec![format!("Lbl'-LT-'{cell}'-GT-'")],
            through: vec![Through {
                at: 1,
                cell: "job".to_owned(),
                sort: sort("SortJobCellCollection"),
                heads: vec![
                    Self::UNIT.to_owned(),
                    Self::CONCAT.to_owned(),
                    Self::ELEMENT.to_owned(),
                ],
                collection: Collection {
                    kind,
                    element: Self::ELEMENT.to_owned(),
                    instance: u32::from(kind == CollectionKind::Map),
                    concat: Self::CONCAT.to_owned(),
                    unit: Self::UNIT.to_owned(),
                },
            }],
        };
        Self { kind, position }
    }

    fn projection(&self) -> CellProjection {
        CellProjection::new(vec![self.position.clone()]).unwrap()
    }

    /// The `<job>` instance with `a` and `b` as its cells' contents, `None` standing for the
    /// position's placeholder.
    fn job(&self, a: Option<&str>, b: Option<&str>) -> Pattern {
        let content = |cell: &str, value: Option<&str>| match value {
            Some(value) => app(&format!("Lbl'-LT-'{cell}'-GT-'"), vec![constant(value)]),
            None => Pattern::Top {
                sort: self.position.sort.clone(),
            },
        };
        app(Self::JOB, vec![content("a", a), content("b", b)])
    }

    /// The configuration holding `instances`, right-nested in the order given; a Map's element
    /// holds each instance by its `<a>` cell.
    fn end(&self, instances: &[(Option<&str>, Option<&str>)]) -> Pattern {
        let elements = instances.iter().map(|&(a, b)| {
            let instance = self.job(a, b);
            match self.kind {
                CollectionKind::Map => app(
                    Self::ELEMENT,
                    vec![
                        app("Lbl'-LT-'a'-GT-'", vec![constant(a.unwrap())]),
                        instance,
                    ],
                ),
                _ => app(Self::ELEMENT, vec![instance]),
            }
        });
        let collection = elements
            .rev()
            .reduce(|rest, element| app(Self::CONCAT, vec![element, rest]))
            .unwrap_or_else(|| constant(Self::UNIT));
        app(TOP, vec![collection])
    }
}

/// A Map's or a Set's projected collection is a function of the multiset of its projected
/// instances, whatever order an end writes them in: an end the backend does not normalise (a
/// work-bound, breadth-bound or stopped leaf keeps its state as given) may write equal
/// collections in another order. The components are sorted after each instance is projected, so
/// an uncompared cell's content plays no part in the order: instances whose uncompared cell
/// precedes the compared one sort by the compared one. A List keeps its order.
#[test]
fn the_projection_reads_a_maps_or_a_sets_instances_as_a_multiset_in_any_written_order() {
    for kind in [CollectionKind::Map, CollectionKind::Set] {
        // `<b>` left out: the instances differ in the compared `<a>` and the uncompared `<b>`.
        let jobs = Jobs::new(kind, 1);
        let projection = jobs.projection();
        let written = jobs.end(&[(Some("Lbl1"), Some("LblX")), (Some("Lbl2"), Some("LblY"))]);
        let permuted = jobs.end(&[(Some("Lbl2"), Some("LblZ")), (Some("Lbl1"), Some("LblW"))]);
        let sorted = jobs.end(&[(Some("Lbl1"), None), (Some("Lbl2"), None)]);
        assert_eq!(
            projection.project(&written).into_owned(),
            sorted,
            "{kind:?}"
        );
        assert_eq!(
            projection.project(&permuted).into_owned(),
            sorted,
            "{kind:?}"
        );
        // Without the sort, the permuted end would keep its written order and differ.
        assert_ne!(
            jobs.end(&[(Some("Lbl2"), None), (Some("Lbl1"), None)]),
            sorted,
            "{kind:?}"
        );
        // A compared difference still shows.
        let other = jobs.end(&[(Some("Lbl1"), Some("LblX")), (Some("Lbl3"), Some("LblY"))]);
        assert_ne!(
            projection.project(&other),
            projection.project(&written),
            "{kind:?}"
        );
    }

    // A Set's `<a>` left out: it precedes the compared `<b>`, so sorting the written instances
    // before projecting them would order them by `<a>`, keeping `left`'s compared (Y, X) apart
    // from `right`'s (X, Y). Sorted after projecting, both are (X, Y).
    let jobs = Jobs::new(CollectionKind::Set, 0);
    let projection = jobs.projection();
    let left = jobs.end(&[(Some("Lbl1"), Some("LblY")), (Some("Lbl2"), Some("LblX"))]);
    let right = jobs.end(&[(Some("Lbl1"), Some("LblX")), (Some("Lbl2"), Some("LblY"))]);
    let sorted = jobs.end(&[(None, Some("LblX")), (None, Some("LblY"))]);
    assert_eq!(projection.project(&left).into_owned(), sorted);
    assert_eq!(projection.project(&right).into_owned(), sorted);
    assert_ne!(
        jobs.end(&[(None, Some("LblY")), (None, Some("LblX"))]),
        sorted
    );

    // A collection whose instances already hold the placeholder but are out of order is still
    // changed: the projection sorts it, so it is idempotent and agrees with its sorted
    // permutation.
    let jobs = Jobs::new(CollectionKind::Set, 1);
    let projection = jobs.projection();
    let unsorted = jobs.end(&[(Some("Lbl2"), None), (Some("Lbl1"), None)]);
    let sorted = jobs.end(&[(Some("Lbl1"), None), (Some("Lbl2"), None)]);
    assert!(matches!(
        projection.project(&unsorted),
        std::borrow::Cow::Owned(_)
    ));
    assert_eq!(projection.project(&unsorted).into_owned(), sorted);
    assert!(matches!(
        projection.project(&sorted),
        std::borrow::Cow::Borrowed(_)
    ));

    // A List's instances are compared in order: a permutation is another projection.
    let jobs = Jobs::new(CollectionKind::List, 1);
    let projection = jobs.projection();
    let written = jobs.end(&[(Some("Lbl1"), Some("LblX")), (Some("Lbl2"), Some("LblY"))]);
    let permuted = jobs.end(&[(Some("Lbl2"), Some("LblY")), (Some("Lbl1"), Some("LblX"))]);
    assert_eq!(
        projection.project(&permuted).into_owned(),
        jobs.end(&[(Some("Lbl2"), None), (Some("Lbl1"), None)])
    );
    assert_ne!(projection.project(&permuted), projection.project(&written));
}

/// A collection on a position's path is reached after at least one step of the path and before
/// its last, in path order: at step 0 it would be the top cell, at the path's length the
/// position itself, and out of order the walk could not go from one to the next.
#[test]
fn a_cell_projection_refuses_a_collection_outside_its_paths_steps_or_out_of_order() {
    let valid = Jobs::new(CollectionKind::Set, 1).position;
    assert!(CellProjection::new(vec![valid.clone()]).is_ok());
    let at = |steps: &[u32]| {
        let mut position = valid.clone();
        position.through = steps
            .iter()
            .map(|&at| Through {
                at,
                ..valid.through[0].clone()
            })
            .collect();
        position
    };
    for steps in [&[0][..], &[2], &[3], &[1, 1]] {
        let refused = CellProjection::new(vec![at(steps)]).unwrap_err();
        assert_eq!(
            refused.kind(),
            kink_campaign::OracleFailureKind::InvalidDeclaration,
            "{steps:?}"
        );
        assert!(
            refused.to_string().contains("in path order"),
            "{steps:?}: {refused}"
        );
    }
    // Two collections in path order are admitted.
    let mut deeper = at(&[1, 2]);
    deeper.path.push(0);
    deeper.symbols.push("Lbl'-LT-'b'-GT-'".to_owned());
    assert!(CellProjection::new(vec![deeper]).is_ok());
    // Out of order.
    let mut swapped = at(&[2, 1]);
    swapped.path.push(0);
    swapped.symbols.push("Lbl'-LT-'b'-GT-'".to_owned());
    assert!(CellProjection::new(vec![swapped]).is_err());
}
