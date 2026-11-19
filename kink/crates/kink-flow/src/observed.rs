//! What a flow program's second slot compares: the observable cells (README, "Which cells are
//! compared").
//!
//! A cell declared `unobservable` holds state no use of the definition may observe, so no kill
//! may rest on its content. By default the second slot compares every cell except the
//! unobservable ones: it is the whole final term (slot `whole-term`) when the configuration
//! declares no unobservable cell, and otherwise the final term with the content of each maximal
//! unobservable cell replaced by `\top` of its sort (slot `cells`, kink-campaign
//! `StateProjection::Cells`). The manifest's projections narrow the compared cells to the union
//! of the cells they compare (`FlowManifest::record_cells`; `[[projection]] compare`); they can
//! never widen them past the specification's statement, so a projection naming an unobservable
//! cell, or a cell inside one, is refused. A narrowing to no cell (every projection a `trace`
//! projection) leaves out every cell the specification declares.
//!
//! The cells are kink-campaign's [`CellLayout`] of the compiled configuration. Without a
//! narrowing the second slot is [`CellLayout::unobservable_projection`]. The layout is a premise
//! only of a projection that leaves something out, so a specification that declares no
//! unobservable cell and whose projections narrow nothing compares the whole term whether or not its
//! cells can be placed: it is refused at stage `result` only when the layout is needed, and
//! otherwise the layout only names the compared cells in the documents.
//!
//! A position is left out in every end of the baseline's shape: through cells of multiplicity
//! `1` it is one argument path, and inside a `?` or `*` cell it is that path relative to each
//! instance, so the projection leaves the cell out of every instance and compares a Map's or a
//! Set's instances as a multiset (kink-campaign `CellLayout::position`). A Map holds each
//! instance by its key, the instance's key cell, so a cell compared inside a Map's instances is
//! compared per key: narrowed to the cells `C`, the compared cells `K` are the cells of `C` and
//! the key of every Map that encloses a cell of `C`, each without the cells of `K` inside it. The
//! uncompared positions are every cell outside `K` that is neither inside a cell of `K` nor
//! encloses one, whose parent encloses a cell of `K` (the siblings of `K` and of its ancestors),
//! and every maximal unobservable cell inside a cell of `K`. A Map's key is never left out: an
//! unobservable cell at or inside one is refused (`map-key-left-out`), since each element also
//! holds the key as its first argument, where the projection would still compare it. Under a
//! narrowing that names a cell inside the Map, marking the whole Map unobservable is refused in
//! turn (`result-cell-unobservable`): only a narrowing to cells outside it leaves it out whole.
//!
//! `<generatedTop>` and `<generatedCounter>` are compilation's cells, not the specification's:
//! neither is named in a document, neither can be named in a projection's `compare`, and the counter's
//! content is erased by every projection of a final term.

use std::collections::BTreeSet;
use std::fmt;

use k_rust::definition::{AttributeKey, Definition, Sentence, configuration::CellMultiplicity};
use k_rust::kore::ast::Definition as KoreDefinition;
use kink_campaign::{
    CellLayout, CellLayoutRefusal, CellProjection, OracleDeclaration, StateProjection,
};
use kink_native::ValidatedDefinition;
use serde_json::{Value, json};

use crate::manifest::RecordCell;

/// The KORE symbol of compilation's fresh-name counter cell, the top cell's last child.
const GENERATED_COUNTER: &str = "Lbl'-LT-'generatedCounter'-GT-'";

/// The slot names when the second slot compares the whole final term.
pub const WHOLE_TERM_SLOTS: [&str; 2] = ["exit-stop", "whole-term"];
/// The slot names when the second slot leaves some cell out.
pub const CELLS_SLOTS: [&str; 2] = ["exit-stop", "cells"];

/// What a flow program's second slot compares, computed once at admission
/// ([`result_projection`]).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResultProjection {
    /// [`StateProjection::WholeTerm`] when nothing is left out; otherwise
    /// [`StateProjection::Cells`] over [`Self::not_compared`].
    pub state: StateProjection,
    /// The maximal cells compared, in configuration preorder: the cells the projections compare
    /// and the key of each Map that encloses one when the projections narrow them, otherwise the
    /// outermost cells neither left out nor enclosing a cell left out. A cell listed here is
    /// compared except for the cells of [`Self::not_compared`] inside it. `None` when the second
    /// slot compares the whole term of a configuration whose cells cannot be placed
    /// (kink-campaign `cell-layout`), so no cell can be named.
    pub compared: Option<Vec<String>>,
    /// The cells whose content the second slot leaves out, in configuration preorder.
    pub not_compared: Vec<String>,
    /// Every cell the specification declares unobservable, in configuration preorder.
    pub unobservable: Vec<String>,
}

impl ResultProjection {
    /// The cell projection of the second slot; `None` when it compares the whole final term.
    #[must_use]
    pub fn cells(&self) -> Option<&CellProjection> {
        match &self.state {
            StateProjection::Cells(projection) => Some(projection),
            _ => None,
        }
    }

    /// The slot names, in slot order: `["exit-stop", "whole-term"]` when nothing is left out,
    /// `["exit-stop", "cells"]` otherwise.
    #[must_use]
    pub fn slots(&self) -> [&'static str; 2] {
        if self.cells().is_some() {
            CELLS_SLOTS
        } else {
            WHOLE_TERM_SLOTS
        }
    }

    /// The two oracles of every flow program: the exit stop without an exit-code cell, then
    /// [`Self::state`]; a semantic crash is outside the operand domain (`reject`).
    #[must_use]
    pub fn oracles(&self) -> Vec<OracleDeclaration> {
        crate::results::oracle_declarations(self.state.clone())
    }

    /// Every document's `result`: `{slots, compared, not_compared, unobservable}`.
    #[must_use]
    pub fn value(&self) -> Value {
        json!({
            "slots": self.slots(),
            "compared": self.compared,
            "not_compared": self.not_compared,
            "unobservable": self.unobservable,
        })
    }
}

/// Why the compared cells cannot be computed: the specification is refused at stage `result`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResultRefusal {
    /// The configuration's cells cannot be placed or projected (kink-campaign's reasons:
    /// `cell-layout`, `unobservable-cell-outside-configuration`, `map-key-left-out`).
    Layout(CellLayoutRefusal),
    /// A projection's `compare` names no cell of the configuration (reason
    /// `result-cell-unknown`).
    CellUnknown {
        cell: String,
        projection: String,
        cells: Vec<String>,
    },
    /// A projection's `compare` names an unobservable cell, or a cell inside one (reason
    /// `result-cell-unobservable`).
    CellUnobservable {
        cell: String,
        projection: String,
        unobservable: String,
    },
}

impl ResultRefusal {
    /// The refusal's reason, a stable name.
    #[must_use]
    pub const fn reason(&self) -> &'static str {
        match self {
            Self::Layout(refusal) => refusal.reason(),
            Self::CellUnknown { .. } => "result-cell-unknown",
            Self::CellUnobservable { .. } => "result-cell-unobservable",
        }
    }
}

impl fmt::Display for ResultRefusal {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Layout(refusal) => refusal.fmt(formatter),
            Self::CellUnknown {
                cell,
                projection,
                cells,
            } => write!(
                formatter,
                "the projection `{projection}` compares <{cell}>, which is no cell of the \
                 configuration; name cells the configuration declares: {}",
                cells
                    .iter()
                    .map(|cell| format!("<{cell}>"))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Self::CellUnobservable {
                cell,
                projection,
                unobservable,
            } if cell == unobservable => write!(
                formatter,
                "the projection `{projection}` compares <{cell}>, which the specification \
                 declares unobservable: a projection may narrow the compared cells but never \
                 compare an unobservable one; drop <{cell}> from the projection's `compare`, or \
                 drop `unobservable` from its declaration if a test may observe it"
            ),
            Self::CellUnobservable {
                cell,
                projection,
                unobservable,
            } => write!(
                formatter,
                "the projection `{projection}` compares <{cell}>, which lies inside the \
                 unobservable cell <{unobservable}>: a projection may narrow the compared cells \
                 but never compare an unobservable one; drop <{cell}> from the projection's \
                 `compare`, or drop `unobservable` from the declaration of <{unobservable}> if a \
                 test may observe it"
            ),
        }
    }
}

impl std::error::Error for ResultRefusal {}

/// What the second slot of every program of `compiled` compares, narrowed to the cells
/// `narrowed` when the projections narrow them (`FlowManifest::record_cells`, each cell with the
/// projection that names it; module documentation). `kore` is `compiled`'s `definition.kore`,
/// parsed.
///
/// `own` holds, where the record is not narrowed, the `compare` of each projection that has one
/// (`crate::manifest::compare_cells`): each is checked as the narrowing of a record of its own
/// and its result discarded, so a cell a projection names that the configuration does not have,
/// or that it declares unobservable, is refused as it would be were that projection the flow's
/// only one, though another projection keeps every cell in the record. A narrowed record already
/// holds every projection's `compare` (the union), so `own` is read only where it is not.
pub fn result_projection(
    compiled: &ValidatedDefinition,
    kore: &KoreDefinition,
    narrowed: Option<&[RecordCell]>,
    own: &[Vec<RecordCell>],
) -> Result<ResultProjection, ResultRefusal> {
    let layout = match CellLayout::of_parsed(compiled, kore) {
        Ok(layout) => layout,
        // Every cell the layout would declare unobservable is a production of the execution
        // definition with the attribute, so without one and without a narrowing nothing is left
        // out, and the whole term needs no layout. A projection's own `compare` names cells, which
        // only the layout places.
        Err(CellLayoutRefusal::Layout { .. })
            if narrowed.is_none()
                && own.is_empty()
                && !declares_unobservable(&compiled.artifacts().execution_definition) =>
        {
            return Ok(ResultProjection {
                state: StateProjection::WholeTerm,
                compared: None,
                not_compared: Vec::new(),
                unobservable: Vec::new(),
            });
        }
        Err(refusal) => return Err(ResultRefusal::Layout(refusal)),
    };
    let Some(written) = narrowed else {
        let result = unnarrowed(&layout)?;
        for cells in own {
            narrowed_to(&layout, cells)?;
        }
        return Ok(result);
    };
    narrowed_to(&layout, written)
}

/// The specification's cells of `layout`: neither the top cell (index 0) nor the counter cell
/// compilation adds beside the declared ones.
fn declared(layout: &CellLayout, at: usize) -> bool {
    let cells = layout.cells();
    cells[at].parent.is_some()
        && !(cells[at].parent == Some(0) && cells[at].kore_symbol == GENERATED_COUNTER)
}

/// The names of the cells `set` of `layout`, in its order.
fn names(layout: &CellLayout, set: &[usize]) -> Vec<String> {
    set.iter()
        .map(|&at| layout.cells()[at].name.clone())
        .collect()
}

/// Every cell `layout` declares unobservable, in configuration preorder.
fn unobservable(layout: &CellLayout) -> Vec<usize> {
    let cells = layout.cells();
    (0..cells.len())
        .filter(|&at| cells[at].unobservable)
        .collect()
}

/// The second slot when nothing narrows it: every maximal unobservable cell left out, as
/// kink-campaign's own projection leaves them out.
fn unnarrowed(layout: &CellLayout) -> Result<ResultProjection, ResultRefusal> {
    let cells = layout.cells();
    let left_out = layout.maximal_unobservable();
    let state = layout
        .unobservable_projection()
        .map_err(ResultRefusal::Layout)?
        .map_or(StateProjection::WholeTerm, StateProjection::Cells);
    let enclosing = left_out
        .iter()
        .flat_map(|&at| layout.ancestors(at))
        .collect::<BTreeSet<_>>();
    let compared = (0..cells.len())
        .filter(|&at| {
            declared(layout, at)
                && cells[at]
                    .parent
                    .is_some_and(|parent| parent == 0 || enclosing.contains(&parent))
                && !left_out.contains(&at)
                && !enclosing.contains(&at)
        })
        .collect::<Vec<_>>();
    Ok(ResultProjection {
        state,
        compared: Some(names(layout, &compared)),
        not_compared: names(layout, &left_out),
        unobservable: names(layout, &unobservable(layout)),
    })
}

/// The second slot narrowed to the cells `written` (module documentation).
fn narrowed_to(
    layout: &CellLayout,
    written: &[RecordCell],
) -> Result<ResultProjection, ResultRefusal> {
    let cells = layout.cells();
    let mut chosen = BTreeSet::new();
    for RecordCell {
        cell: name,
        projection,
    } in written
    {
        let Some(at) = layout.cell(name).filter(|&at| declared(layout, at)) else {
            return Err(ResultRefusal::CellUnknown {
                cell: name.clone(),
                projection: projection.clone(),
                cells: names(
                    layout,
                    &(0..cells.len())
                        .filter(|&at| declared(layout, at))
                        .collect::<Vec<_>>(),
                ),
            });
        };
        if let Some(hidden) = std::iter::once(at)
            .chain(layout.ancestors(at))
            .find(|&at| cells[at].unobservable)
        {
            return Err(ResultRefusal::CellUnobservable {
                cell: name.clone(),
                projection: projection.clone(),
                unobservable: cells[hidden].name.clone(),
            });
        }
        chosen.insert(at);
    }
    // A Map holds each instance by its key, so a cell compared inside its instances is compared
    // per key: the key of every Map that encloses a named cell is compared with it.
    let keys = chosen
        .iter()
        .flat_map(|&at| layout.ancestors(at))
        .filter(|&above| cells[above].multiplicity == CellMultiplicity::Star)
        .filter_map(|holder| cells[holder].key)
        .collect::<Vec<_>>();
    chosen.extend(keys);
    // A compared cell inside another compared cell adds nothing.
    let chosen = chosen
        .iter()
        .copied()
        .filter(|&at| !layout.ancestors(at).any(|above| chosen.contains(&above)))
        .collect::<Vec<_>>();
    // The top cell encloses every compared cell; named here too so that a narrowing to no cell
    // leaves out every cell the specification declares, its children.
    let enclosing = chosen
        .iter()
        .flat_map(|&at| layout.ancestors(at))
        .chain([0])
        .collect::<BTreeSet<_>>();
    let mut left_out = (0..cells.len())
        .filter(|&at| {
            declared(layout, at)
                && cells[at]
                    .parent
                    .is_some_and(|parent| enclosing.contains(&parent))
                && !chosen.contains(&at)
                && !enclosing.contains(&at)
        })
        .collect::<Vec<_>>();
    // Every unobservable cell at or inside a compared cell is left out; at a compared cell it is
    // a key, which the projection refuses to leave out.
    left_out.extend(layout.maximal_unobservable().into_iter().filter(|&at| {
        std::iter::once(at)
            .chain(layout.ancestors(at))
            .any(|above| chosen.contains(&above))
    }));
    left_out.sort_unstable();
    left_out.dedup();

    let state = if left_out.is_empty() {
        StateProjection::WholeTerm
    } else {
        StateProjection::Cells(
            layout
                .projection(&left_out)
                .map_err(ResultRefusal::Layout)?,
        )
    };

    Ok(ResultProjection {
        state,
        compared: Some(names(layout, &chosen)),
        not_compared: names(layout, &left_out),
        unobservable: names(layout, &unobservable(layout)),
    })
}

/// Whether some production of `definition` carries `unobservable`: every cell a configuration
/// declares unobservable is one.
fn declares_unobservable(definition: &Definition) -> bool {
    definition.modules.iter().any(|module| {
        module.local_sentences.iter().any(|sentence| {
            matches!(&**sentence, Sentence::Production { attributes, .. }
                if attributes.has(AttributeKey::Unobservable))
        })
    })
}
