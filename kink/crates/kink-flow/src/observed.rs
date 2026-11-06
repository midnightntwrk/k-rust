//! What a flow program's second slot compares: the observable cells (README, "Which cells are
//! compared").
//!
//! A cell declared `unobservable` holds state no use of the definition may observe, so no kill
//! may rest on its content. By default the second slot compares every cell except the
//! unobservable ones: it is the whole final term (slot `whole-term`) when the configuration
//! declares no unobservable cell, and otherwise the final term with the content of each maximal
//! unobservable cell replaced by `\top` of its sort (slot `cells`, kink-campaign
//! `StateProjection::Cells`). A manifest may narrow the compared cells (`[result] cells`); it can
//! never widen them past the specification's statement, so naming an unobservable cell, or a cell
//! inside one, is refused.
//!
//! The cells are kink-campaign's [`CellLayout`] of the compiled configuration. Without a
//! narrowing the second slot is [`CellLayout::unobservable_projection`]. The layout is a premise
//! only of a projection that leaves something out, so a specification that declares no
//! unobservable cell and names no `[result] cells` compares the whole term whether or not its
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
//! neither is named in a document, neither can be named in `[result] cells`, and the counter's
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
    /// The maximal cells compared, in configuration preorder: the cells of `[result] cells` and
    /// the key of each Map that encloses one when the manifest narrows them, otherwise the
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
    /// `[result] cells` names no cell of the configuration (reason `result-cell-unknown`).
    CellUnknown { cell: String, cells: Vec<String> },
    /// `[result] cells` names an unobservable cell, or a cell inside one (reason
    /// `result-cell-unobservable`).
    CellUnobservable { cell: String, unobservable: String },
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
            Self::CellUnknown { cell, cells } => write!(
                formatter,
                "[result] cells names <{cell}>, which is no cell of the configuration; name \
                 cells the configuration declares: {}",
                cells
                    .iter()
                    .map(|cell| format!("<{cell}>"))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Self::CellUnobservable { cell, unobservable } if cell == unobservable => write!(
                formatter,
                "[result] cells names <{cell}>, which the specification declares unobservable: \
                 a manifest may narrow the compared cells but never compare an unobservable one; \
                 drop <{cell}> from [result] cells, or drop `unobservable` from its declaration \
                 if a test may observe it"
            ),
            Self::CellUnobservable { cell, unobservable } => write!(
                formatter,
                "[result] cells names <{cell}>, which lies inside the unobservable cell \
                 <{unobservable}>: a manifest may narrow the compared cells but never compare an \
                 unobservable one; drop <{cell}> from [result] cells, or drop `unobservable` from \
                 the declaration of <{unobservable}> if a test may observe it"
            ),
        }
    }
}

impl std::error::Error for ResultRefusal {}

/// What the second slot of every program of `compiled` compares, narrowed to the cells
/// `narrowed` when the manifest names them (`[result] cells`; module documentation). `kore` is
/// `compiled`'s `definition.kore`, parsed.
pub fn result_projection(
    compiled: &ValidatedDefinition,
    kore: &KoreDefinition,
    narrowed: Option<&[String]>,
) -> Result<ResultProjection, ResultRefusal> {
    let layout = match CellLayout::of_parsed(compiled, kore) {
        Ok(layout) => layout,
        // Every cell the layout would declare unobservable is a production of the execution
        // definition with the attribute, so without one and without a narrowing nothing is left
        // out, and the whole term needs no layout.
        Err(CellLayoutRefusal::Layout { .. })
            if narrowed.is_none()
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
    let cells = layout.cells();
    // The specification's cells: neither the top cell (index 0) nor the counter cell compilation
    // adds beside the declared ones.
    let declared = |at: usize| {
        cells[at].parent.is_some()
            && !(cells[at].parent == Some(0) && cells[at].kore_symbol == GENERATED_COUNTER)
    };
    let names = |set: &[usize]| {
        set.iter()
            .map(|&at| cells[at].name.clone())
            .collect::<Vec<_>>()
    };
    let unobservable = (0..cells.len())
        .filter(|&at| cells[at].unobservable)
        .collect::<Vec<_>>();

    let Some(written) = narrowed else {
        // Every maximal unobservable cell, as kink-campaign's own projection leaves them out.
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
                declared(at)
                    && cells[at]
                        .parent
                        .is_some_and(|parent| parent == 0 || enclosing.contains(&parent))
                    && !left_out.contains(&at)
                    && !enclosing.contains(&at)
            })
            .collect::<Vec<_>>();
        return Ok(ResultProjection {
            state,
            compared: Some(names(&compared)),
            not_compared: names(&left_out),
            unobservable: names(&unobservable),
        });
    };

    let mut chosen = BTreeSet::new();
    for name in written {
        let Some(at) = layout.cell(name).filter(|&at| declared(at)) else {
            return Err(ResultRefusal::CellUnknown {
                cell: name.clone(),
                cells: names(
                    &(0..cells.len())
                        .filter(|&at| declared(at))
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
    let enclosing = chosen
        .iter()
        .flat_map(|&at| layout.ancestors(at))
        .collect::<BTreeSet<_>>();
    let mut left_out = (0..cells.len())
        .filter(|&at| {
            declared(at)
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
        compared: Some(names(&chosen)),
        not_compared: names(&left_out),
        unobservable: names(&unobservable),
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
