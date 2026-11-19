//! `kink-flow prune FLOW.toml MUTATIONS [PATTERNS.toml]` (or `kink-flow prune FLOW.toml...`,
//! "Several flows"): which cases of the corpus are redundant, read from what the corpus discharges (README, "Redundant programs"). It writes no
//! lock and edits no file; it reads and fills the caches as `run`, `query` and `coverage` do.
//!
//! # The obligations
//!
//! A corpus discharges existential obligations, each of the shape "some case does X":
//!
//! - `mutations`: a mutation is killed, discharged by every case whose cell of the full kill
//!   matrix is a proved difference ([`crate::report::kill_cells`]); in a flow that declares
//!   `[[projection]]`, a mutation is killed under a projection `run` lists ("Projections"
//!   below);
//! - `patterns`: a pattern is hit, discharged by every case whose answer is a hit
//!   ([`crate::query::hit_cells`]); every pattern is an obligation of the corpus, with or without
//!   `programs` ([`crate::query`], "The obligation");
//! - each coverage family's items (`rules`, `requirements`, `syntax`, `rule_windows`,
//!   `syntax_paths`, `flips`), discharged by the cases the item's covering list names
//!   ([`crate::coverage::cover_cells`]). Each is covered by one case's own run or record: a
//!   rule's firing, an outcome class of a condition or of an operand, a production or a field
//!   value a fired instance touched, a window one path took as consecutive steps, a syntax path
//!   one fired instance touched, a flip's killer;
//! - the unique-cause level of the `requirements` family (`[coverage] mcdc`), which no list of
//!   single dischargers states: a pair of cases may discharge it together ("Pair obligations"
//!   below);
//! - `arguments`: an argued item's invariant evidence that holds, discharged by every case whose
//!   run read a step of the item's rules ([`crate::coverage::argument_cells`]).
//!
//! Each obligation's row gives, per case, a decided discharge, a decided non-discharge, or an
//! unknown cell (an answer neither decided nor refuted: a timeout, an unknown, a record that left
//! a value or a combination out). An unknown cell never discharges. An obligation with no case
//! that can discharge it in any corpus (an `equivalent` mutation, a refused flip, an
//! out-of-scope rule) is none.
//!
//! The report is computed, never read from a stored document: `prune` runs `coverage` (tier 2,
//! the flips where the front end derives them) in process, then the kill search and the pattern
//! walk of the corpus (lazily, "Lazy cells" below; with `--full` `run --full` and `query
//! --full`), each through its own command's code and caches ([`crate::coverage::coverage_front`],
//! [`crate::search::run_session`], [`crate::query::query_session`]), so it is a function of the
//! definition, the corpus and the counted budgets, as their verdicts are. The run stores no report
//! ([`crate::search::run_stored`]), so `report` and `fuzz --kill` keep reading the last `run`'s.
//! A family whose input is absent is skipped, and the document says so: no mutation list (a front
//! end's layout without one), or no patterns (none named and none declared).
//!
//! # The lists
//!
//! The `mutations` and `patterns` families read a list, and each `families` entry names it
//! (`list`: `{path, corpus_own}`, `path` null for the patterns the manifest declares or a
//! family with no list). The report holds for the lists it read: a case removable against a
//! list that is not the corpus's own may be the only killer of a mutation of the corpus's own
//! list. Only a front end knows its corpus's own lists (its layout), so `corpus_own` is what the
//! front end states ([`PruneOptions::corpus_lists`]), and null where none does: kink-flow's own
//! command line takes the mutation list as an operand and has no notion of a corpus's own list.
//!
//! # The scope
//!
//! The report is of one flow: its obligations are those of the flow's definition. A flow that
//! names its corpus root (`[corpus] root`) reads cases that other flows may read too, each with
//! the obligations of its own definition, and a case is removable from the root only when it is
//! redundant in every flow that reads it, which is not the intersection of the flows' lists
//! ("Redundant alone, removable together" holds across flows as within one). So the document of
//! such a flow says that its answer holds for this flow alone (`scope`: `{flow_only: true,
//! corpus_root, detail}`, and a `note:` line of the text rendering); the document of a flow whose
//! cases are in its own directory has no `scope`. The flows that read a root are known to no
//! flow, so a prune of them all names them ("Several flows").
//!
//! # Several flows
//!
//! `kink-flow prune FLOW.toml...` names flows by their manifests alone (a shell glob names
//! them), and each reads the mutation lists its manifest names (`[mutations] lists`,
//! [`FlowManifest::mutation_lists`], their mutations in the order named, an id two lists give
//! refused) and the patterns it declares; a K flow has no default list, so a flow that names
//! none is refused by name. One flow gives that flow's document, its `mutations` family's
//! `list` naming the lists (`declared`, `corpus_own` true). Several flows give one report
//! ([`flows_command`]), which holds for the flows given (`scope`: `{flow_only: false, flows,
//! detail}`); a flow not given may read a case.
//!
//! Every flow given names one corpus root (the canonical directory of `[corpus] root`); a flow
//! that names none, or another, refuses the command. A case is one case in every flow: its id
//! is its path relative to the root, and two flows' programs of one id must be read from one
//! file of the root, and one file under the same ids, else the command is refused (a `[[program]]`
//! of inline text is no file of the root, so its id is one flow's alone).
//!
//! Each flow is bound and run as a prune of it alone is: its coverage, kill search and pattern
//! walk, through its own front end and cache, give its own facts ("The obligations"), each of its
//! obligations over the cases it reads. A case a flow does not read has no cell in that flow's
//! obligations, as a case outside a projection's domain has none under it, so it is neither a
//! discharger nor unknown there, and its class there decides nothing. The facts are merged before
//! any decision: a case is redundant alone when no rule of any flow that reads it keeps it, and
//! the set removable together is one walk over every case of the root, in reverse of the joint
//! order (`reverse-flow-manifest`: the cases of the flows in the order given, each flow's in
//! manifest order after the cases of the flows before it), a case removed only when no flow's
//! rules, read against the cases still kept, keep it. Since each flow's rules read only its own
//! obligations over its own cases, removing a case no flow keeps loses no flow's discharge, by
//! the argument of a single flow applied to each, and a case one flow reads alone is kept
//! whenever that flow keeps it. A case whose entry in some flow states that it must be rejected
//! before it runs is kept for that flow (`rejected-before-run`); a flow that cannot ask its
//! question (a manifest, list or case refused, a family's command refused) refuses the command,
//! never reads as a flow that reads no case. Every entry and reason that names an obligation or
//! keeps a case names its flow (`flow`, the manifest as given), the text rendering as `FLOW:
//! mutations ID under NAME`; a case's baseline class is per flow (`classes`), and each flow's
//! `spec`, `families`, `accounting` and `projections` are in `flows`. A record (`--lock`) is
//! one definition's, and a cache directory (`--cache`) would replace flows' different defaults,
//! so neither is taken with several flows: each flow reads its own default cache, which two
//! manifests in one directory share. Lazily, every flow's searches stay open together
//! while the walk decides, since it may ask any flow's cell; `--full` runs each flow's in turn.
//! The removal order keeps each flow's early cases (the killers and witnesses its records name)
//! only where the flows' manifest orders agree (limit `flows`).
//!
//! # What is never prunable
//!
//! - A case a claim names: a pattern's `programs`. Removing it makes the pattern list refuse
//!   (`no program of the manifest has the id`). Nothing else of the manifest, the mutation lists
//!   or the pattern lists names a case: a mutation's `expect` states a verdict, not a case.
//! - A case whose decided cell refutes a universal claim: a killer of a mutation that expects to
//!   survive, a hitter of a pattern that expects `no`, the case whose run gave an argued item's
//!   invariant evidence its failing state, and a case whose own expectation is unmet. Removing
//!   it would hide the finding, not a redundancy.
//! - A case that is the only decided discharger of an obligation; of a pair obligation, a case
//!   without which no decided pair discharges it.
//! - A case whose cell on an obligation is unknown while no other case discharges that
//!   obligation: removing it could lose the only potential discharger.
//! - A case whose decided row is a side of a pair obligation that no decided pair discharges
//!   without it, while another case's cell on it is unknown or its baseline undecided
//!   (`unknown-partner`): what that case holds may be the other side of a pair with its row.
//! - A case whose baseline run is undecided (class `timeout` or `unknown`: kink did not ask it of
//!   any mutant or pattern) while some obligation has no decided discharger: each of its cells
//!   is unknown, so the rule above applies to every obligation.
//! - A case whose entry states that it must be rejected before it runs (`expect = { rejected =
//!   ... }`, class `rejected` or `accepted`; PJ-32, `rejected-before-run`): no command runs it or
//!   asks it of a mutant or a pattern, so it discharges no obligation prune reads, and it is in
//!   the corpus for obligations prune does not read (the implementation's acceptance under the
//!   acceptance projection, the kill of a grammar mutation). Its redundancy is not decided here.
//!
//! So the report only ever under-states what is prunable: every unknown counts against removal.
//! The document counts the unknown cells (`unanswered`).
//!
//! # Pair obligations
//!
//! A unique-cause requirement of an atom `a` ([`crate::coverage`], "Unique-cause MC/DC") is
//! covered by two valuation combinations the comparable cases' records hold, one where the
//! condition held and one where it was refuted, in which `a` has the two truths and every other
//! atom the same decided truth. The two may be two cases' records, so its covering list (both
//! sides of the one pair the item shows) is not a list of cases each of which discharges it
//! alone: where only `x` holds one side and only `y` the other, neither is redundant. Its
//! obligation over a set S of cases, P(S), is a disjunction over every pair the rule's
//! combination rows give (`guard.combinations`, not only the item's `pair`): some pair with a
//! case of its held side and a case of its refuted side in S. One case is on both sides of a
//! pair whose two combinations its own record holds. Reading P(S) as "S holds a case of the
//! covering list" would call `x` and `y` each redundant and remove one of them.
//!
//! The pairs are of decided sides: a row whose guard outcome is decided, `a` two-valued and
//! every other atom decided ([`crate::coverage::cover_cells`]). A case's cell is unknown where
//! its record may hold a side the rows do not show: a row whose outcome (`undecided`,
//! `stopped`), truth of `a` or truth of another atom is undecided, `a` not undefined; or a record
//! that left a combination out (`truncated_by`). A case of an undecided baseline holds no record,
//! so what it would hold may be a side too. P(S) is the decided discharge; each rule above
//! reads it where a single-case obligation reads "a decided discharger in S":
//!
//! - sole-discharger: c is kept when P(S) and not P(S ∖ {c}); for a single-case obligation that
//!   is c being its only decided discharger in S;
//! - unknown: when not P(S ∖ {c}), c is kept when its cell is unknown, and, where c's row is a
//!   decided side, when another case of S has an unknown cell or an undecided baseline
//!   (`unknown-partner`, those cases its `with`);
//! - baseline-undecided: when not P(S ∖ {c}), as for every obligation;
//! - refutes: no unique-cause outcome refutes a universal claim. The requirement states no
//!   expectation; `open` and `undecided` state only that no recorded pair discharges it, which a
//!   case added to the corpus can change; an argued one's evidence is read with `arguments`.
//!
//! Removing a case c that no rule keeps from S loses no pair that may hold over S. Either P(S ∖
//! {c}), and a decided pair discharges the obligation without c; or neither P(S ∖ {c}) nor
//! P(S), since c is not kept as a sole discharger. Then no decided pair holds over S, and a pair
//! that may hold has a side that a case u of an unknown cell or an undecided baseline may hold.
//! u is not c, which neither rule keeps, so u is in S ∖ {c}; c's cell is decided, so c holds no
//! side beyond its rows; and none of c's rows is the other side, since c is kept as a partner
//! when one is a decided side and such a u is in S ∖ {c}. So every pair that may hold over S
//! may hold over S ∖ {c}, and the report only ever under-states what is prunable.
//!
//! The walk ("Redundant alone, and removable together") never falsifies P: a case whose removal
//! would is kept as a sole discharger. So where P holds over the corpus it holds over the kept
//! cases; where it does not, every case of an unknown cell or an undecided baseline is kept at
//! every step (P(S ∖ {c}) never holds), and, where there is one, every case of a decided side.
//! The coverage rows are the same in both modes (one coverage run, complete), so a lazy report
//! and a `--full` one read the same pairs and decide the same.
//!
//! # Projections
//!
//! In a flow that declares `[[projection]]`, a kill obligation is a (mutation, projection) pair,
//! for each mutation of the list and each projection `[run] projections` lists
//! ([`FlowManifest::run_projections`]): "some case of the projection's domain kills the mutation
//! under it". The document names it by `family`, `id` (the mutation's) and `projection`, in every
//! entry and reason that names an obligation, and the text rendering as `mutations ID under
//! NAME`. The row's own status, the search over the union of the projections' observations, is
//! no obligation there: a kill under a projection is a difference of what the run's slots
//! compare ([`crate::projected`]), so a kill only the union gives is one no listed projection
//! observes.
//!
//! Under a projection P a case's cell is a decided discharge where `run`'s verdict of it under P
//! is `killed`, unknown where it is `unknown`, and a decided non-discharge where it is `agree`.
//! A case outside P's domain has no cell under P: it is neither a discharger nor unknown, and its
//! undecided baseline keeps it for no obligation under P. A projection judged as the run's own
//! with no `domain` takes the row's status, so its cells are the row's own; one `run` does not
//! judge (`undecided`) leaves each comparable case of its domain unknown
//! ([`crate::report::projection_kill_cells`]). Every rule above then reads each pair as one
//! obligation, so a case is removable only when every (mutation, projection) kill it gives is
//! given by another kept case, which is one of that projection's domain: a case that is the only
//! killer of a mutation under one projection is kept, whoever kills it under another.
//!
//! A string `expect = "survive"` is a claim on the row's own status: a killed row is no
//! obligation under any projection, and the killers of the row's own search refute it, since
//! survival under the union is survival under every projection. A table `expect = { NAME =
//! "survive" }` of a mutation killed under NAME makes that pair no obligation, and each case that
//! kills it there refutes it (`refutes` naming the projection).
//!
//! Lazily, a pair with a known killer under its projection is read as a killed row is, its cells
//! not judged asked one at a time ("Lazy cells"); one ask runs the mutation's full row over the
//! one program and answers it under every listed projection, each its status there
//! ([`crate::search::KillCells`]), so a cell is asked once whatever the number of projections,
//! and `accounting.cells` counts (mutation, case) cells. `--lock` gives the search each
//! (mutation, projection)'s recorded killer too, and a run row moves where its killer under a
//! projection is removed.
//!
//! # Grammar mutations
//!
//! `run` judges a grammar mutation (PJ-34) only in its default search, first-kill over the whole
//! corpus in a flow that declares no projection; `run --full` and a flow that declares
//! projections give its row `error` (`grammar-not-run`) and exit 2, so `prune --full`, and
//! `prune` of such a flow, refuse the list as their `run` does. The default search parses every
//! case again under the mutant's grammar before it runs anything, so its row states each case's
//! verdict (`grammar`), and prune reads that row whole, asking none of its cells (a cell asked one
//! at a time is refused too) ([`crate::report::grammar_kill_cells`]): a case whose reparse kills
//! discharges, the row's killer discharges, and a case whose reparse is undecided, or left to a
//! campaign call that did not run every case (any status but `survived`), is unknown.
//!
//! # Redundant alone, and removable together
//!
//! A case is redundant alone when it is not kept by any rule above against the whole corpus:
//! every obligation it discharges has another decided discharger (a pair obligation, a decided
//! pair without it), and every obligation on which its cell is unknown has a decided
//! discharger. That is not the same as removable together: two cases can each be the other's
//! only alternative. So the report also gives one set removable together, built greedily:
//! walking the cases in reverse manifest order, a case is removed when the same rules, read
//! against the cases still kept, keep it nowhere. Each obligation then keeps a decided
//! discharger among the kept cases (a pair obligation, a decided pair), or every unknown cell
//! it had, whatever is removed.
//!
//! The order is reverse manifest order because every command that names one discharger of an
//! obligation names, by default, an early case: a mutation's killer is the first killing case of
//! the search order, whose groups are each in manifest order, and a pattern's witness the first
//! hitting case in manifest order, while no record names another ([`crate::search`],
//! [`crate::query`]). Removing the latest cases first keeps those, so the corpus record's rows
//! move least. The set is a function of the corpus and of this order; it is maximal under the
//! order (no kept case can be removed after it), not minimum: a smallest removable set is a
//! set cover problem.
//!
//! # Lazy cells
//!
//! The report reads three things of an obligation's row: whether a decided discharger other than
//! the case judged is among the cases still considered (the sole and unknown rules), the case's
//! own cell (discharger, unknown or neither), and, for a claim a decided cell refutes, every
//! refuting case. It never needs a row's every cell to answer them. Without `--full` the
//! `mutations` and `patterns` rows are asked lazily, and every decision is still the one the full
//! rows give:
//!
//! - The ordinary search of each family runs first: `run`'s first-kill search over the list and
//!   `query`'s walk of each pattern ([`crate::search`], [`crate::query`], "The obligation"),
//!   through their code and caches. A killed mutation's search gives one decided killer, its
//!   witness here, and every cell it asked before it; a hit pattern's walk one hitter and the
//!   pairs it asked. Every other row (survived, unknown, open, undecided, or no obligation) is
//!   one the search asked of every case it can be asked of, so it is complete, as under
//!   `--full`. Which killer or hitter it found depends on the recorded killer or witness of
//!   `--lock` and on the search order, never a decision: the decisions are functions of the
//!   cells alone.
//! - Let w be a known decided discharger of an obligation o, and S the cases considered (the
//!   whole corpus for redundant alone, the cases still kept during the walk). For a case c ≠ w
//!   with w in S, o keeps c by no rule: c is not o's only decided discharger in S, since w is
//!   one, and the unknown and baseline-undecided rules apply only to an obligation with no
//!   decided discharger in S other than c. So while some known discharger other than c is in S,
//!   no unasked cell of o can change the decision about c.
//! - When none is, the decision needs more of the row: its cells over S other than c that were
//!   not asked are asked one at a time (a mutation's in its search order, the programs that
//!   witness its edit first, a pattern's in manifest order) until one is a decided discharger or
//!   none is left, and then c's own cell if it was not asked. Each is asked through the code
//!   its full command asks it with ([`crate::search::KillCells`], [`crate::query::HitCells`]):
//!   a mutation's full row over an O holding that program alone, under the corpus's floor of
//!   polls, which tier 1 serves when a record is current; a pattern's one row. No record of the
//!   corpus record (`--lock`) is a cell: it only orders the searches. Every cell learned is
//!   kept for the later decisions. Then o's known cells over S other than c are its every cell
//!   there, so the rules read what the full row gives.
//! - A mutation that expects to survive and is killed, and a pattern that expects `no` and is
//!   hit, keep every refuting case: their rows are asked whole.
//! - A case that is not redundant alone is kept by the walk without asking anything: each rule
//!   of a single-case obligation only weakens as S shrinks (a discharger outside S counts for
//!   nothing), and a pair obligation's rules keep, against each S the walk reaches, every case
//!   they keep against the whole corpus ("Pair obligations"), so a case some rule keeps against
//!   the whole corpus is kept against every S of the walk. The document gives no reason the
//!   walk found for it.
//! - The coverage rows, the pair obligations' included, are complete in both modes: `prune`
//!   runs the same coverage either way, and asks none of their cells.
//! - Within a family a cell's value does not depend on which other cells were asked: under tier
//!   1 an outcome is a function of its key ([`crate::search`], module docs, the schedule
//!   paragraph) and a pattern answer of its own key ([`crate::query`]). Where the caches are off
//!   (a solver the clock bounds), every cell is a live run in either mode, and neither mode's
//!   report is a function of its inputs.
//!
//! In a lazy report the evidence holds the cells asked, not every cell: each obligation of a
//! `redundant` entry lists the other known dischargers (`others`; a pair obligation, the pairs
//! that hold without the case, `pairs`, each `{held, refuted}` naming its sides' other cases)
//! with whether its row is complete (`complete`), the entry counts the obligations on which the
//! case's own cell was not asked (`unasked`), and each family and `unanswered` say whether
//! every cell was asked (`complete`). A distinguished flip's row is never complete: its kill
//! search stops at its first killer (limit `flips`). `accounting.cells` counts each family's
//! cells: the matrix size, those the ordinary search held, and those asked one at a time after
//! it.
//!
//! # The corpus record
//!
//! With `--lock FILE` the record is read, never written: a removable case that is a recorded
//! killer (`[run]`, `[coverage]` flips), witness (`[query]`) or a program of a compare row
//! (`[compare]`) moves those rows when it is removed, so `--locked` fails until a command
//! without it re-records them; the document names them per case.
//!
//! # Limits
//!
//! `[[implementation]]` compare evidence and a case's own expectation are universal per case,
//! not existential, and are not read as obligations (an unmet expectation still keeps its case).
//! A fuzz template list may name a case (`program`); it is not read.

use crate::{
    cli::{EXIT_UNASKED, EXIT_YES, FrontEnd, Verb, completed},
    coverage::{ARGUED, CoverageOptions, FAMILIES},
    flips::DISTINGUISHED,
    lock::{Lock, LockKind},
    manifest::FlowManifest,
    mutation::{Expect, MutationList},
    pattern::{PatternExpect, PatternList},
    projected::Judge,
    query::{HitCell, HitCells, QueryOptions},
    results::ResultClass,
    search::{KillCell, KillCells, Recorded, RunMode, RunOptions},
};
use kink_campaign::ScheduleMode;
use kink_native::execution::SolverProfile;
use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

/// The `schema` of the prune document.
pub const PRUNE_SCHEMA: &str = "kink-flow-prune";
/// The version of the prune document. Version 2 asks the `mutations` and `patterns` rows lazily
/// unless `--full` (module docs, "Lazy cells"), with the same decisions, and names what the
/// evidence holds: the document's `mode` (`lazy` or `full`); each family's `list` (`{path,
/// corpus_own}`, the `mutations` and `patterns` families) and `complete`; each `redundant`
/// entry's obligations and unknown cells with `complete`, and its `unasked`; `unanswered`'s
/// `complete`; `accounting.cells`; and the limit `lazy` of a lazy report. Every field of
/// version 1 keeps its name and, under `--full`, its value. Version 3 reads a unique-cause
/// requirement as a pair obligation (module docs, "Pair obligations"), which a pair of cases
/// may discharge together, where version 2 read its covering list as single dischargers and
/// could call both cases of its only pair redundant: its entries of a `redundant` case's
/// `obligations` and `unknown` name the pairs that hold without the case (`pairs`, each
/// `{held, refuted}`) in place of `others` and `dischargers`, and a kept case's reason may be
/// `unknown-partner` (`{reason, family, id, with}`). A corpus whose coverage has no unique-cause
/// requirement gives version 2's document but for its version.
/// Version 4 names the projections of a flow that declares `[[projection]]` (`projections`,
/// [`FlowManifest::projections_value`]), as every kink-flow document does; a flow that declares
/// none gives version 3's document but for its version.
/// Version 5 keeps every case whose entry states that it must be rejected before it runs
/// (classes `rejected` and `accepted`, PJ-32), with the reason `rejected-before-run`
/// (`{reason, class}`), and asks no cell of it; a flow whose entries state no rejection gives
/// version 4's document but for its version.
/// Version 6 reads the `mutations` obligations of a flow that declares `[[projection]]` as
/// (mutation, projection) pairs, one per projection `[run] projections` lists (module docs,
/// "Projections"): each entry and reason naming one has `projection`, and a run row of the
/// record moves where its killer under a projection is removed (`lock`). It reads a grammar
/// mutation's row whole (module docs, "Grammar mutations"), and `expect = { default =
/// "survive" }` in a flow that declares no projection as `expect = "survive"`. A flow that
/// declares no projection and whose list has neither gives version 5's document but for its
/// version.
/// Version 7 prunes several flows that read one corpus root (module docs, "Several flows"): its
/// document names each flow in every entry and reason naming an obligation or keeping a case
/// (`flow`), each case's class per flow (`classes`), each flow's `spec`, `families`,
/// `accounting` and `projections` (`flows`), the order `reverse-flow-manifest`, the scope of the
/// flows given (`flow_only: false`, `flows`) and the limit `flows`; a refusal names its flow
/// (`refused.flow`). A flow named by its manifest alone reads the lists `[mutations] lists`
/// names (`families[].list.declared`). A prune of one flow given its list gives version 6's
/// document but for its version.
pub const PRUNE_VERSION: u64 = 7;

/// The order the removable set is built in (`removable.order`, module docs).
pub const REVERSE_MANIFEST_ORDER: &str = "reverse-manifest";

/// The document's `mode` without `--full`: the rows asked lazily (module docs, "Lazy cells").
pub const LAZY: &str = "lazy";
/// The document's `mode` under `--full`: every cell of every row asked.
pub const FULL: &str = "full";

/// The obligation families, in the order the document lists them.
pub const PRUNE_FAMILIES: [&str; 9] = [
    "mutations",
    "patterns",
    "rules",
    "requirements",
    "syntax",
    "rule_windows",
    "syntax_paths",
    "flips",
    "arguments",
];

/// What the report does not read, each `{limit, detail}` in the document's `limits`.
const LIMITS: [(&str, &str); 5] = [
    (
        "implementation",
        "[[implementation]] compare evidence is universal per case, not an existential: it is \
         not read, and removing a case drops its [compare] rows (lock consequences)",
    ),
    (
        "case-expectation",
        "a case's own expectation is a claim about that case alone, not an existential: it is \
         not read as an obligation; an unmet one keeps its case",
    ),
    (
        "templates",
        "a fuzz template list, whose templates may name a case (`program`), is not read",
    ),
    (
        "flips",
        "a condition flip's kill search stops at its first killer, so its killer is its only \
         decided discharger",
    ),
    (
        "maximal",
        "the removable set is maximal under its order, not minimum: a smallest one is a set \
         cover problem",
    ),
];

/// The limit of a lazy report (`limits`, module docs "Lazy cells").
const LAZY_LIMIT: (&str, &str) = (
    "lazy",
    "a cell is asked only where a decision needs it: the evidence (`others`, `unknown`, \
     `unanswered`) holds the cells asked, and `complete` says where that is every cell; the \
     decisions are those of --full, which asks every cell",
);

/// Options of the `prune` command.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct PruneOptions {
    /// The cache directory; default `<directory of FLOW.toml>/.kink-flow`.
    pub cache: Option<PathBuf>,
    /// `--lock FILE`: the corpus record, read for the rows a removal moves and for the order
    /// the searches ask in, never written.
    pub lock: Option<PathBuf>,
    /// `--compile-workers N`, as `run`'s ([`RunOptions::compile_workers`]).
    pub compile_workers: Option<usize>,
    /// `--full`: ask every cell of every row (`run --full`, `query --full`), where `prune`
    /// without it asks a cell only where a decision needs it (module docs, "Lazy cells"). The
    /// decisions are the same either way.
    pub full: bool,
    /// Whether each list the command reads is the corpus's own, as a front end that keeps a
    /// corpus layout states it ([`crate::cli::FlowCommand::set_corpus_lists`]); `None` where
    /// the caller knows no layout, as kink-flow's own command line does.
    pub corpus_lists: Option<CorpusLists>,
}

/// Whether the lists a `prune` reads are its corpus's own ([`PruneOptions::corpus_lists`]).
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct CorpusLists {
    /// The mutation list is the corpus's own (also when the corpus has none and none is named).
    pub mutations: bool,
    /// The patterns are the corpus's own (also when it declares none and none are named).
    pub patterns: bool,
}

/// What one obligation's row states of each case ([`Reading::Obligation`]).
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Cells {
    /// The cases whose decided cell discharges the obligation.
    pub dischargers: Vec<String>,
    /// The cases whose cell is unknown: neither a decided discharge nor a decided non-discharge.
    pub unknown: Vec<String>,
    /// The row says the obligation is discharged and names no case that does: every case's cell
    /// is then read as unknown.
    pub unnamed: bool,
}

/// What a pair obligation's rows state of each case ([`Reading::Pairs`], module docs, "Pair
/// obligations").
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct PairCells {
    /// Each pair that discharges the obligation: the cases of its held side and of its refuted
    /// side, a case of each together discharging it.
    pub pairs: Vec<[Vec<String>; 2]>,
    /// The cases whose row is a decided side, of a pair or not: each may make a pair with what
    /// an unknown cell holds.
    pub sides: Vec<String>,
    /// The cases whose cell is unknown: what they hold may be a side of a pair.
    pub unknown: Vec<String>,
}

/// What a document's row states, read as a fact of the corpus.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Reading {
    /// No obligation: no case of any corpus can discharge it.
    None,
    /// An existential obligation of the corpus, with its cells.
    Obligation(Cells),
    /// An existential obligation that a pair of cases discharges together (a unique-cause
    /// requirement), with its pairs and cells.
    Pairs(PairCells),
    /// A universal claim that the listed cases' decided cells refute: a finding each of them is
    /// evidence of.
    Refuted(Vec<String>),
}

/// Where a cell of an obligation not yet asked is asked: the list's mutation, or the selected
/// pattern, at this index.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Source {
    Mutation(usize),
    Pattern(usize),
}

/// One cell, as the report reads it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Cell {
    /// A decided discharge.
    Discharges,
    /// A decided non-discharge.
    Not,
    /// Neither.
    Unknown,
}

/// One asked cell: a pattern's, or a mutation's under the run's own slots (`cell`) and under each
/// projection `run` lists (`projections`, by name; empty in a flow that declares none).
#[derive(Clone, Debug, Eq, PartialEq)]
struct Answer {
    cell: Cell,
    projections: Vec<(String, Cell)>,
}

/// Why a cell could not be asked: the family and the detail of its refusal.
type Refusal = (&'static str, String);

/// The commands a lazy report asks its cells through.
trait Ask {
    /// The cell of `source` on the case at `case`, and whether a cache served it.
    fn ask(&mut self, source: Source, case: usize) -> Result<(Answer, bool), Refusal>;
    /// A progress line.
    fn announce(&self, line: &str);
    /// The run's `outcome_cache` and `baseline_runs` and the query's `pattern_cache` as they
    /// stand (null for a family that did not run).
    fn caches(&self) -> [Value; 3];
}

/// A report of complete rows asks nothing (`--full`): the documents' `outcome_cache`,
/// `baseline_runs` and `pattern_cache`.
struct Complete([Value; 3]);

impl Ask for Complete {
    fn ask(&mut self, _: Source, _: usize) -> Result<(Answer, bool), Refusal> {
        Err((
            "mutations",
            "a complete row has no cell left to ask".to_owned(),
        ))
    }

    fn announce(&self, _: &str) {}

    fn caches(&self) -> [Value; 3] {
        self.0.clone()
    }
}

/// The open search of each family a lazy report asks its cells through.
struct Askers<'c, 'k, 'h> {
    cases: &'c [String],
    kills: Option<&'k mut dyn KillCells>,
    hits: Option<&'h mut dyn HitCells>,
    progress: Option<&'c (dyn Fn(&str) + Sync)>,
}

impl Ask for Askers<'_, '_, '_> {
    fn ask(&mut self, source: Source, case: usize) -> Result<(Answer, bool), Refusal> {
        match source {
            Source::Mutation(index) => {
                let kills = self
                    .kills
                    .as_deref_mut()
                    .ok_or_else(|| ("mutations", "no search asks the mutations".to_owned()))?;
                let (cell, projections, cached) = kills
                    .cell(index, &self.cases[case])
                    .map_err(|row| ("mutations", row_refusal(&row)))?;
                let of = |cell: KillCell| match cell {
                    KillCell::Kill => Cell::Discharges,
                    KillCell::Agree => Cell::Not,
                    KillCell::Unknown => Cell::Unknown,
                };
                Ok((
                    Answer {
                        cell: of(cell),
                        projections: projections
                            .into_iter()
                            .map(|(name, cell)| (name, of(cell)))
                            .collect(),
                    },
                    cached,
                ))
            }
            Source::Pattern(index) => {
                let hits = self
                    .hits
                    .as_deref_mut()
                    .ok_or_else(|| ("patterns", "no query asks the patterns".to_owned()))?;
                let (cell, cached) = hits
                    .cell(index, case)
                    .map_err(|row| ("patterns", row_refusal(&row)))?;
                Ok((
                    Answer {
                        cell: match cell {
                            HitCell::Hit => Cell::Discharges,
                            HitCell::No => Cell::Not,
                            HitCell::Unknown => Cell::Unknown,
                        },
                        projections: Vec::new(),
                    },
                    cached,
                ))
            }
        }
    }

    fn announce(&self, line: &str) {
        if let Some(progress) = self.progress {
            progress(line);
        }
    }

    fn caches(&self) -> [Value; 3] {
        [
            self.kills
                .as_deref()
                .map_or(Value::Null, KillCells::outcome_cache),
            self.kills
                .as_deref()
                .map_or(Value::Null, KillCells::baseline_runs),
            self.hits
                .as_deref()
                .map_or(Value::Null, HitCells::pattern_cache),
        ]
    }
}

/// The refusal detail of a row a cell's ask could not decide.
fn row_refusal(row: &Value) -> String {
    let named = |key: &str| row[key].as_str().unwrap_or("?").to_owned();
    format!(
        "asking `{}` of `{}` met an error: {}: {}",
        row["id"]
            .as_str()
            .or_else(|| row["pattern"].as_str())
            .unwrap_or("?"),
        row["program"].as_str().unwrap_or("its program"),
        row["reason"]
            .as_str()
            .or_else(|| row["answer"].as_str())
            .unwrap_or("error"),
        row["detail"]
            .as_str()
            .or_else(|| row["cause"].as_str())
            .map_or_else(|| named("cache_error"), str::to_owned),
    )
}

/// One obligation, its cells by case index.
struct Obligation {
    family: &'static str,
    id: String,
    /// For a `mutations` obligation of a flow that declares `[[projection]]`, the listed
    /// projection it is under ([`Facts::projections`]; module docs, "Projections").
    projection: Option<usize>,
    /// The known decided dischargers, in manifest order.
    dischargers: Vec<usize>,
    /// The known unknown cells, in manifest order.
    unknown: Vec<usize>,
    /// The cases whose cell was not asked, in the order they are asked; empty for a complete
    /// row.
    unasked: Vec<usize>,
    /// Where an unasked cell is asked.
    source: Option<Source>,
    /// The search that gave the row stopped at its first discharger (a distinguished flip):
    /// the cells after it were never asked, and are read as non-discharge (limit `flips`).
    stopped: bool,
    /// For a pair obligation, its pairs and sides; `dischargers` is then the cases of every
    /// pair's sides, and `unknown` its unknown cells (module docs, "Pair obligations").
    pairing: Option<Pairing>,
}

/// A pair obligation's pairs and sides, by case index ([`PairCells`]).
struct Pairing {
    /// Each pair's held side and refuted side, each in manifest order.
    pairs: Vec<[Vec<usize>; 2]>,
    /// The cases of a decided side, in manifest order.
    sides: Vec<usize>,
}

impl Obligation {
    /// Every cell of the row is known.
    fn complete(&self) -> bool {
        self.unasked.is_empty() && !self.stopped
    }

    /// Whether a decided discharge holds over the cases `kept`, the case at `without` left out:
    /// a known decided discharger among them, or, for a pair obligation, a pair with a case of
    /// each side among them.
    fn holds(&self, kept: &[bool], without: Option<usize>) -> bool {
        let considered = |at: &usize| kept[*at] && Some(*at) != without;
        match &self.pairing {
            None => self.dischargers.iter().any(considered),
            Some(pairing) => pairing
                .pairs
                .iter()
                .any(|[one, other]| one.iter().any(considered) && other.iter().any(considered)),
        }
    }

    /// For a pair obligation, each pair that holds over every case but the one at `at`, as its
    /// sides without `at`, each pair once; `None` for another obligation.
    fn pairs_without(&self, at: usize) -> Option<Vec<[Vec<usize>; 2]>> {
        let pairing = self.pairing.as_ref()?;
        let mut pairs = Vec::new();
        for sides in &pairing.pairs {
            let [one, other] = sides.clone().map(|mut side| {
                side.retain(|case| *case != at);
                side
            });
            if !one.is_empty()
                && !other.is_empty()
                && !pairs.contains(&[one.clone(), other.clone()])
            {
                pairs.push([one, other]);
            }
        }
        Some(pairs)
    }
}

/// Why a case is kept, against a set of kept cases.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Keep {
    /// A pattern's `programs` names it.
    Claimed(String),
    /// Its decided cell refutes a universal claim (family, id, and the listed projection the
    /// claim is under, if any).
    Refutes(&'static str, String, Option<usize>),
    /// It is the only kept decided discharger of the obligation at this index (a pair
    /// obligation: no kept decided pair holds without it).
    Sole(usize),
    /// Its cell is unknown on the obligation at this index, which no kept case discharges.
    Unknown(usize),
    /// Its decided row is a side of the pair obligation at this index, which no kept pair
    /// discharges, while these kept cases' cells are unknown: what one holds may make a pair
    /// with it.
    Partner(usize, Vec<usize>),
    /// Its baseline is undecided (its class), and these obligations have no kept discharger.
    Undecided(String, Vec<usize>),
    /// Its entry states that it must be rejected before it runs (its class, `rejected` or
    /// `accepted`; PJ-32): it discharges no obligation prune reads, and what it is in the corpus
    /// for (the acceptance projection, a grammar mutation) is no obligation prune reads either.
    Rejected(String),
}

/// A family's facts as the commands gave them.
struct Family {
    name: &'static str,
    /// `None` when computed; else the reason token and its detail.
    skipped: Option<(&'static str, String)>,
}

/// What a family's cells cost (`accounting.cells`): the matrix's size, the cells the ordinary
/// search held, and the cells asked one at a time after it, of which a cache served
/// `from_cache`.
#[derive(Clone, Copy, Debug, Default)]
struct Asked {
    matrix: usize,
    searched: usize,
    asked: usize,
    from_cache: usize,
}

impl Asked {
    fn value(self) -> Value {
        json!({
            "matrix": self.matrix,
            "searched": self.searched,
            "asked": self.asked,
            "from_cache": self.from_cache,
        })
    }
}

/// What a lazy report does with the open first-kill search (`None` without a mutation list).
type WithRun<'f> = dyn FnMut(Option<(&Value, &mut dyn KillCells)>) -> (Value, u8) + 'f;
/// What a lazy report does with the open pattern walk (`None` without patterns).
type WithQuery<'f> = dyn FnMut(Option<(&Value, &mut dyn HitCells)>) -> (Value, u8) + 'f;

/// What the commands give `prune`, read before its families' searches run.
struct Inputs<'a> {
    manifest: &'a FlowManifest,
    options: &'a PruneOptions,
    front: &'a FrontEnd<'a>,
    locks: &'a [Lock],
    list: Option<&'a MutationList>,
    pattern_list: Option<&'a PatternList>,
    coverage: &'a Value,
    skipped: &'a [Family],
    /// Each family's `list` (`mutations`, `patterns`).
    lists: [Value; 2],
}

impl Inputs<'_> {
    fn announce(&self, line: &str) {
        if let Some(progress) = self.front.progress {
            progress(line);
        }
    }

    fn lock(&self, kind: LockKind) -> Option<&Lock> {
        self.locks.iter().find(|lock| lock.kind == kind)
    }

    fn run_options(&self, schedule: ScheduleMode) -> RunOptions {
        RunOptions {
            cache: self.options.cache.clone(),
            compile_workers: self.options.compile_workers,
            schedule,
            ..RunOptions::default()
        }
    }

    fn query_options(&self) -> QueryOptions {
        QueryOptions {
            cache: self.options.cache.clone(),
            full: self.options.full,
            no_explain: true,
            ..QueryOptions::default()
        }
    }

    /// The refusal of a family whose own command could not ask its question.
    fn family_refused(&self, family: &str, document: &Value, verb: Verb) -> (Value, u8) {
        let flag = if self.options.full { " --full" } else { "" };
        refused(
            family,
            Some(document),
            &format!("`{}{flag}` shows why", self.front.spelling.command(verb)),
        )
    }

    /// The prune document from the families' documents (each `None` where its family is
    /// skipped), asking further cells through `ask`; the `accounting`'s caches and baseline
    /// runs are as they stand once every cell is asked ([`Ask::caches`]).
    fn report(&self, run: Option<&Value>, query: Option<&Value>, ask: &mut dyn Ask) -> (Value, u8) {
        let claimed = self.pattern_list.map(claims).unwrap_or_default();
        let lazy = !self.options.full;
        let built = Facts::read(self, run, query, claimed, lazy, ask).and_then(|mut facts| {
            let document = facts.document(self.locks, &self.lists, ask)?;
            Ok((facts, document))
        });
        let (facts, mut document) = match built {
            Ok(built) => built,
            Err((family, detail)) => return refused(family, Some(self.coverage), &detail),
        };
        document["spec"] = self.coverage["spec"].clone();
        if let Some(corpus) = &self.manifest.corpus {
            document["scope"] = scope(corpus);
        }
        document["accounting"] = self.accounting(run, query, &facts, ask);
        (document, EXIT_YES)
    }

    /// The document's `accounting`: the caches and baseline runs as they stand once every cell
    /// is asked ([`Ask::caches`]), and what each family's cells cost.
    fn accounting(
        &self,
        run: Option<&Value>,
        query: Option<&Value>,
        facts: &Facts,
        ask: &dyn Ask,
    ) -> Value {
        let [outcome_cache, baseline_runs, pattern_cache] = ask.caches();
        json!({
            "mutations": run.map(|_| json!({
                "outcome_cache": outcome_cache,
                "baseline_runs": baseline_runs,
            })),
            "patterns": query.map(|_| pattern_cache),
            "coverage": {"baseline_runs": self.coverage["baseline_runs"]},
            "cells": {
                "mutations": run.map(|_| facts.cells[0].value()),
                "patterns": query.map(|_| facts.cells[1].value()),
            },
        })
    }

    /// `--full`: `run --full` and `query --full`, each in one pass, and the report of their
    /// complete rows.
    fn full(&self) -> (Value, u8) {
        let (run, query, mut complete) = match self.full_documents() {
            Ok(documents) => documents,
            Err(refusal) => return refusal,
        };
        self.report(run.as_ref(), query.as_ref(), &mut complete)
    }

    /// The documents of `run --full` and `query --full` (each `None` where its family is
    /// skipped), and the asker of their complete rows, or the refusal of a family whose own
    /// command could not ask its question.
    fn full_documents(&self) -> Result<FullDocuments, (Value, u8)> {
        let mut run = None;
        if let Some(list) = self.list {
            self.announce("prune: run --full of the mutation list");
            let (document, ok) = crate::search::run_stored(
                self.manifest,
                list,
                &self.run_options(ScheduleMode::Full),
                RunMode::Search,
                self.front,
                false,
            );
            if completed(crate::cli::run_status(&document), ok) == EXIT_UNASKED {
                return Err(self.family_refused("mutations", &document, Verb::Run));
            }
            run = Some(document);
        }
        let mut query = None;
        if let Some(list) = self.pattern_list {
            self.announce("prune: query --full of the patterns");
            let (document, ok) = crate::query::query_spelled(
                self.manifest,
                list,
                &self.query_options(),
                &self.front.spelling.verb(Verb::Query),
            );
            if completed(crate::cli::query_status(&document), ok) == EXIT_UNASKED {
                return Err(self.family_refused("patterns", &document, Verb::Query));
            }
            query = Some(document);
        }
        let complete = Complete([
            run.as_ref()
                .map_or(Value::Null, |run| run["outcome_cache"].clone()),
            run.as_ref()
                .map_or(Value::Null, |run| run["baseline_runs"].clone()),
            query
                .as_ref()
                .map_or(Value::Null, |query| query["pattern_cache"].clone()),
        ]);
        Ok((run, query, complete))
    }

    /// Without `--full`: the first-kill search of the mutation list and the walk of the
    /// patterns, each kept open while the report asks its further cells (module docs, "Lazy
    /// cells").
    fn lazy(&self) -> (Value, u8) {
        self.with_run(&mut |mut run| {
            self.with_query(&mut |query| {
                let run: Option<(&Value, &mut dyn KillCells)> = match &mut run {
                    Some((document, kills)) => Some((*document, &mut **kills)),
                    None => None,
                };
                self.lazy_report(run, query)
            })
        })
    }

    /// The lazy report of the open searches.
    fn lazy_report(
        &self,
        run: Option<(&Value, &mut dyn KillCells)>,
        query: Option<(&Value, &mut dyn HitCells)>,
    ) -> (Value, u8) {
        let cases = self
            .manifest
            .programs
            .iter()
            .map(|program| program.id.clone())
            .collect::<Vec<_>>();
        let (run, kills) = run.unzip();
        let (query, hits) = query.unzip();
        let mut askers = Askers {
            cases: &cases,
            kills,
            hits,
            progress: self.front.progress,
        };
        self.report(run, query, &mut askers)
    }

    /// `f` of the open first-kill search of the mutation list (`None` without a list), or the
    /// refusal of a search that could not ask its question.
    fn with_run(&self, f: &mut WithRun<'_>) -> (Value, u8) {
        let Some(list) = self.list else {
            return f(None);
        };
        self.announce("prune: run of the mutation list (the first-kill search)");
        // The lock's killers order the search, the mutations' own and each (mutation,
        // projection)'s (decision U2); none is a cell.
        let recorded = self.lock(LockKind::Run).map(|lock| Recorded {
            killers: lock.killers(),
            projections: lock.projection_killers(),
        });
        let mut out = None;
        let (document, _) = crate::search::run_session(
            self.manifest,
            list,
            &self.run_options(ScheduleMode::FirstKill),
            RunMode::Search,
            self.front,
            false,
            Some(recorded.unwrap_or_default()),
            Some(&mut |document, ok, kills| {
                out = Some(
                    if completed(crate::cli::run_status(document), ok) == EXIT_UNASKED {
                        self.family_refused("mutations", document, Verb::Run)
                    } else {
                        f(Some((document, kills)))
                    },
                );
            }),
        );
        out.unwrap_or_else(|| self.family_refused("mutations", &document, Verb::Run))
    }

    /// `f` of the open walk of the patterns (`None` without patterns), or the refusal of a
    /// query that could not ask its question.
    fn with_query(&self, f: &mut WithQuery<'_>) -> (Value, u8) {
        let Some(list) = self.pattern_list else {
            return f(None);
        };
        self.announce("prune: query of the patterns (each walk to its first hit)");
        let recorded = self
            .lock(LockKind::Query)
            .map(Lock::witnesses)
            .unwrap_or_default();
        let mut out = None;
        let (document, _) = crate::query::query_session(
            self.manifest,
            list,
            &self.query_options(),
            &recorded,
            &mut |document, ok, hits| {
                out = Some(
                    if completed(crate::cli::query_status(document), ok) == EXIT_UNASKED {
                        self.family_refused("patterns", document, Verb::Query)
                    } else {
                        f(Some((document, hits)))
                    },
                );
            },
        );
        out.unwrap_or_else(|| self.family_refused("patterns", &document, Verb::Query))
    }
}

/// `kink-flow prune`: the prune document and the exit status, [`EXIT_YES`] when the report is
/// computed (unknowns make it conservative, never unanswered: every set it states holds), and
/// [`EXIT_UNASKED`] when a lock does not decode, a list does not decode, or a family's own command
/// could not ask its question (its exit status would be 2: a refused specification, program,
/// mutation or pattern, a corpus or infrastructure error, also one a cell asked lazily met),
/// whose document the refusal names. No status is 1: the report refutes nothing. Every document
/// names the projections the flow declares (`projections`, [`FlowManifest::projections_value`]),
/// a refused one's too: each family's facts are read from the records the projections keep.
#[must_use]
pub fn command(
    manifest: &FlowManifest,
    mutations: Option<&Path>,
    patterns: Option<&Path>,
    options: &PruneOptions,
    front: &FrontEnd<'_>,
) -> (Value, u8) {
    let (mut document, status) = asked(
        manifest,
        Lists::Operand(mutations),
        patterns,
        options,
        front,
    );
    if let Some(projections) = manifest.projections_value() {
        document["projections"] = projections;
    }
    (document, status)
}

/// One flow of a prune over flows named by their manifests ([`flows_command`]): its manifest as
/// the command line gives it, the manifest bound, and its front end.
pub struct PruneFlow<'a> {
    pub path: String,
    pub manifest: &'a FlowManifest,
    pub front: &'a FrontEnd<'a>,
}

/// The removal order of a prune of several flows (`removable.order`, module docs, "Several
/// flows"): the cases of the flows in the order given, each flow's in manifest order after the
/// cases of the flows before it, walked latest first.
pub const REVERSE_FLOW_MANIFEST_ORDER: &str = "reverse-flow-manifest";

/// The limit of a prune of several flows (`limits`, module docs, "Several flows").
const FLOWS_LIMIT: (&str, &str) = (
    "flows",
    "the report holds for the flows given: a flow not given may read a case and be its only \
     discharger; the removal order keeps each flow's early cases only where the flows' manifest \
     orders agree",
);

/// `kink-flow prune FLOW.toml...`: the prune of the flows `flows`, each named by its manifest
/// alone and reading the mutation lists it names (`[mutations] lists`) and the patterns it
/// declares (module docs, "Several flows"). One flow gives that flow's document, its lists
/// named in `families` (`list.declared`); several give one document over every case of their
/// corpus root, each obligation, reason and class naming its flow. The exit statuses are
/// [`command`]'s; a refusal of one flow refuses the command and names the flow (`refused.flow`).
#[must_use]
pub fn flows_command(flows: &[PruneFlow<'_>], options: &PruneOptions) -> (Value, u8) {
    if let [flow] = flows {
        let (mut document, status) =
            asked(flow.manifest, Lists::Declared, None, options, flow.front);
        if let Some(projections) = flow.manifest.projections_value() {
            document["projections"] = projections;
        }
        return (document, status);
    }
    let (mut document, status) = several(flows, options);
    if !document["refused"].is_null() {
        document["flows"] = json!(flows.iter().map(|flow| &flow.path).collect::<Vec<_>>());
    }
    (document, status)
}

/// `refusal` naming the flow `path` (`refused.flow`), unless a flow is already named.
fn flow_refused((mut document, status): (Value, u8), path: &str) -> (Value, u8) {
    if document["refused"].is_object() && document["refused"]["flow"].is_null() {
        document["refused"]["flow"] = json!(path);
    }
    (document, status)
}

/// Where a program of a flow is read from in the corpus root: the case document's case (its id),
/// or its program text's path; `None` for an inline text or a program of variables, which is
/// no file of the root.
fn origin(program: &crate::manifest::Program) -> Option<String> {
    match (&program.case, &program.source) {
        (Some(_), _) => Some(program.id.clone()),
        (None, Some(kink_corpus::ProgramSource::File(path))) => Some(path.clone()),
        _ => None,
    }
}

/// Why `flows` cannot be pruned together, if they cannot: a flow that names no corpus root, two
/// roots that are not one directory, or a case identity two flows disagree on (one id read from
/// two places, or one file of the root read under different ids).
fn shared_root(flows: &[PruneFlow<'_>]) -> Result<(), (String, String)> {
    let mut root = None::<(PathBuf, &str)>;
    for flow in flows {
        let Some(corpus) = &flow.manifest.corpus else {
            return Err((
                flow.path.clone(),
                "the flow names no corpus root ([corpus] root): its cases are in its own \
                 directory, so it shares none with another flow"
                    .to_owned(),
            ));
        };
        let directory = flow
            .manifest
            .case_root()
            .canonical()
            .map_err(|error| {
                (
                    flow.path.clone(),
                    format!(
                        "the corpus root `{}` cannot be resolved: {error}",
                        corpus.root
                    ),
                )
            })?
            .directory;
        match &root {
            None => root = Some((directory, &flow.path)),
            Some((first, path)) if *first != directory => {
                return Err((
                    flow.path.clone(),
                    format!(
                        "it reads its cases from the corpus root `{}`, which is not the corpus \
                         root of `{path}`: the flows of one prune read one corpus root",
                        corpus.root
                    ),
                ));
            }
            Some(_) => {}
        }
    }
    // One case identity: an id names one place, and a file one id, across the flows.
    let mut ids = BTreeMap::<&str, (&str, Option<String>)>::new();
    let mut files = BTreeMap::<String, (&str, Vec<&str>)>::new();
    for flow in flows {
        let mut read = BTreeMap::<String, Vec<&str>>::new();
        for program in &flow.manifest.programs {
            let from = origin(program);
            if let Some(file) = &from {
                read.entry(file.clone()).or_default().push(&program.id);
            }
            match ids.get(program.id.as_str()) {
                Some((first, place)) if from.is_none() || *place != from => {
                    return Err((
                        flow.path.clone(),
                        format!(
                            "its case `{}` is read from {}, and the case of that id of `{first}` \
                             from {}: one id names one case of the corpus root",
                            program.id,
                            from.as_deref()
                                .map_or_else(|| "no file".to_owned(), |file| format!("`{file}`")),
                            place
                                .as_deref()
                                .map_or_else(|| "no file".to_owned(), |file| format!("`{file}`")),
                        ),
                    ));
                }
                Some(_) => {}
                None => {
                    ids.insert(&program.id, (&flow.path, from));
                }
            }
        }
        for (file, mut read_as) in read {
            read_as.sort_unstable();
            match files.get(&file) {
                Some((first, theirs)) if *theirs != read_as => {
                    return Err((
                        flow.path.clone(),
                        format!(
                            "it reads `{file}` as the cases {}, and `{first}` as {}: one file of \
                             the corpus root is read under the same ids by every flow",
                            read_as.join(", "),
                            theirs.join(", ")
                        ),
                    ));
                }
                Some(_) => {}
                None => {
                    files.insert(file, (&flow.path, read_as));
                }
            }
        }
    }
    Ok(())
}

/// The askers of the flows of a prune of several flows, by flow index, with the documents of
/// their families' searches.
trait Asks {
    fn of(&mut self, flow: usize) -> &mut dyn Ask;
    /// The run and query documents of the flow at `flow` (each `None` where its family is
    /// skipped).
    fn documents(&self, flow: usize) -> (Option<Value>, Option<Value>);
}

/// The documents of `run --full` and `query --full` of one flow (each `None` where its family
/// is skipped), and the asker of their complete rows.
type FullDocuments = (Option<Value>, Option<Value>, Complete);

/// The complete rows of `--full`, one flow each.
struct Completes(Vec<FullDocuments>);

impl Asks for Completes {
    fn of(&mut self, flow: usize) -> &mut dyn Ask {
        &mut self.0[flow].2
    }

    fn documents(&self, flow: usize) -> (Option<Value>, Option<Value>) {
        (self.0[flow].0.clone(), self.0[flow].1.clone())
    }
}

/// The open searches of the flows of a lazy prune of several flows: this flow's, and the flows'
/// before it (`outer`).
struct Level<'a> {
    flow: usize,
    here: &'a mut dyn Ask,
    run: Option<&'a Value>,
    query: Option<&'a Value>,
    outer: &'a mut dyn Asks,
}

impl Asks for Level<'_> {
    fn of(&mut self, flow: usize) -> &mut dyn Ask {
        if flow == self.flow {
            self.here
        } else {
            self.outer.of(flow)
        }
    }

    fn documents(&self, flow: usize) -> (Option<Value>, Option<Value>) {
        if flow == self.flow {
            (self.run.cloned(), self.query.cloned())
        } else {
            self.outer.documents(flow)
        }
    }
}

/// No flow's search: the outermost [`Level`]'s `outer`.
struct NoFlow;

impl Asks for NoFlow {
    fn of(&mut self, flow: usize) -> &mut dyn Ask {
        unreachable!("no search of the flow at {flow} is open")
    }

    fn documents(&self, _: usize) -> (Option<Value>, Option<Value>) {
        (None, None)
    }
}

/// What a joint decision runs over: the flows' facts and the cases of their root.
struct Joint {
    facts: Vec<Facts>,
    /// The flows' manifests as given.
    paths: Vec<String>,
    /// The cases in the joint order (module docs, "Several flows").
    cases: Vec<String>,
    /// For each flow, the joint index of each of its cases.
    of: Vec<Vec<usize>>,
    /// For each case, the flows that read it and its index in each.
    readers: Vec<Vec<(usize, usize)>>,
}

impl Joint {
    fn new(facts: Vec<Facts>, paths: Vec<String>) -> Self {
        let mut cases = Vec::<String>::new();
        let mut index = BTreeMap::<String, usize>::new();
        let mut of = Vec::new();
        let mut readers = Vec::<Vec<(usize, usize)>>::new();
        for (flow, facts) in facts.iter().enumerate() {
            let mut joint = Vec::new();
            for (at, case) in facts.cases.iter().enumerate() {
                let j = *index.entry(case.clone()).or_insert_with(|| {
                    cases.push(case.clone());
                    readers.push(Vec::new());
                    cases.len() - 1
                });
                readers[j].push((flow, at));
                joint.push(j);
            }
            of.push(joint);
        }
        Self {
            facts,
            paths,
            cases,
            of,
            readers,
        }
    }

    /// Why the case at `j` is kept against the kept cases `kept`, by the flows that read it, each
    /// reason with its flow; empty when no flow keeps it. A flow that does not read the case has
    /// no cell of it, so it keeps it for none of its obligations.
    fn keeps(
        &mut self,
        j: usize,
        kept: &[bool],
        asks: &mut dyn Asks,
    ) -> Result<Vec<(usize, Keep)>, (usize, Refusal)> {
        let mut keeps = Vec::new();
        for (flow, at) in self.readers[j].clone() {
            let theirs = self.of[flow].iter().map(|j| kept[*j]).collect::<Vec<_>>();
            let found = self.facts[flow]
                .keeps(at, &theirs, asks.of(flow))
                .map_err(|refusal| (flow, refusal))?;
            keeps.extend(found.into_iter().map(|keep| (flow, keep)));
        }
        Ok(keeps)
    }

    fn values(&self, keeps: &[(usize, Keep)]) -> Vec<Value> {
        keeps
            .iter()
            .map(|(flow, keep)| self.facts[*flow].keep_value(keep))
            .collect()
    }

    fn classes(&self, j: usize) -> Value {
        json!(
            self.readers[j]
                .iter()
                .map(|(flow, at)| json!({
                    "flow": self.paths[*flow],
                    "class": self.facts[*flow].classes[*at],
                }))
                .collect::<Vec<_>>()
        )
    }

    /// The document of the joint decisions: the redundant cases, one set removable together in
    /// the joint order, and why each other case is kept, every entry naming its flow.
    fn document(&mut self, asks: &mut dyn Asks) -> Result<Value, (usize, Refusal)> {
        let all = vec![true; self.cases.len()];
        let mut alone = Vec::with_capacity(self.cases.len());
        for j in 0..self.cases.len() {
            alone.push(self.keeps(j, &all, asks)?);
        }
        let mut kept = all.clone();
        let mut kept_for = vec![Vec::new(); self.cases.len()];
        for j in (0..self.cases.len()).rev() {
            if !alone[j].is_empty() {
                continue;
            }
            let keeps = self.keeps(j, &kept, asks)?;
            if keeps.is_empty() {
                kept[j] = false;
            } else {
                kept_for[j] = keeps;
            }
        }
        let each = |j: usize, value: &dyn Fn(&Facts, usize) -> Vec<Value>| {
            self.readers[j]
                .iter()
                .flat_map(|(flow, at)| value(&self.facts[*flow], *at))
                .collect::<Vec<_>>()
        };
        let redundant = (0..self.cases.len())
            .filter(|j| alone[*j].is_empty())
            .map(|j| {
                json!({
                    "case": self.cases[j],
                    "classes": self.classes(j),
                    "obligations": each(j, &Facts::discharged_values),
                    "unknown": each(j, &Facts::unknown_values),
                    "unasked": self.readers[j]
                        .iter()
                        .map(|(flow, at)| self.facts[*flow].unasked(*at))
                        .sum::<usize>(),
                    "removable": !kept[j],
                    "kept_for": self.values(&kept_for[j]),
                    "lock": null,
                })
            })
            .collect::<Vec<_>>();
        let kept_cases = (0..self.cases.len())
            .filter(|j| !alone[*j].is_empty())
            .map(|j| {
                json!({
                    "case": self.cases[j],
                    "classes": self.classes(j),
                    "reasons": self.values(&alone[j]),
                })
            })
            .collect::<Vec<_>>();
        let paths = &self.paths;
        let undecided = self
            .facts
            .iter()
            .enumerate()
            .flat_map(|(flow, facts)| {
                (0..facts.cases.len())
                    .filter(|at| facts.undecided(*at))
                    .map(move |at| {
                        json!({
                            "case": facts.cases[at],
                            "flow": paths[flow],
                            "class": facts.classes[at],
                        })
                    })
            })
            .collect::<Vec<_>>();
        let obligations = || self.facts.iter().flat_map(|facts| facts.obligations.iter());
        let lazy = self.facts.iter().any(|facts| facts.lazy);
        let mut document = header();
        document["mode"] = json!(if lazy { LAZY } else { FULL });
        document["cases"] = json!(self.cases.len());
        document["redundant"] = json!(redundant);
        document["removable"] = json!({
            "order": REVERSE_FLOW_MANIFEST_ORDER,
            "cases": (0..self.cases.len())
                .filter(|j| !kept[*j])
                .map(|j| self.cases[j].clone())
                .collect::<Vec<_>>(),
            "lock": [],
        });
        document["kept"] = json!(kept_cases);
        document["unanswered"] = json!({
            "cells": obligations().map(|o| o.unknown.len()).sum::<usize>(),
            "complete": obligations().all(Obligation::complete),
            "undecided_cases": undecided,
        });
        document["lock"] = Value::Null;
        document["limits"] = json!(
            LIMITS
                .iter()
                .chain(lazy.then_some(&LAZY_LIMIT))
                .chain(std::iter::once(&FLOWS_LIMIT))
                .map(|(limit, detail)| json!({"limit": limit, "detail": detail}))
                .collect::<Vec<_>>()
        );
        Ok(document)
    }
}

/// The prune of several flows ([`flows_command`]).
fn several(flows: &[PruneFlow<'_>], options: &PruneOptions) -> (Value, u8) {
    // A record is one definition's, and a cache directory beside one flow: each flow reads its
    // own default cache and no record.
    if options.lock.is_some() {
        return refused(
            "lock",
            None,
            "a corpus record is the record of one flow's definition, so a prune of several \
             flows reads none",
        );
    }
    if options.cache.is_some() {
        return refused(
            "cache",
            None,
            "a prune of several flows reads each flow's own cache (.kink-flow beside its \
             manifest)",
        );
    }
    if let Err((flow, detail)) = shared_root(flows) {
        return flow_refused(refused("flows", None, &detail), &flow);
    }
    let mut prepared = Vec::with_capacity(flows.len());
    for flow in flows {
        match prepare(flow.manifest, Lists::Declared, None, options, flow.front) {
            Ok(one) => prepared.push(one),
            Err(refusal) => return flow_refused(refusal, &flow.path),
        }
    }
    let inputs = flows
        .iter()
        .zip(&prepared)
        .map(|(flow, prepared)| prepared.inputs(flow.manifest, options, flow.front))
        .collect::<Vec<_>>();
    let paths = flows
        .iter()
        .map(|flow| flow.path.clone())
        .collect::<Vec<_>>();
    if options.full {
        let mut completes = Vec::with_capacity(inputs.len());
        for (inputs, path) in inputs.iter().zip(&paths) {
            match inputs.full_documents() {
                Ok(documents) => completes.push(documents),
                Err(refusal) => return flow_refused(refusal, path),
            }
        }
        joint(&inputs, &paths, &mut Completes(completes), false)
    } else {
        nest(&inputs, &paths, 0, &mut NoFlow)
    }
}

/// Open the searches of the flow at `at` and of every later flow (module docs, "Several
/// flows"), then decide over them all.
fn nest(inputs: &[Inputs<'_>], paths: &[String], at: usize, outer: &mut dyn Asks) -> (Value, u8) {
    let Some(flow) = inputs.get(at) else {
        return joint(inputs, paths, outer, true);
    };
    let cases = flow
        .manifest
        .programs
        .iter()
        .map(|program| program.id.clone())
        .collect::<Vec<_>>();
    let decided = flow.with_run(&mut |mut run| {
        flow.with_query(&mut |query| {
            let run: Option<(&Value, &mut dyn KillCells)> = match &mut run {
                Some((document, kills)) => Some((*document, &mut **kills)),
                None => None,
            };
            let (run, kills) = run.unzip();
            let (query, hits) = query.unzip();
            let mut askers = Askers {
                cases: &cases,
                kills,
                hits,
                progress: flow.front.progress,
            };
            let mut level = Level {
                flow: at,
                here: &mut askers,
                run,
                query,
                outer: &mut *outer,
            };
            nest(inputs, paths, at + 1, &mut level)
        })
    });
    flow_refused(decided, &paths[at])
}

/// The document of the joint decisions over the flows' facts, read from `asks`' documents.
fn joint(inputs: &[Inputs<'_>], paths: &[String], asks: &mut dyn Asks, lazy: bool) -> (Value, u8) {
    let mut facts = Vec::with_capacity(inputs.len());
    let mut documents = Vec::with_capacity(inputs.len());
    for (flow, one) in inputs.iter().enumerate() {
        let (run, query) = asks.documents(flow);
        let claimed = one.pattern_list.map(claims).unwrap_or_default();
        match Facts::read(
            one,
            run.as_ref(),
            query.as_ref(),
            claimed,
            lazy,
            asks.of(flow),
        ) {
            Ok(mut read) => {
                read.flow = Some(paths[flow].clone());
                facts.push(read);
            }
            Err((family, detail)) => {
                return flow_refused(refused(family, Some(one.coverage), &detail), &paths[flow]);
            }
        }
        documents.push((run, query));
    }
    let mut joint = Joint::new(facts, paths.to_vec());
    let mut document = match joint.document(asks) {
        Ok(document) => document,
        Err((flow, (family, detail))) => {
            return flow_refused(
                refused(family, Some(inputs[flow].coverage), &detail),
                &paths[flow],
            );
        }
    };
    document["flows"] = json!(
        inputs
            .iter()
            .enumerate()
            .map(|(flow, one)| {
                let facts = &joint.facts[flow];
                let (run, query) = &documents[flow];
                let mut value = json!({
                    "flow": paths[flow],
                    "spec": one.coverage["spec"],
                    "families": facts.families_value(&one.lists),
                    "accounting": one.accounting(run.as_ref(), query.as_ref(), facts, asks.of(flow)),
                    "unanswered": {
                        "cells": facts.obligations.iter().map(|o| o.unknown.len()).sum::<usize>(),
                        "complete": facts.obligations.iter().all(Obligation::complete),
                    },
                });
                if let Some(projections) = one.manifest.projections_value() {
                    value["projections"] = projections;
                }
                value
            })
            .collect::<Vec<_>>()
    );
    document["scope"] = json!({
        "flow_only": false,
        "flows": inputs
            .iter()
            .enumerate()
            .map(|(flow, one)| json!({
                "flow": paths[flow],
                "corpus_root": one.manifest.corpus.as_ref().map(|corpus| &corpus.root),
            }))
            .collect::<Vec<_>>(),
        "detail": format!(
            "the report holds for the flows given, {}, which read one corpus root: a flow not \
             given may read a case and be its only discharger",
            paths
                .iter()
                .map(|path| format!("`{path}`"))
                .collect::<Vec<_>>()
                .join(", ")
        ),
    });
    (document, EXIT_YES)
}

/// Where a flow's mutation list comes from: the command line's operand (`None`: a front end's
/// layout with none, which skips the family), or the lists its manifest names (`[mutations]
/// lists`, [`FlowManifest::mutation_lists`]; module docs, "Several flows").
#[derive(Clone, Copy, Debug)]
enum Lists<'a> {
    Operand(Option<&'a Path>),
    Declared,
}

/// What one flow's `prune` reads before its families' searches run ([`Inputs`]).
struct Prepared {
    locks: Vec<Lock>,
    list: Option<MutationList>,
    pattern_list: Option<PatternList>,
    coverage: Value,
    skipped: Vec<Family>,
    lists: [Value; 2],
}

impl Prepared {
    fn inputs<'a>(
        &'a self,
        manifest: &'a FlowManifest,
        options: &'a PruneOptions,
        front: &'a FrontEnd<'a>,
    ) -> Inputs<'a> {
        Inputs {
            manifest,
            options,
            front,
            locks: &self.locks,
            list: self.list.as_ref(),
            pattern_list: self.pattern_list.as_ref(),
            coverage: &self.coverage,
            skipped: &self.skipped,
            lists: self.lists.clone(),
        }
    }
}

/// [`command`] without the projections.
fn asked(
    manifest: &FlowManifest,
    mutations: Lists<'_>,
    patterns: Option<&Path>,
    options: &PruneOptions,
    front: &FrontEnd<'_>,
) -> (Value, u8) {
    let prepared = match prepare(manifest, mutations, patterns, options, front) {
        Ok(prepared) => prepared,
        Err(refusal) => return refusal,
    };
    let inputs = prepared.inputs(manifest, options, front);
    if options.full {
        inputs.full()
    } else {
        inputs.lazy()
    }
}

/// The mutation list of the lists `manifest` names ([`FlowManifest::mutation_lists`]), each
/// read as a list operand is, their mutations in the order the lists are named; an id two lists
/// give is refused, since an obligation is named by its mutation's id.
fn declared_list(manifest: &FlowManifest) -> Result<MutationList, String> {
    if manifest.mutation_lists.is_empty() {
        return Err(
            "the flow names no mutation list: a flow that prune is given by its manifest alone \
             reads the lists its [mutations] lists names, and a K flow has no default list"
                .to_owned(),
        );
    }
    let mut mutations = Vec::<crate::mutation::Mutation>::new();
    let mut from = BTreeMap::<String, &str>::new();
    for path in &manifest.mutation_lists {
        let list = MutationList::read(&manifest.directory.join(path))
            .map_err(|error| format!("{path}: {error}"))?;
        for mutation in list.mutations {
            if let Some(first) = from.get(&mutation.id) {
                return Err(format!(
                    "the mutation id `{}` is given by {first} and by {path}: an obligation is \
                     named by its mutation's id, so the lists a flow names give each id once",
                    mutation.id
                ));
            }
            from.insert(mutation.id.clone(), path);
            mutations.push(mutation);
        }
    }
    Ok(MutationList { mutations })
}

/// What `prune` of one flow reads before its families' searches run: the lock, the lists and the
/// coverage, or the refusal of the command.
fn prepare(
    manifest: &FlowManifest,
    mutations: Lists<'_>,
    patterns: Option<&Path>,
    options: &PruneOptions,
    front: &FrontEnd<'_>,
) -> Result<Prepared, (Value, u8)> {
    let mut locks = Vec::new();
    if let Some(path) = &options.lock {
        for kind in [
            LockKind::Run,
            LockKind::Coverage,
            LockKind::Compare,
            LockKind::Query,
        ] {
            // The record of another definition holds none of this flow's rows.
            let read = Lock::read_kind(path, kind)
                .and_then(|lock| lock.for_definition(manifest.definition.as_deref()));
            match read {
                Ok(lock) => locks.push(lock),
                Err(detail) => return Err(refused("lock", None, &detail)),
            }
        }
    }
    // Every input is decoded before anything runs: a list that does not decode refuses the
    // command at once.
    let mut skipped = Vec::new();
    let list = match mutations {
        Lists::Operand(mutations) => match mutations.map(MutationList::read).transpose() {
            Ok(list) => list,
            Err(error) => return Err(refused("mutations", None, &error.to_string())),
        },
        Lists::Declared => match declared_list(manifest) {
            Ok(list) => Some(list),
            Err(detail) => return Err(refused("mutations", None, &detail)),
        },
    };
    if list.is_none() {
        skipped.push(Family {
            name: "mutations",
            skipped: Some(("no-mutation-list", "no mutation list was given".to_owned())),
        });
    }
    let pattern_list = if patterns.is_none() && manifest.patterns.is_empty() {
        skipped.push(Family {
            name: "patterns",
            skipped: Some((
                "no-patterns",
                "no pattern list was given and the manifest declares none".to_owned(),
            )),
        });
        None
    } else {
        match crate::pattern::declared_patterns(manifest, patterns, front.krs_patterns) {
            Ok(list) => Some(list),
            Err(error) => return Err(refused("patterns", None, &error.to_string())),
        }
    };
    let lists = match mutations {
        Lists::Operand(mutations) => {
            let own = |pick: fn(&CorpusLists) -> bool| options.corpus_lists.as_ref().map(pick);
            [
                json!({
                    "path": mutations.map(|path| path.display().to_string()),
                    "corpus_own": own(|lists| lists.mutations),
                }),
                json!({
                    "path": patterns.map(|path| path.display().to_string()),
                    "corpus_own": own(|lists| lists.patterns),
                }),
            ]
        }
        // The lists the manifest names and the patterns it declares are the flow's own.
        Lists::Declared => [
            json!({
                "path": null,
                "corpus_own": true,
                "declared": manifest.mutation_lists,
            }),
            json!({"path": null, "corpus_own": true}),
        ],
    };
    if let Some(progress) = front.progress {
        progress("prune: coverage of the corpus");
    }
    let coverage_options = CoverageOptions {
        cache: options.cache.clone(),
        ..CoverageOptions::default()
    };
    let coverage_lock = locks.iter().find(|lock| lock.kind == LockKind::Coverage);
    let (coverage, ok) =
        crate::coverage::coverage_front(manifest, &coverage_options, front, coverage_lock);
    let mut coverage = front.annotated(coverage);
    crate::coverage::derive(&mut coverage, front.spelling);
    if completed(crate::cli::coverage_status(&coverage), ok) == EXIT_UNASKED {
        return Err(refused(
            "coverage",
            Some(&coverage),
            &format!("`{}` shows why", front.spelling.command(Verb::Coverage)),
        ));
    }
    Ok(Prepared {
        locks,
        list,
        pattern_list,
        coverage,
        skipped,
        lists,
    })
}

/// Each claim of `list`: the pattern's id and the case its `programs` names.
fn claims(list: &PatternList) -> Vec<(String, String)> {
    list.patterns
        .iter()
        .flat_map(|entry| {
            entry
                .programs
                .iter()
                .flatten()
                .map(|program| (entry.id.clone(), program.clone()))
        })
        .collect()
}

/// The `scope` of the prune document of a flow that names its corpus root (module documentation,
/// "The scope"): `{flow_only, corpus_root, detail}`.
fn scope(corpus: &crate::manifest::CorpusSection) -> Value {
    json!({
        "flow_only": true,
        "corpus_root": corpus.root,
        "detail": format!(
            "the cases are read from the corpus root `{}`, which other flows may name: the report \
             holds for this flow alone, and a case redundant here may be the only discharger of \
             another flow's obligation",
            corpus.root
        ),
    })
}

/// The header every prune document has.
fn header() -> Value {
    crate::with_z3_build(json!({
        "schema": PRUNE_SCHEMA,
        "version": PRUNE_VERSION,
        "k_rust_revision": crate::k_rust_revision(),
        "profile": SolverProfile::BUILD.name(),
    }))
}

/// The document of a prune that could not ask its question: `refused`, `{family, detail}`, and
/// the family's document's `spec` where it has one; exit [`EXIT_UNASKED`].
fn refused(family: &str, document: Option<&Value>, detail: &str) -> (Value, u8) {
    let mut value = header();
    value["spec"] = document.map_or(Value::Null, |document| document["spec"].clone());
    value["refused"] = json!({"family": family, "detail": detail});
    (value, EXIT_UNASKED)
}

/// The prune document of a manifest that does not decode, under the command's schema.
#[must_use]
pub fn manifest_refused(error: &crate::ManifestError) -> Value {
    let mut document = crate::cli::manifest_refused(error);
    document["schema"] = json!(PRUNE_SCHEMA);
    document["version"] = json!(PRUNE_VERSION);
    document
}

/// The corpus's facts, by case index.
struct Facts {
    /// The cases, in manifest order.
    cases: Vec<String>,
    /// Each case's baseline class.
    classes: Vec<String>,
    obligations: Vec<Obligation>,
    /// Each case's claims and refutations.
    keeps: Vec<Vec<Keep>>,
    /// Each family, computed or skipped.
    families: Vec<Family>,
    /// Whether the rows were read lazily (the document's `mode`).
    lazy: bool,
    /// What the `mutations` and the `patterns` cells cost.
    cells: [Asked; 2],
    /// The projections `run` lists (`[run] projections`) in a flow that declares
    /// `[[projection]]`, in listed order; empty in a flow that declares none (module docs,
    /// "Projections").
    projections: Vec<Listed>,
    /// Each cell asked one at a time, by source and case: one ask of a mutation's cell answers
    /// it under every listed projection.
    answers: BTreeMap<(Source, usize), Answer>,
    /// In a prune of several flows, this flow's manifest as given, which every entry and reason
    /// naming one of its obligations or keeping one of its cases names (`flow`); `None` for a
    /// prune of one flow (module docs, "Several flows").
    flow: Option<String>,
}

/// A projection `run` lists, as the `mutations` obligations under it read it.
struct Listed {
    name: String,
    /// It is judged as the run's own and has no `domain` ([`Judge::Run`]): its status is the
    /// row's, and its cells are the row's own.
    own: bool,
    /// Whether its `domain` holds each case, in manifest order: a case outside it has no cell
    /// under it.
    domain: Vec<bool>,
}

/// Insert `at` into the sorted `into`, once.
fn insert(into: &mut Vec<usize>, at: usize) {
    if let Err(place) = into.binary_search(&at) {
        into.insert(place, at);
    }
}

impl Facts {
    /// The index of the case `id`.
    fn index(&self, id: &str) -> Option<usize> {
        self.cases.iter().position(|case| case == id)
    }

    /// The indices of the cases `ids`, sorted, once each.
    fn indices(&self, ids: &[String]) -> Vec<usize> {
        let mut found = ids
            .iter()
            .filter_map(|id| self.index(id))
            .collect::<Vec<_>>();
        found.sort_unstable();
        found.dedup();
        found
    }

    /// Add what `reading` states of the row `id` of `family`, under the listed projection
    /// `projection` (a `mutations` row of a flow that declares projections).
    fn add(
        &mut self,
        family: &'static str,
        id: &Value,
        reading: Reading,
        projection: Option<usize>,
    ) {
        match reading {
            Reading::None => {}
            Reading::Refuted(by) => {
                for at in self.indices(&by) {
                    self.keeps[at].push(Keep::Refutes(family, text(id), projection));
                }
            }
            Reading::Obligation(cells) => {
                let (dischargers, unknown) = if cells.unnamed {
                    (Vec::new(), (0..self.cases.len()).collect())
                } else {
                    let dischargers = self.indices(&cells.dischargers);
                    let mut unknown = self.indices(&cells.unknown);
                    unknown.retain(|at| !dischargers.contains(at));
                    (dischargers, unknown)
                };
                self.obligations.push(Obligation {
                    family,
                    id: text(id),
                    projection,
                    dischargers,
                    unknown,
                    unasked: Vec::new(),
                    source: None,
                    stopped: false,
                    pairing: None,
                });
            }
            Reading::Pairs(cells) => {
                let pairs = cells
                    .pairs
                    .iter()
                    .map(|sides| sides.each_ref().map(|side| self.indices(side)))
                    .filter(|[one, other]| !one.is_empty() && !other.is_empty())
                    .collect::<Vec<_>>();
                let mut dischargers = Vec::new();
                for at in pairs.iter().flatten().flatten() {
                    insert(&mut dischargers, *at);
                }
                // A case on a pair's side may still hold a side its rows do not show, so
                // its unknown cell stays one (module docs, "Pair obligations").
                let unknown = self.indices(&cells.unknown);
                let sides = self.indices(&cells.sides);
                self.obligations.push(Obligation {
                    family,
                    id: text(id),
                    projection,
                    dischargers,
                    unknown,
                    unasked: Vec::new(),
                    source: None,
                    stopped: false,
                    pairing: Some(Pairing { pairs, sides }),
                });
            }
        }
    }

    /// The `mutations` obligation of the run's `row` (the list's mutation at `mutation`, when
    /// the list has it): the row's own (`projection` `None`, a flow that declares no projection
    /// or a row whose `expect = "survive"` its killers refute), or the one under the listed
    /// projection at `projection`. A lazy report reads a row with a known killer as the search
    /// left it, its cells not judged asked as decisions need them (module docs, "Lazy cells");
    /// every other row is read whole. A row whose claim of survival its killers refute is asked
    /// whole, and each of its killers is kept for it.
    fn read_mutation(
        &mut self,
        row: &Value,
        mutation: Option<usize>,
        projection: Option<usize>,
        comparable: &[bool],
        ask: &mut dyn Ask,
    ) -> Result<(), Refusal> {
        let listed = projection.map(|at| &self.projections[at]);
        let name = listed.map(|listed| listed.name.clone());
        let own = listed.is_none_or(|listed| listed.own);
        // The comparable cases of the projection's domain: the cases a cell under it is of.
        let domain = (0..self.cases.len())
            .filter(|at| comparable[*at] && listed.is_none_or(|listed| listed.domain[*at]))
            .collect::<Vec<_>>();
        let survive = match &name {
            None => crate::report::expects_survival(row),
            Some(name) => row["expect"][name] == Expect::Survive.as_str(),
        };
        // A grammar mutation's row is read whole (module docs, "Grammar mutations").
        if row["grammar"].is_array() {
            let reading = crate::report::grammar_kill_cells(row);
            self.add("mutations", &row["id"], reading, projection);
            return Ok(());
        }
        let lazy = match mutation.filter(|_| self.lazy) {
            Some(mutation) if own && row["status"] == "killed" => {
                Some(self.lazy_killed(row, mutation, comparable))
            }
            Some(mutation) if !own => {
                self.lazy_projected(row, mutation, projection, name.as_deref(), &domain)
            }
            _ => None,
        };
        let Some(mut obligation) = lazy else {
            let reading = match &name {
                None => crate::report::kill_cells(row),
                Some(name) => crate::report::projection_kill_cells(
                    row,
                    name,
                    (!own).then(|| self.ids(domain.iter().copied())).as_deref(),
                ),
            };
            self.add("mutations", &row["id"], reading, projection);
            return Ok(());
        };
        obligation.projection = projection;
        self.obligations.push(obligation);
        if survive {
            // Every killer refutes the claim: the row is asked whole.
            let at = self.obligations.len() - 1;
            self.learn_all(at, ask)?;
            let obligation = self.obligations.pop().expect("just pushed");
            for case in obligation.dischargers {
                self.keeps[case].push(Keep::Refutes(
                    "mutations",
                    obligation.id.clone(),
                    projection,
                ));
            }
        }
        Ok(())
    }

    /// The programs that witness the edit of `row`, which the search order asks first.
    fn witnesses(&self, row: &Value) -> Vec<usize> {
        self.indices(
            &row["witnesses"]
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(Value::as_str)
                .map(str::to_owned)
                .collect::<Vec<_>>(),
        )
    }

    /// A killed row of the first-kill search, read lazily under the run's own slots: its killer
    /// and the cells it asked before it; a cached kill it read past the killer is asked again.
    fn lazy_killed(&self, row: &Value, mutation: usize, comparable: &[bool]) -> Obligation {
        let killer = row["killer"].as_str().and_then(|id| self.index(id));
        let mut obligation = Obligation {
            family: "mutations",
            id: text(&row["id"]),
            projection: None,
            dischargers: killer.into_iter().collect(),
            unknown: Vec::new(),
            unasked: Vec::new(),
            source: Some(Source::Mutation(mutation)),
            stopped: false,
            pairing: None,
        };
        let mut known = killer.into_iter().collect::<Vec<_>>();
        for entry in row["executed"].as_array().into_iter().flatten() {
            let Some(at) = entry["program"].as_str().and_then(|id| self.index(id)) else {
                continue;
            };
            match entry["outcome"].as_str() {
                Some("distinguish") => {}
                Some("agree") => insert(&mut known, at),
                _ => {
                    insert(&mut known, at);
                    if Some(at) != killer {
                        insert(&mut obligation.unknown, at);
                    }
                }
            }
        }
        // The search order: the programs that witness the edit first, each group in
        // manifest order.
        let witnesses = self.witnesses(row);
        obligation.unasked = (0..self.cases.len())
            .filter(|at| comparable[*at] && !known.contains(at))
            .collect();
        obligation.unasked.sort_by_key(|at| !witnesses.contains(at));
        obligation
    }

    /// The row's obligation under the projection `name`, judged per program, read lazily when
    /// some case is known to kill under it (its killer, or a program judged `killed` under it):
    /// the verdicts the run gave under it (the row's `executed` and its `projection_search`'s),
    /// the cases of `domain` (comparable, in the projection's domain) it judged nothing of asked
    /// as decisions need them. `None` where no case is known to kill under it, or the row's
    /// status no program decides (the projection then has the row's): it is read whole.
    fn lazy_projected(
        &self,
        row: &Value,
        mutation: usize,
        projection: Option<usize>,
        name: Option<&str>,
        domain: &[usize],
    ) -> Option<Obligation> {
        let name = name?;
        let executed = row["executed"].as_array().map_or(&[][..], Vec::as_slice);
        if !matches!(
            row["status"].as_str(),
            Some("killed" | "survived" | "unknown")
        ) || executed.is_empty()
        {
            return None;
        }
        let mut verdicts = BTreeMap::new();
        for entry in executed.iter().chain(
            row["projection_search"]["executed"]
                .as_array()
                .into_iter()
                .flatten(),
        ) {
            if let (Some(at), Some(verdict)) = (
                entry["program"].as_str().and_then(|id| self.index(id)),
                entry["projections"][name].as_str(),
            ) && domain.contains(&at)
            {
                verdicts.insert(at, verdict);
            }
        }
        let status = row["projections"]
            .as_array()
            .into_iter()
            .flatten()
            .find(|entry| entry["name"] == name)?;
        let killer = status["killer"]
            .as_str()
            .filter(|_| status["status"] == "killed")
            .and_then(|id| self.index(id))
            .filter(|at| domain.contains(at));
        let mut obligation = Obligation {
            family: "mutations",
            id: text(&row["id"]),
            projection,
            dischargers: killer.into_iter().collect(),
            unknown: Vec::new(),
            unasked: Vec::new(),
            source: Some(Source::Mutation(mutation)),
            stopped: false,
            pairing: None,
        };
        for (at, verdict) in &verdicts {
            match *verdict {
                "killed" => insert(&mut obligation.dischargers, *at),
                "unknown" if Some(*at) != killer => insert(&mut obligation.unknown, *at),
                _ => {}
            }
        }
        if obligation.dischargers.is_empty() {
            return None;
        }
        let witnesses = self.witnesses(row);
        obligation.unasked = domain
            .iter()
            .copied()
            .filter(|at| Some(*at) != killer && !verdicts.contains_key(at))
            .collect();
        obligation.unasked.sort_by_key(|at| !witnesses.contains(at));
        Some(obligation)
    }

    #[allow(clippy::too_many_lines)]
    fn read(
        inputs: &Inputs<'_>,
        run: Option<&Value>,
        query: Option<&Value>,
        claims: Vec<(String, String)>,
        lazy: bool,
        ask: &mut dyn Ask,
    ) -> Result<Self, Refusal> {
        let (manifest, coverage) = (inputs.manifest, inputs.coverage);
        let cases = manifest
            .programs
            .iter()
            .map(|program| program.id.clone())
            .collect::<Vec<_>>();
        let index = |id: &str| cases.iter().position(|case| case == id);
        let rows = coverage["programs"]
            .as_array()
            .map_or(&[][..], Vec::as_slice);
        let classes = cases
            .iter()
            .map(|case| {
                rows.iter()
                    .find(|row| row["id"] == case.as_str())
                    .and_then(|row| row["class"].as_str())
                    .unwrap_or("unknown")
                    .to_owned()
            })
            .collect::<Vec<_>>();
        // The cases a mutant runs on: the comparable ones (`run`'s O). Every other case has no
        // cell of the kill matrix, which reads it as no discharge.
        let comparable = classes
            .iter()
            .map(|class| ResultClass::can_kill(&json!(class)))
            .collect::<Vec<_>>();
        // The cases whose entry states that they must be rejected before they run (PJ-32): no
        // command runs or asks them, so they have no cell of any family, and none is asked.
        let stated = classes
            .iter()
            .map(|class| ResultClass::states_rejection(&json!(class)))
            .collect::<Vec<_>>();
        let mut keeps = vec![Vec::new(); cases.len()];
        for (pattern, case) in claims {
            if let Some(at) = index(&case) {
                keeps[at].push(Keep::Claimed(pattern));
            }
        }
        for (at, class) in classes.iter().enumerate() {
            if stated[at] {
                keeps[at].push(Keep::Rejected(class.clone()));
            }
        }
        // A case's own expectation that its run does not meet.
        for row in rows {
            if row["expectation"]["verdict"] == "unmet"
                && let Some(at) = row["id"].as_str().and_then(index)
            {
                keeps[at].push(Keep::Refutes("expectations", cases[at].clone(), None));
            }
        }
        // The projections `run` lists, in a flow that declares any (module docs, "Projections").
        let projections = if manifest.projections.is_empty() {
            Vec::new()
        } else {
            manifest
                .run_projections()
                .iter()
                .map(|projection| Listed {
                    name: projection.name.clone(),
                    own: projection.domain.is_none()
                        && Judge::of(projection, manifest) == Judge::Run,
                    domain: manifest
                        .programs
                        .iter()
                        .map(|program| projection.holds(program))
                        .collect(),
                })
                .collect()
        };
        let mut facts = Self {
            classes,
            obligations: Vec::new(),
            keeps,
            families: Vec::new(),
            lazy,
            cells: [Asked::default(); 2],
            cases: cases.clone(),
            projections,
            answers: BTreeMap::new(),
            flow: None,
        };
        if let Some(run) = run {
            let comparable_count = comparable.iter().filter(|c| **c).count();
            facts.cells[0].matrix =
                inputs.list.map_or(0, |list| list.mutations.len()) * comparable_count;
            for row in run["mutations"].as_array().into_iter().flatten() {
                // The cells the search held: the programs it ran or read, for the row or for
                // its projections, and each killer.
                let held = row["executed"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .chain(
                        row["projection_search"]["executed"]
                            .as_array()
                            .into_iter()
                            .flatten(),
                    )
                    .filter_map(|entry| entry["program"].as_str().and_then(index))
                    .chain(row["killer"].as_str().and_then(index))
                    .chain(
                        row["projections"]
                            .as_array()
                            .into_iter()
                            .flatten()
                            .filter_map(|entry| entry["killer"].as_str().and_then(index)),
                    )
                    .filter(|at| comparable[*at])
                    .collect::<std::collections::BTreeSet<_>>();
                facts.cells[0].searched += held.len();
                let mutation = inputs.list.and_then(|list| {
                    list.mutations
                        .iter()
                        .position(|mutation| row["id"] == mutation.id.as_str())
                });
                // A flow that declares projections: an obligation per listed projection, but
                // for a row whose claim of survival (on the row's own status) its killers
                // refute, which is no obligation under any (module docs, "Projections").
                if facts.projections.is_empty()
                    || (row["status"] == "killed" && row["expect"] == Expect::Survive.as_str())
                {
                    facts.read_mutation(row, mutation, None, &comparable, ask)?;
                } else {
                    for projection in 0..facts.projections.len() {
                        facts.read_mutation(row, mutation, Some(projection), &comparable, ask)?;
                    }
                }
            }
        }
        if let Some(query) = query {
            // The patterns by the programs a pattern can be asked of: none of a case whose entry
            // states that it must be rejected before it runs.
            facts.cells[1].matrix = inputs.pattern_list.map_or(0, |list| list.patterns.len())
                * stated.iter().filter(|stated| !**stated).count();
            let rows = query["rows"].as_array().map_or(&[][..], Vec::as_slice);
            facts.cells[1].searched = rows.len();
            for obligation in query["obligations"].as_array().into_iter().flatten() {
                let pattern = inputs.pattern_list.and_then(|list| {
                    list.patterns
                        .iter()
                        .position(|entry| obligation["id"] == entry.id.as_str())
                });
                let (true, Some(pattern)) = (lazy && obligation["status"] == "hit", pattern) else {
                    facts.add(
                        "patterns",
                        &obligation["id"],
                        crate::query::hit_cells(obligation),
                        None,
                    );
                    continue;
                };
                // A hit pattern's walk: the pairs it asked (its claims, then the walk to its
                // first hit).
                let mut lazy = Obligation {
                    family: "patterns",
                    id: text(&obligation["id"]),
                    projection: None,
                    dischargers: Vec::new(),
                    unknown: Vec::new(),
                    unasked: Vec::new(),
                    source: Some(Source::Pattern(pattern)),
                    stopped: false,
                    pairing: None,
                };
                let mut known = Vec::new();
                for row in rows.iter().filter(|row| row["pattern"] == obligation["id"]) {
                    let Some(at) = row["program"].as_str().and_then(index) else {
                        continue;
                    };
                    insert(&mut known, at);
                    match row["answer"].as_str() {
                        Some("hit") => insert(&mut lazy.dischargers, at),
                        Some("no") => {}
                        _ => insert(&mut lazy.unknown, at),
                    }
                }
                lazy.unasked = (0..cases.len())
                    .filter(|at| !stated[*at] && !known.contains(at))
                    .collect();
                facts.obligations.push(lazy);
                if obligation["expect"] == PatternExpect::No.as_str() {
                    let at = facts.obligations.len() - 1;
                    facts.learn_all(at, ask)?;
                    let obligation = facts.obligations.pop().expect("just pushed");
                    for case in obligation.dischargers {
                        facts.keeps[case].push(Keep::Refutes(
                            "patterns",
                            obligation.id.clone(),
                            None,
                        ));
                    }
                }
            }
        }
        // The coverage families, each by its own name, which is also its prune family's.
        let rules = coverage["families"]["rules"]["items"]
            .as_array()
            .map_or(&[][..], Vec::as_slice);
        for family in PRUNE_FAMILIES
            .into_iter()
            .filter(|family| FAMILIES.contains(family))
        {
            let value = &coverage["families"][family];
            let binders = value["binders"].as_array().map_or(&[][..], Vec::as_slice);
            for item in value["items"].as_array().into_iter().flatten() {
                let before = facts.obligations.len();
                facts.add(
                    family,
                    &item["id"],
                    crate::coverage::cover_cells(family, item, binders, rules),
                    None,
                );
                if family == "flips"
                    && facts.obligations.len() > before
                    && flip_status(item) == DISTINGUISHED
                {
                    facts.obligations[before].stopped = true;
                }
            }
        }
        for family in FAMILIES {
            for item in coverage["families"][family]["items"]
                .as_array()
                .into_iter()
                .flatten()
            {
                facts.add(
                    "arguments",
                    &item["id"],
                    crate::coverage::argument_cells(item),
                    None,
                );
            }
        }
        facts.families = PRUNE_FAMILIES
            .iter()
            .map(|name| Family {
                name,
                skipped: inputs
                    .skipped
                    .iter()
                    .find(|family| family.name == *name)
                    .and_then(|family| family.skipped.clone())
                    .or_else(|| coverage_skipped(coverage, name)),
            })
            .collect();
        Ok(facts)
    }

    /// Ask the cell of the obligation at `index` on the case at `case`, where it was not asked.
    fn learn(&mut self, index: usize, case: usize, ask: &mut dyn Ask) -> Result<(), Refusal> {
        let obligation = &mut self.obligations[index];
        let Some(place) = obligation.unasked.iter().position(|at| *at == case) else {
            return Ok(());
        };
        obligation.unasked.remove(place);
        let source = obligation
            .source
            .expect("a row with an unasked cell has a source");
        // One ask of a mutation's cell answers it under every listed projection: an answer
        // already asked for another projection is read again, not asked again.
        let cached = match self.answers.get(&(source, case)) {
            Some(_) => None,
            None => {
                let (answer, cached) = ask.ask(source, case)?;
                let counted = match source {
                    Source::Mutation(_) => &mut self.cells[0],
                    Source::Pattern(_) => &mut self.cells[1],
                };
                counted.asked += 1;
                counted.from_cache += usize::from(cached);
                self.answers.insert((source, case), answer);
                Some(cached)
            }
        };
        let answer = &self.answers[&(source, case)];
        let listed = obligation.projection.map(|at| &self.projections[at]);
        let cell = match listed {
            // A case outside the projection's domain has no cell under it.
            Some(listed) if !listed.domain[case] => Cell::Not,
            Some(listed) if !listed.own => answer
                .projections
                .iter()
                .find(|(name, _)| *name == listed.name)
                .map_or(Cell::Unknown, |(_, cell)| *cell),
            _ => answer.cell,
        };
        match cell {
            Cell::Discharges => insert(&mut obligation.dischargers, case),
            Cell::Unknown => insert(&mut obligation.unknown, case),
            Cell::Not => {}
        }
        ask.announce(&format!(
            "prune: {} `{}`{} on `{}`: {}{}",
            obligation.family,
            obligation.id,
            listed.map_or_else(String::new, |listed| format!(" under `{}`", listed.name)),
            self.cases[case],
            match cell {
                Cell::Discharges => "discharges",
                Cell::Not => "does not discharge",
                Cell::Unknown => "unknown",
            },
            match cached {
                Some(true) => " (cached)",
                Some(false) => "",
                None => " (asked for another projection)",
            }
        ));
        Ok(())
    }

    /// Ask every cell of the obligation at `index` not asked yet.
    fn learn_all(&mut self, index: usize, ask: &mut dyn Ask) -> Result<(), Refusal> {
        while let Some(&case) = self.obligations[index].unasked.first() {
            self.learn(index, case, ask)?;
        }
        Ok(())
    }

    /// Make the row of the obligation at `index` decide the case at `at` against the kept cases
    /// `kept` (module docs, "Lazy cells"): when no known decided discharger other than `at` is
    /// kept, ask its unasked cells over the kept cases other than `at`, in its order, until one
    /// discharges or none is left, then `at`'s own.
    fn settle(
        &mut self,
        index: usize,
        at: usize,
        kept: &[bool],
        ask: &mut dyn Ask,
    ) -> Result<(), Refusal> {
        let others = |obligation: &Obligation| obligation.holds(kept, Some(at));
        let obligation = &self.obligations[index];
        if obligation.unasked.is_empty() || others(obligation) {
            return Ok(());
        }
        let order = obligation
            .unasked
            .iter()
            .copied()
            .filter(|case| *case != at && kept[*case])
            .collect::<Vec<_>>();
        for case in order {
            self.learn(index, case, ask)?;
            if others(&self.obligations[index]) {
                return Ok(());
            }
        }
        self.learn(index, at, ask)
    }

    /// Whether the case at `at` has an undecided baseline: kink asked it of no mutant and no
    /// pattern, and covered nothing by it.
    fn undecided(&self, at: usize) -> bool {
        matches!(self.classes[at].as_str(), "timeout" | "unknown")
    }

    /// Why the case at `at` is kept against the kept cases `kept` (`at` itself among them); empty
    /// when it is not (module docs, "What is never prunable"), asking the cells the rules need.
    fn keeps(&mut self, at: usize, kept: &[bool], ask: &mut dyn Ask) -> Result<Vec<Keep>, Refusal> {
        let mut keeps = self.keeps[at].clone();
        let mut open = Vec::new();
        for index in 0..self.obligations.len() {
            self.settle(index, at, kept, ask)?;
            let obligation = &self.obligations[index];
            if obligation.holds(kept, Some(at)) {
                continue;
            }
            // `at` is among `kept`, so a discharge that holds over them now needs it.
            if obligation.holds(kept, None) {
                keeps.push(Keep::Sole(index));
            } else if obligation.unknown.contains(&at) {
                keeps.push(Keep::Unknown(index));
            } else if let Some(pairing) = &obligation.pairing
                && pairing.sides.contains(&at)
            {
                // A decided side may pair with what a kept unknown cell holds, a case of an
                // undecided baseline's included (module docs, "Pair obligations").
                let with = (0..self.cases.len())
                    .filter(|other| {
                        *other != at
                            && kept[*other]
                            && (obligation.unknown.contains(other) || self.undecided(*other))
                    })
                    .collect::<Vec<_>>();
                if !with.is_empty() {
                    keeps.push(Keep::Partner(index, with));
                }
            } else if self.undecided(at) && self.in_domain(obligation, at) {
                open.push(index);
            }
        }
        if !open.is_empty() {
            keeps.push(Keep::Undecided(self.classes[at].clone(), open));
        }
        Ok(keeps)
    }

    /// Whether the case at `at` has a cell of `obligation`: not when the obligation is under a
    /// projection whose domain does not hold it (module docs, "Projections").
    fn in_domain(&self, obligation: &Obligation, at: usize) -> bool {
        obligation
            .projection
            .is_none_or(|projection| self.projections[projection].domain[at])
    }

    /// How the document names an obligation: `{family, id}`, and `projection` for one under a
    /// listed projection.
    fn named(&self, family: &str, id: &str, projection: Option<usize>) -> Value {
        let mut value = json!({"family": family, "id": id});
        if let Some(projection) = projection {
            value["projection"] = json!(self.projections[projection].name);
        }
        self.tagged(value)
    }

    /// `value` with this flow's `flow`, in a prune of several flows.
    fn tagged(&self, mut value: Value) -> Value {
        if let Some(flow) = &self.flow {
            value["flow"] = json!(flow);
        }
        value
    }

    fn reference(&self, index: usize) -> Value {
        let obligation = &self.obligations[index];
        self.named(obligation.family, &obligation.id, obligation.projection)
    }

    fn keep_value(&self, keep: &Keep) -> Value {
        match keep {
            Keep::Claimed(pattern) => self.tagged(json!({"reason": "claimed",
                                                         "family": "patterns", "id": pattern})),
            Keep::Refutes(family, id, projection) => {
                let mut value = json!({"reason": "refutes"});
                for (key, named) in self
                    .named(family, id, *projection)
                    .as_object()
                    .into_iter()
                    .flatten()
                {
                    value[key] = named.clone();
                }
                value
            }
            Keep::Sole(index) => {
                let mut value = self.reference(*index);
                value["reason"] = json!("sole-discharger");
                value
            }
            Keep::Unknown(index) => {
                let mut value = self.reference(*index);
                value["reason"] = json!("unknown");
                value
            }
            Keep::Partner(index, with) => {
                let mut value = self.reference(*index);
                value["reason"] = json!("unknown-partner");
                value["with"] = json!(self.ids(with.iter().copied()));
                value
            }
            Keep::Undecided(class, open) => self.tagged(json!({
                "reason": "baseline-undecided",
                "class": class,
                "obligations": open.iter().map(|index| self.reference(*index)).collect::<Vec<_>>(),
            })),
            Keep::Rejected(class) => {
                self.tagged(json!({"reason": "rejected-before-run", "class": class}))
            }
        }
    }

    fn ids(&self, indices: impl IntoIterator<Item = usize>) -> Vec<String> {
        indices
            .into_iter()
            .map(|at| self.cases[at].clone())
            .collect()
    }

    /// A pair obligation's pairs as the evidence names them: each `{held, refuted}`, the cases
    /// of its side where the condition held and of the one where it was refuted.
    fn pairs_value(&self, pairs: &[[Vec<usize>; 2]]) -> Value {
        json!(
            pairs
                .iter()
                .map(|[held, refuted]| json!({
                    "held": self.ids(held.iter().copied()),
                    "refuted": self.ids(refuted.iter().copied()),
                }))
                .collect::<Vec<_>>()
        )
    }

    /// The document of these facts, with the rows each case's removal moves in `locks` and
    /// each list-reading family's `list`, asking the cells its decisions need.
    #[allow(clippy::too_many_lines)]
    fn document(
        &mut self,
        locks: &[Lock],
        lists: &[Value; 2],
        ask: &mut dyn Ask,
    ) -> Result<Value, Refusal> {
        let all = vec![true; self.cases.len()];
        let alone = (0..self.cases.len())
            .map(|at| self.keeps(at, &all, ask))
            .collect::<Result<Vec<_>, _>>()?;
        // The greedy set (module docs): each case, latest first, against the cases still kept;
        // what kept a case is recorded when it was examined. A case some rule keeps against the
        // whole corpus is kept against every subset of it (module docs, "Lazy cells").
        let mut kept = all.clone();
        let mut kept_for = vec![Vec::new(); self.cases.len()];
        for at in (0..self.cases.len()).rev() {
            if !alone[at].is_empty() {
                continue;
            }
            let keeps = self.keeps(at, &kept, ask)?;
            if keeps.is_empty() {
                kept[at] = false;
            } else {
                kept_for[at] = keeps;
            }
        }
        let lock_rows = |at: usize| lock_rows(locks, &self.cases[at]);
        let redundant = (0..self.cases.len())
            .filter(|at| alone[*at].is_empty())
            .map(|at| {
                json!({
                    "case": self.cases[at],
                    "class": self.classes[at],
                    "obligations": self.discharged_values(at),
                    "unknown": self.unknown_values(at),
                    "unasked": self.unasked(at),
                    "removable": !kept[at],
                    "kept_for": kept_for[at]
                        .iter()
                        .map(|keep| self.keep_value(keep))
                        .collect::<Vec<_>>(),
                    "lock": lock_rows(at),
                })
            })
            .collect::<Vec<_>>();
        let kept_cases = (0..self.cases.len())
            .filter(|at| !alone[*at].is_empty())
            .map(|at| {
                let reasons = alone[at]
                    .iter()
                    .map(|keep| self.keep_value(keep))
                    .collect::<Vec<_>>();
                json!({"case": self.cases[at], "class": self.classes[at], "reasons": reasons})
            })
            .collect::<Vec<_>>();
        let removable = (0..self.cases.len())
            .filter(|at| !kept[*at])
            .collect::<Vec<_>>();
        let families = self.families_value(lists);
        let undecided = (0..self.cases.len())
            .filter(|at| self.undecided(*at))
            .map(|at| json!({"case": self.cases[at], "class": self.classes[at]}))
            .collect::<Vec<_>>();
        let mut document = header();
        document["mode"] = json!(if self.lazy { LAZY } else { FULL });
        document["cases"] = json!(self.cases.len());
        document["families"] = json!(families);
        document["redundant"] = json!(redundant);
        document["removable"] = json!({
            "order": REVERSE_MANIFEST_ORDER,
            "cases": self.ids(removable.iter().copied()),
            "lock": removable
                .iter()
                .filter_map(|at| {
                    let rows = lock_rows(*at);
                    (!rows.is_null()).then(|| json!({"case": self.cases[*at], "rows": rows}))
                })
                .collect::<Vec<_>>(),
        });
        document["kept"] = json!(kept_cases);
        document["unanswered"] = json!({
            "cells": self.obligations.iter().map(|o| o.unknown.len()).sum::<usize>(),
            "complete": self.obligations.iter().all(Obligation::complete),
            "undecided_cases": undecided,
        });
        document["lock"] = locks.first().map_or(Value::Null, |lock| {
            json!({
                "path": lock.path.display().to_string(),
                "read": lock.text.is_some(),
                "sections": locks
                    .iter()
                    .filter(|lock| lock.records())
                    .map(|lock| lock.kind.document())
                    .collect::<Vec<_>>(),
            })
        });
        document["limits"] = json!(
            LIMITS
                .iter()
                .chain(self.lazy.then_some(&LAZY_LIMIT))
                .map(|(limit, detail)| json!({"limit": limit, "detail": detail}))
                .collect::<Vec<_>>()
        );
        Ok(document)
    }

    /// The obligations the case at `at` discharges, each with the other known dischargers
    /// (`others`; a pair obligation, the pairs that hold without it, `pairs`) and `complete`.
    fn discharged_values(&self, at: usize) -> Vec<Value> {
        self.obligations
            .iter()
            .filter(|obligation| obligation.dischargers.contains(&at))
            .map(|obligation| {
                let mut value =
                    self.named(obligation.family, &obligation.id, obligation.projection);
                match obligation.pairs_without(at) {
                    None => {
                        value["others"] = json!(
                            self.ids(
                                obligation
                                    .dischargers
                                    .iter()
                                    .copied()
                                    .filter(|other| *other != at)
                            )
                        );
                    }
                    Some(pairs) => value["pairs"] = self.pairs_value(&pairs),
                }
                value["complete"] = json!(obligation.complete());
                value
            })
            .collect()
    }

    /// The obligations on which the case at `at` has an unknown cell, each with its known
    /// dischargers (a pair obligation, the pairs that hold without it) and `complete`.
    fn unknown_values(&self, at: usize) -> Vec<Value> {
        self.obligations
            .iter()
            .filter(|obligation| obligation.unknown.contains(&at))
            .map(|obligation| {
                let mut value =
                    self.named(obligation.family, &obligation.id, obligation.projection);
                match obligation.pairs_without(at) {
                    None => {
                        value["dischargers"] =
                            json!(self.ids(obligation.dischargers.iter().copied()));
                    }
                    Some(pairs) => value["pairs"] = self.pairs_value(&pairs),
                }
                value["complete"] = json!(obligation.complete());
                value
            })
            .collect()
    }

    /// How many obligations did not ask the case at `at` its cell.
    fn unasked(&self, at: usize) -> usize {
        self.obligations
            .iter()
            .filter(|obligation| obligation.unasked.contains(&at))
            .count()
    }

    /// The document's `families`: each family computed (its counts) or skipped (why), and the
    /// list the `mutations` and `patterns` families read.
    fn families_value(&self, lists: &[Value; 2]) -> Vec<Value> {
        self.families
            .iter()
            .map(|family| {
                let of = self
                    .obligations
                    .iter()
                    .filter(|obligation| obligation.family == family.name)
                    .collect::<Vec<_>>();
                let mut value = match &family.skipped {
                    Some((reason, detail)) => json!({
                        "family": family.name,
                        "run": false,
                        "reason": reason,
                        "detail": detail,
                    }),
                    None => json!({
                        "family": family.name,
                        "run": true,
                        "obligations": of.len(),
                        "discharged": of.iter().filter(|o| !o.dischargers.is_empty()).count(),
                        "unanswered": of.iter().map(|o| o.unknown.len()).sum::<usize>(),
                        "complete": of.iter().all(|o| o.complete()),
                    }),
                };
                match family.name {
                    "mutations" => value["list"] = lists[0].clone(),
                    "patterns" => value["list"] = lists[1].clone(),
                    _ => {}
                }
                value
            })
            .collect()
    }
}

/// A flip item's status as its reading takes it: an argued flip's `unargued_status`.
fn flip_status(item: &Value) -> &str {
    if item["status"] == ARGUED {
        item["unargued_status"].as_str().unwrap_or_default()
    } else {
        item["status"].as_str().unwrap_or_default()
    }
}

/// Why the coverage document computed no family `name` (a coverage family, or `arguments`,
/// which every computed document reads); `None` for a family it computed or that is not one of
/// its own.
fn coverage_skipped(coverage: &Value, name: &str) -> Option<(&'static str, String)> {
    if !FAMILIES.contains(&name) {
        return None;
    }
    let family = &coverage["families"][name];
    let detail = family["reason"].as_str().map(str::to_owned);
    if family.is_null() {
        Some((
            "not-computed",
            "the coverage document computes no such family at its depth".to_owned(),
        ))
    } else if family["run"] == false || !family["items"].is_array() {
        Some((
            "not-computed",
            detail.unwrap_or_else(|| "the coverage family did not run".to_owned()),
        ))
    } else {
        None
    }
}

/// The rows of the corpus record that name `case`, by section: `run` and `coverage` rows whose
/// killer it is, `query` rows whose witness it is, `compare` rows of its program (`{implementation,
/// view}`); null when none does.
fn lock_rows(locks: &[Lock], case: &str) -> Value {
    let mut rows = serde_json::Map::new();
    for lock in locks {
        let named = lock
            .rows
            .iter()
            .filter_map(|row| match lock.kind {
                // A run row moves where its own killer or its killer under a projection is the case.
                LockKind::Run | LockKind::Coverage => (row.killer.as_deref() == Some(case)
                    || row
                        .projections
                        .iter()
                        .flatten()
                        .any(|entry| entry.killer.as_deref() == Some(case)))
                .then(|| json!(row.id)),
                LockKind::Query => (row.witness.as_deref() == Some(case)).then(|| json!(row.id)),
                LockKind::Compare => {
                    let parts: Vec<String> = serde_json::from_str(&row.id).ok()?;
                    (parts.get(1).map(String::as_str) == Some(case))
                        .then(|| json!({"implementation": parts[0], "view": parts.get(2)}))
                }
            })
            .collect::<Vec<_>>();
        if !named.is_empty() {
            rows.insert(lock.kind.document().to_owned(), json!(named));
        }
    }
    if rows.is_empty() {
        Value::Null
    } else {
        Value::Object(rows)
    }
}

/// A row's id as text.
fn text(id: &Value) -> String {
    id.as_str().map_or_else(|| id.to_string(), str::to_owned)
}

/// The `--output text` rendering of a prune document: what is removable together; a note for
/// each list that is not the corpus's own; for a lazy report, the cells its families held and
/// asked; what each removal moves in the corpus record; each case redundant alone with the
/// other dischargers of what it discharges (of the cases asked, where its row is not complete);
/// each kept case with its reasons; the families and the unanswered cells.
///
/// # Errors
///
/// When the document is no prune document.
pub fn text_rendering(document: &Value) -> Result<String, String> {
    if document["schema"] != PRUNE_SCHEMA {
        return Err("the document has no text rendering".to_owned());
    }
    let mut text = String::new();
    if !document["refused"].is_null() {
        text.push_str(&format!(
            "prune refused: {}{}: {}\n",
            document["refused"]["flow"]
                .as_str()
                .map_or_else(String::new, |flow| format!("{flow}: ")),
            document["refused"]["family"].as_str().unwrap_or("?"),
            document["refused"]["detail"].as_str().unwrap_or("")
        ));
        return Ok(text);
    }
    if document["spec"]["outcome"] == "refused" {
        text.push_str(&format!(
            "prune refused: {}the specification is refused at stage {}: {}\n",
            document["flow"]
                .as_str()
                .map_or_else(String::new, |flow| format!("{flow}: ")),
            document["spec"]["stage"].as_str().unwrap_or("?"),
            document["spec"]["detail"].as_str().unwrap_or("")
        ));
        return Ok(text);
    }
    let list = |value: &Value| {
        let ids = strings(value);
        if ids.is_empty() {
            "none".to_owned()
        } else {
            ids.join(", ")
        }
    };
    let removable = &document["removable"];
    text.push_str(&format!(
        "{} cases: {} redundant alone, {} removable together (in {} order): {}\n",
        document["cases"],
        document["redundant"].as_array().map_or(0, Vec::len),
        removable["cases"].as_array().map_or(0, Vec::len),
        removable["order"].as_str().unwrap_or("?"),
        list(&removable["cases"]),
    ));
    if let Some(detail) = document["scope"]["detail"].as_str() {
        text.push_str(&format!("note: {detail}\n"));
    }
    // Each flow's families: the document's own, or, of several flows, each flow's (`flows`).
    let flows = document["flows"].as_array().map_or_else(
        || vec![(None, document)],
        |flows| {
            flows
                .iter()
                .map(|flow| (flow["flow"].as_str(), flow))
                .collect()
        },
    );
    let of = |flow: Option<&str>| flow.map_or_else(String::new, |flow| format!("{flow}: "));
    for (flow, families) in &flows {
        for family in families["families"].as_array().into_iter().flatten() {
            if family["list"]["corpus_own"] == false {
                text.push_str(&format!(
                    "note: {}the {} family read {}, not the corpus's own list: the report holds \
                     for that list, not for the corpus\n",
                    of(*flow),
                    family["family"].as_str().unwrap_or("?"),
                    family["list"]["path"].as_str().map_or_else(
                        || "the patterns the manifest declares".to_owned(),
                        |path| { format!("`{path}`") }
                    ),
                ));
            }
        }
    }
    if document["mode"] == LAZY {
        let parts = flows
            .iter()
            .flat_map(|(flow, of_flow)| {
                let cells = &of_flow["accounting"]["cells"];
                ["mutations", "patterns"]
                    .into_iter()
                    .filter(|family| cells[family].is_object())
                    .map(move |family| {
                        format!(
                            "{}{family} {} held by the search and {} asked after it, of {}",
                            of(*flow),
                            cells[family]["searched"],
                            cells[family]["asked"],
                            cells[family]["matrix"]
                        )
                    })
            })
            .collect::<Vec<_>>();
        if !parts.is_empty() {
            text.push_str(&format!(
                "cells (lazy, as each decision needs them; --full asks every one): {}\n",
                parts.join("; ")
            ));
        }
    }
    for entry in removable["lock"].as_array().into_iter().flatten() {
        for (section, rows) in entry["rows"].as_object().into_iter().flatten() {
            let rows = rows
                .as_array()
                .into_iter()
                .flatten()
                .map(|row| {
                    row.as_str().map_or_else(
                        || {
                            format!(
                                "{} {}",
                                row["implementation"].as_str().unwrap_or("?"),
                                row["view"].as_str().unwrap_or("?")
                            )
                        },
                        str::to_owned,
                    )
                })
                .collect::<Vec<_>>();
            text.push_str(&format!(
                "  removing {} moves the record's [{section}] rows {}: --locked fails until they \
                 are recorded again\n",
                entry["case"].as_str().unwrap_or("?"),
                rows.join(", "),
            ));
        }
    }
    let reference = |value: &Value| {
        format!(
            "{}{} {}{}",
            of(value["flow"].as_str()),
            value["family"].as_str().unwrap_or("?"),
            value["id"].as_str().unwrap_or("?"),
            value["projection"]
                .as_str()
                .map_or_else(String::new, |projection| format!(" under {projection}"))
        )
    };
    text.push_str("redundant alone:\n");
    for entry in document["redundant"].as_array().into_iter().flatten() {
        let mut parts = entry["obligations"]
            .as_array()
            .into_iter()
            .flatten()
            .map(|o| {
                format!(
                    "{} (also {}{})",
                    reference(o),
                    if o["pairs"].is_array() {
                        pairs_text(&o["pairs"])
                    } else {
                        list(&o["others"])
                    },
                    if o["complete"] == false {
                        ", of the cases asked"
                    } else {
                        ""
                    }
                )
            })
            .collect::<Vec<_>>();
        if parts.is_empty() {
            parts.push("discharges nothing".to_owned());
        }
        let kept = entry["kept_for"]
            .as_array()
            .into_iter()
            .flatten()
            .map(|keep| reason_text(keep, &reference))
            .collect::<Vec<_>>();
        text.push_str(&format!(
            "  {}{}: {}\n",
            entry["case"].as_str().unwrap_or("?"),
            if entry["removable"] == true {
                String::new()
            } else {
                format!(" (kept in the removable set: {})", kept.join("; "))
            },
            parts.join("; ")
        ));
    }
    text.push_str("kept:\n");
    for entry in document["kept"].as_array().into_iter().flatten() {
        let reasons = entry["reasons"]
            .as_array()
            .into_iter()
            .flatten()
            .map(|keep| reason_text(keep, &reference))
            .collect::<Vec<_>>();
        text.push_str(&format!(
            "  {}: {}\n",
            entry["case"].as_str().unwrap_or("?"),
            reasons.join("; ")
        ));
    }
    text.push_str("families:\n");
    for (flow, family) in flows.iter().flat_map(|(flow, families)| {
        families["families"]
            .as_array()
            .into_iter()
            .flatten()
            .map(move |family| (*flow, family))
    }) {
        if family["run"] == true {
            text.push_str(&format!(
                "  {}{}: {} obligations, {} discharged, {} unanswered cells{}\n",
                of(flow),
                family["family"].as_str().unwrap_or("?"),
                family["obligations"],
                family["discharged"],
                family["unanswered"],
                if family["complete"] == false {
                    " (not every cell asked)"
                } else {
                    ""
                },
            ));
        } else {
            text.push_str(&format!(
                "  {}{}: skipped ({})\n",
                of(flow),
                family["family"].as_str().unwrap_or("?"),
                family["detail"].as_str().unwrap_or("?"),
            ));
        }
    }
    let unanswered = &document["unanswered"];
    text.push_str(&format!(
        "unanswered cells: {}; cases with an undecided baseline: {}{}\n",
        unanswered["cells"],
        list(&json!(
            unanswered["undecided_cases"]
                .as_array()
                .into_iter()
                .flatten()
                .map(|case| case["case"].clone())
                .collect::<Vec<_>>()
        )),
        if unanswered["complete"] == false {
            "; not every cell was asked"
        } else {
            ""
        },
    ));
    Ok(text)
}

/// A kept case's reason as the text rendering states it.
fn reason_text(keep: &Value, reference: &dyn Fn(&Value) -> String) -> String {
    // A reason that names no obligation names its flow (a prune of several flows) at its end.
    let flow = keep["flow"]
        .as_str()
        .map_or_else(String::new, |flow| format!(" (in {flow})"));
    match keep["reason"].as_str() {
        Some("claimed") => format!(
            "claimed by the pattern {}{flow}",
            keep["id"].as_str().unwrap_or("?")
        ),
        Some("refutes") => format!("its cell refutes {}", reference(keep)),
        Some("sole-discharger") => format!("the only discharger of {}", reference(keep)),
        Some("unknown") => format!(
            "its cell is unknown on {}, which no other case discharges",
            reference(keep)
        ),
        Some("unknown-partner") => format!(
            "its combination may pair on {} with what the unknown cell of {} holds, and no other \
             pair discharges it",
            reference(keep),
            strings(&keep["with"]).join(", ")
        ),
        Some("baseline-undecided") => format!(
            "its baseline is {} and {} obligations have no discharger{flow}",
            keep["class"].as_str().unwrap_or("?"),
            keep["obligations"].as_array().map_or(0, Vec::len)
        ),
        Some("rejected-before-run") => format!(
            "it states that it is rejected before it runs (`{}`), so no command runs it, and \
             prune reads none of the obligations it is in the corpus for{flow}",
            keep["class"].as_str().unwrap_or("?")
        ),
        _ => "?".to_owned(),
    }
}

/// A pair obligation's pairs (`{held, refuted}`) as the text rendering names them.
fn pairs_text(pairs: &Value) -> String {
    let pairs = pairs
        .as_array()
        .into_iter()
        .flatten()
        .map(|pair| {
            format!(
                "the pair held by {} and refuted by {}",
                strings(&pair["held"]).join(", "),
                strings(&pair["refuted"]).join(", ")
            )
        })
        .collect::<Vec<_>>();
    if pairs.is_empty() {
        "no pair".to_owned()
    } else {
        pairs.join(", or ")
    }
}

fn strings(value: &Value) -> Vec<String> {
    value
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(Value::as_str)
        .map(str::to_owned)
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The facts of `cases` (each `(id, class)`) with the one pair obligation `pairs`, `sides`
    /// and `unknown`, by case index.
    fn facts(
        cases: &[(&str, &str)],
        pairs: &[[&[usize]; 2]],
        sides: &[usize],
        unknown: &[usize],
    ) -> Facts {
        let pairs = pairs
            .iter()
            .map(|sides| sides.map(<[usize]>::to_vec))
            .collect::<Vec<_>>();
        let mut dischargers = Vec::new();
        for at in pairs.iter().flatten().flatten() {
            insert(&mut dischargers, *at);
        }
        Facts {
            cases: cases.iter().map(|(id, _)| (*id).to_owned()).collect(),
            classes: cases.iter().map(|(_, class)| (*class).to_owned()).collect(),
            obligations: vec![Obligation {
                family: "requirements",
                id: "requirement:r:A:mcdc".to_owned(),
                projection: None,
                dischargers,
                unknown: unknown.to_vec(),
                unasked: Vec::new(),
                source: None,
                stopped: false,
                pairing: Some(Pairing {
                    pairs,
                    sides: sides.to_vec(),
                }),
            }],
            keeps: vec![Vec::new(); cases.len()],
            families: Vec::new(),
            lazy: false,
            cells: [Asked::default(); 2],
            projections: Vec::new(),
            answers: BTreeMap::new(),
            flow: None,
        }
    }

    fn complete() -> Complete {
        Complete([Value::Null, Value::Null, Value::Null])
    }

    /// Why the case at `at` is kept against `kept`.
    fn keeps(facts: &mut Facts, at: usize, kept: &[bool]) -> Vec<Keep> {
        facts.keeps(at, kept, &mut complete()).unwrap()
    }

    /// A pair whose sides two cases give keeps both, each its sole discharger; a case on both
    /// sides of a pair is its sole discharger alone.
    #[test]
    fn each_side_of_an_only_pair_is_kept() {
        let cases = [("x", "result"), ("y", "result"), ("z", "result")];
        let mut split = facts(&cases, &[[&[0], &[1]]], &[0, 1], &[]);
        let all = [true; 3];
        assert_eq!(keeps(&mut split, 0, &all), [Keep::Sole(0)]);
        assert_eq!(keeps(&mut split, 1, &all), [Keep::Sole(0)]);
        assert_eq!(keeps(&mut split, 2, &all), []);
        let mut own = facts(&cases, &[[&[2], &[2]]], &[2], &[]);
        assert_eq!(keeps(&mut own, 2, &all), [Keep::Sole(0)]);
    }

    /// Of two cases on one side, each is redundant alone, and the walk removes the later one and
    /// keeps the other; the evidence names the pair that holds without each.
    #[test]
    fn of_two_cases_on_one_side_one_is_removable() {
        let cases = [("x", "result"), ("y", "result"), ("y2", "result")];
        let mut facts = facts(&cases, &[[&[0], &[1, 2]]], &[0, 1, 2], &[]);
        let document = facts
            .document(&[], &[Value::Null, Value::Null], &mut complete())
            .unwrap();
        assert_eq!(document["removable"]["cases"], json!(["y2"]));
        let redundant = document["redundant"].as_array().unwrap();
        assert_eq!(
            redundant
                .iter()
                .map(|entry| (&entry["case"], &entry["removable"], &entry["kept_for"]))
                .collect::<Vec<_>>(),
            [
                (
                    &json!("y"),
                    &json!(false),
                    &json!([{"reason": "sole-discharger", "family": "requirements",
                             "id": "requirement:r:A:mcdc"}])
                ),
                (&json!("y2"), &json!(true), &json!([])),
            ]
        );
        assert_eq!(
            redundant[0]["obligations"],
            json!([{"family": "requirements", "id": "requirement:r:A:mcdc",
                    "pairs": [{"held": ["x"], "refuted": ["y2"]}], "complete": true}])
        );
        assert_eq!(
            document["kept"],
            json!([{"case": "x", "class": "result", "reasons": [
                {"reason": "sole-discharger", "family": "requirements",
                 "id": "requirement:r:A:mcdc"}]}])
        );
    }

    /// With no decided pair, a decided side is kept while another case's cell is unknown or its
    /// baseline undecided, since what that case holds may be its other side; a case that is no
    /// side is not, and neither is a side once no such case is kept.
    #[test]
    fn a_decided_side_is_kept_while_an_unknown_may_complete_its_pair() {
        let cases = [
            ("x", "result"),
            ("y", "result"),
            ("u", "result"),
            ("z", "result"),
            ("b", "timeout"),
        ];
        let mut facts = facts(&cases, &[], &[0, 1], &[2]);
        let all = [true; 5];
        assert_eq!(keeps(&mut facts, 0, &all), [Keep::Partner(0, vec![2, 4])]);
        assert_eq!(keeps(&mut facts, 2, &all), [Keep::Unknown(0)]);
        assert_eq!(keeps(&mut facts, 3, &all), []);
        assert_eq!(
            keeps(&mut facts, 4, &all),
            [Keep::Undecided("timeout".to_owned(), vec![0])]
        );
        assert_eq!(
            keeps(&mut facts, 1, &[true, true, false, true, true]),
            [Keep::Partner(0, vec![4])]
        );
        assert_eq!(keeps(&mut facts, 1, &[true, true, false, true, false]), []);
        let value = facts.keep_value(&Keep::Partner(0, vec![2, 4]));
        assert_eq!(
            value,
            json!({"reason": "unknown-partner", "family": "requirements",
                   "id": "requirement:r:A:mcdc", "with": ["u", "b"]})
        );
    }
    /// A row's cells under a projection judged per program: its verdicts, the killer, nothing
    /// outside the domain; `undecided` leaves the programs with no verdict unknown; a table
    /// `expect` of survival under the projection is refuted by its killers; a row whose status
    /// no program decides gives its own cells, within the domain; the run's own projection reads
    /// the row's cells.
    #[test]
    fn a_row_is_read_under_each_projection_within_its_domain() {
        use crate::report::projection_kill_cells;
        let domain = ["x".to_owned(), "y".to_owned(), "z".to_owned()];
        let row = |status: &str, expect: Value| {
            json!({
                "id": "m", "status": "killed", "killer": "x", "killed_by": ["x", "w"],
                "expect": expect,
                "executed": [
                    {"program": "x", "outcome": "distinguish",
                     "projections": {"p": "agree", "q": "killed"}},
                    {"program": "w", "outcome": "distinguish",
                     "projections": {"p": "killed", "q": "outside-domain"}},
                ],
                "projection_search": {"executed": [
                    {"program": "y", "outcome": "timeout", "projections": {"p": "unknown"}},
                ]},
                "projections": [
                    {"name": "p", "status": status, "killer": null, "reason": null},
                    {"name": "q", "status": "killed", "killer": "x", "reason": null},
                ],
            })
        };
        let cells = |dischargers: &[&str], unknown: &[&str]| {
            Reading::Obligation(Cells {
                dischargers: dischargers.iter().map(|id| (*id).to_owned()).collect(),
                unknown: unknown.iter().map(|id| (*id).to_owned()).collect(),
                unnamed: false,
            })
        };
        // `w` kills under `p` but is outside the domain given.
        assert_eq!(
            projection_kill_cells(&row("unknown", Value::Null), "p", Some(&domain)),
            cells(&[], &["y"])
        );
        assert_eq!(
            projection_kill_cells(&row("undecided", Value::Null), "p", Some(&domain)),
            cells(&[], &["y", "z"])
        );
        assert_eq!(
            projection_kill_cells(&row("unknown", Value::Null), "q", Some(&domain)),
            cells(&["x"], &[])
        );
        assert_eq!(
            projection_kill_cells(&row("unknown", json!({"q": "survive"})), "q", Some(&domain)),
            Reading::Refuted(vec!["x".to_owned()])
        );
        // The string claim is the row's, read by the caller, not a projection's.
        assert_eq!(
            projection_kill_cells(&row("unknown", json!("survive")), "q", Some(&domain)),
            cells(&["x"], &[])
        );
        assert_eq!(
            projection_kill_cells(&row("equivalent", Value::Null), "p", Some(&domain)),
            Reading::None
        );
        // The run's own projection: the row's killers, `w` among them.
        assert_eq!(
            projection_kill_cells(&row("unknown", Value::Null), "q", None),
            cells(&["x", "w"], &[])
        );
        // A row no program decides gives every projection its own status and cells.
        let timed_out = json!({
            "id": "m", "status": "timeout",
            "executed": [{"program": "z", "outcome": "timeout"},
                         {"program": "w", "outcome": "timeout"}],
            "projections": [{"name": "p", "status": "timeout"}],
        });
        assert_eq!(
            projection_kill_cells(&timed_out, "p", Some(&domain)),
            cells(&[], &["z"])
        );
        // In a flow that declares no projection, `{ default = "survive" }` is the row's claim; in
        // one that declares projections, `default` names a projection of its own.
        let claimed = json!({"id": "m", "status": "killed", "killer": "x",
                             "expect": {"default": "survive"}});
        assert_eq!(
            crate::report::kill_cells(&claimed),
            Reading::Refuted(vec!["x".to_owned()])
        );
        let mut projected = claimed;
        projected["projections"] = json!([]);
        assert_eq!(crate::report::kill_cells(&projected), cells(&["x"], &[]));
    }
    /// An `accepts` projection is judged per program as any flow-side projection: prune reads
    /// its verdicts from the executed entries. The run's own slots agree on every program
    /// (`survived`), and `y` alone is accepted on one side and rejected on the other, so it is
    /// kept as the only discharger of `m` under `acc`; `x` and `z` are removable. A snapshot
    /// projection (`msg`) and a metric one (`alloc`) are in no default `[run] projections`, so
    /// they give no obligation: `m`'s only one is under `acc`.
    #[test]
    fn an_acceptance_kill_keeps_its_only_killer() {
        let manifest = FlowManifest::decode(
            "[spec]\nentry = \"calc.k\"\nmain_module = \"CALC\"\nsyntax_module = \"CALC-SYNTAX\"\n\n\
             [[projection]]\nname = \"acc\"\nkind = \"accepts\"\n\n\
             [[projection]]\nname = \"msg\"\nkind = \"accepts\"\nrelation = \"snapshot\"\n\n\
             [[projection]]\nname = \"alloc\"\nkind = \"metric\"\nmetric = \"bytes\"\n\
             direction = \"lower\"\n\n\
             [[program]]\nid = \"x\"\ntext = \"1\"\n\n\
             [[program]]\nid = \"y\"\ntext = \"2\"\n\n\
             [[program]]\nid = \"z\"\ntext = \"3\"\n",
            Path::new("."),
        )
        .unwrap();
        let entry = |program: &str, verdict: &str| json!({"program": program, "outcome": "agree", "projections": {"acc": verdict}});
        let run = json!({"mutations": [{
            "id": "m", "status": "survived", "killer": null,
            "executed": [entry("x", "agree"), entry("y", "killed"), entry("z", "agree")],
            "projections": [{"name": "acc", "status": "killed", "killer": "y", "reason": null}],
        }]});
        let programs = ["x", "y", "z"].map(|id| json!({"id": id, "class": "comparable"}));
        let coverage = json!({ "programs": programs });
        let options = PruneOptions::default();
        let front = FrontEnd::default();
        let inputs = Inputs {
            manifest: &manifest,
            options: &options,
            front: &front,
            locks: &[],
            list: None,
            pattern_list: None,
            coverage: &coverage,
            skipped: &[],
            lists: [Value::Null, Value::Null],
        };
        let mut facts = Facts::read(
            &inputs,
            Some(&run),
            None,
            Vec::new(),
            false,
            &mut complete(),
        )
        .unwrap();
        let document = facts
            .document(&[], &[Value::Null, Value::Null], &mut complete())
            .unwrap();
        assert_eq!(
            facts
                .obligations
                .iter()
                .filter(|obligation| obligation.family == "mutations")
                .map(|obligation| {
                    facts.named(obligation.family, &obligation.id, obligation.projection)
                })
                .collect::<Vec<_>>(),
            [json!({"family": "mutations", "id": "m", "projection": "acc"})]
        );
        assert_eq!(
            document["removable"]["cases"],
            json!(["x", "z"]),
            "{document:#}"
        );
        assert_eq!(
            document["kept"],
            json!([{"case": "y", "class": "comparable", "reasons": [
                {"reason": "sole-discharger", "family": "mutations", "id": "m",
                 "projection": "acc"}]}]),
            "{document:#}"
        );
    }

    /// One flow's facts for a joint decision: its cases (all `comparable`), each obligation of
    /// the `mutations` family its id and its decided dischargers (case indices), and the cases
    /// whose entry states a rejection.
    fn flow_facts(flow: &str, cases: &[&str], obligations: &[(&str, &[usize])]) -> Facts {
        let mut facts = facts(
            &cases
                .iter()
                .map(|case| (*case, "comparable"))
                .collect::<Vec<_>>(),
            &[],
            &[],
            &[],
        );
        facts.obligations = obligations
            .iter()
            .map(|(id, dischargers)| Obligation {
                family: "mutations",
                id: (*id).to_owned(),
                projection: None,
                dischargers: dischargers.to_vec(),
                unknown: Vec::new(),
                unasked: Vec::new(),
                source: None,
                stopped: false,
                pairing: None,
            })
            .collect();
        facts.flow = Some(flow.to_owned());
        facts
    }

    /// PJ-31: the facts of two flows on one root are merged before any decision. `add` reads
    /// `a1`, `a2`, `m1` and its mutation is killed by `a1` and `a2`; `mul` reads `m1`, `a2`, `x`,
    /// its `mul` killed by `m1` alone and its `edge` by `a2` alone. Alone, `add` would remove
    /// `a2` (reverse manifest order); jointly `a2` is `mul`'s only killer of `edge`, so it is kept
    /// naming `mul`, and `a1` is removable. `m1` is kept for `mul` though `add` reads it with no
    /// cell; `x`, which only `mul` reads and which discharges nothing, is removable, and a case
    /// `mul` states is rejected before it runs is kept for `mul` alone. A reason of an obligation
    /// under a projection names both the flow and the projection.
    #[test]
    fn the_flows_facts_are_merged_before_any_decision() {
        let add = flow_facts("add/FLOW.toml", &["a1", "a2", "m1"], &[("plus", &[0, 1])]);
        let mut mul = flow_facts(
            "mul/FLOW.toml",
            &["m1", "a2", "x", "r"],
            &[("mul", &[0]), ("edge", &[1])],
        );
        mul.keeps[3].push(Keep::Rejected("rejected".to_owned()));
        // `edge` is an obligation under `mul`'s projection `out`, whose domain holds every case.
        mul.projections = vec![Listed {
            name: "out".to_owned(),
            own: false,
            domain: vec![true; 4],
        }];
        mul.obligations[1].projection = Some(0);
        let mut joint = Joint::new(
            vec![add, mul],
            vec!["add/FLOW.toml".to_owned(), "mul/FLOW.toml".to_owned()],
        );
        assert_eq!(joint.cases, ["a1", "a2", "m1", "x", "r"]);
        let mut asks = Completes(vec![(None, None, complete()), (None, None, complete())]);
        let document = joint.document(&mut asks).unwrap();
        assert_eq!(document["removable"]["order"], REVERSE_FLOW_MANIFEST_ORDER);
        assert_eq!(document["removable"]["cases"], json!(["a1", "x"]));
        let kept = |case: &str| {
            document["kept"]
                .as_array()
                .unwrap()
                .iter()
                .find(|entry| entry["case"] == case)
                .unwrap_or_else(|| panic!("{case} not kept: {document:#}"))
                .clone()
        };
        assert_eq!(
            kept("a2")["reasons"],
            json!([{"reason": "sole-discharger", "family": "mutations", "id": "edge",
                    "projection": "out", "flow": "mul/FLOW.toml"}])
        );
        assert_eq!(
            kept("a2")["classes"],
            json!([{"flow": "add/FLOW.toml", "class": "comparable"},
                   {"flow": "mul/FLOW.toml", "class": "comparable"}])
        );
        assert_eq!(
            kept("m1")["reasons"],
            json!([{"reason": "sole-discharger", "family": "mutations", "id": "mul",
                    "flow": "mul/FLOW.toml"}])
        );
        assert_eq!(
            kept("r")["reasons"],
            json!([{"reason": "rejected-before-run", "class": "rejected",
                    "flow": "mul/FLOW.toml"}])
        );
        let a1 = &document["redundant"][0];
        assert_eq!(a1["case"], "a1");
        assert_eq!(
            a1["obligations"],
            json!([{"family": "mutations", "id": "plus", "flow": "add/FLOW.toml",
                    "others": ["a2"], "complete": true}])
        );
        assert_eq!(document["redundant"][1]["case"], "x");
        assert_eq!(document["redundant"][1]["obligations"], json!([]));
        // The text rendering names each obligation's flow.
        let mut shown = document.clone();
        shown["flows"] = json!([]);
        shown["scope"] = json!({"detail": "of the flows given"});
        let text = text_rendering(&shown).unwrap();
        assert!(
            text.starts_with(
                "5 cases: 2 redundant alone, 2 removable together (in reverse-flow-manifest \
                 order): a1, x\n"
            ),
            "{text}"
        );
        assert!(
            text.contains("  a2: the only discharger of mul/FLOW.toml: mutations edge under out\n"),
            "{text}"
        );
        assert!(
            text.contains("  a1: add/FLOW.toml: mutations plus (also a2)\n"),
            "{text}"
        );
        assert!(text.contains("(in mul/FLOW.toml)"), "{text}");
    }
}
