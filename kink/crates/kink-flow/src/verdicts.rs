//! The verdicts of a `coverage`, `run` or `compare` document as deterministic TOML (`--output
//! verdicts`): what the corpus and the specification decide, and nothing that depends on the
//! host, the build, the cache or the order the work was done in. A rendering is the corpus
//! record's header and the command's section ([`crate::lock`]): it is the format of recorded
//! outputs and, without `killed_by`, of the section of `kink.lock` its command writes (`run
//! --lock`, `coverage --lock`, `compare --lock`; [`lock_section`], [`lock_text`]), so that a
//! change of a verdict shows in review and an unchanged corpus renders the same bytes.
//!
//! ```toml
//! # kink's verdicts of a corpus, one section per command: [run] (`run` on a mutation list),
//! # ...
//! schema = "kink-flow-verdicts"
//!
//! [coverage]
//! # The verdicts of kink's `coverage` command (`krs kink coverage`, `kink-flow coverage`): the
//! # ...
//! version = 27
//! profile = "z3"
//! z3_version = "5.3.3.0 430d19e697e2ec9bad79ff210d41b4a7a5fcfa3e 430d19e"
//! z3_library_sha256 = "7ca2ea1f27e40c86269d6ff7f0e82293708253cb05dbec094c90b08c4ec04d31"
//! krs_annotation = 10
//!
//! [coverage.spec]
//! outcome = "admitted"
//!
//! [coverage.settings]
//! depth = 1
//! mcdc = [
//! ]
//! work_factor = 5
//!
//! # Each family lists its obligations by id: `open`, those no program covers; `argued`, those an
//! # ...
//! [coverage.rules]
//! open = [
//!   "rule:crate::plus_succ",
//! ]
//! argued = [
//! ]
//!
//! [coverage.requirements]
//! open = [
//! ]
//! argued = [
//!   { id = "requirement:crate::wake:held", standing = "text" },
//! ]
//!
//! [coverage.syntax]
//! open = [
//! ]
//! argued = [
//! ]
//!
//! # Each [[coverage.flip]] is a condition flip: a mutant kink generates from the definition by
//! # ...
//! [coverage.flips]
//! run = true
//!
//! [[coverage.flip]]
//! id = "flip--dispatch+wake--H"
//! negates = "self.halted"
//! rules = [
//!   "rule:crate::dispatch",
//!   "rule:crate::wake",
//! ]
//! status = "distinguished"
//! killer = "irq"
//!
//! [[coverage.flip]]
//! id = "flip--halted+wake--I"
//! negates = "self.irq"
//! rules = [
//!   "rule:crate::halted",
//!   "rule:crate::wake",
//! ]
//! status = "argued"
//! standing = "text"
//! ```
//!
//! A rendering says what it is without the README: the record's header opens with a comment
//! saying what the file is and who writes each section ([`RECORD_PREAMBLE`]), the section with
//! one naming the command whose verdicts it holds and what that command does with it as a lock
//! ([`RUN_PREAMBLE`], [`COVERAGE_PREAMBLE`]), and a comment before its families and before its
//! rows says what an entry and each status word is ([`MUTATIONS_LEGEND`], [`FAMILIES_LEGEND`],
//! [`FLIPS_LEGEND`]). Each comment is a constant of the rendering's version, so it moves no line
//! of a lock. The record's header holds nothing else but `schema` ([`record_header`]); every
//! value below is the section's, under its `[run]` or `[coverage]` table.
//!
//! The section names its `version` and the build's solver `profile` (`no-z3` or `z3`): under Z3 a
//! class, a status and a cell can move between `killed`, `unknown` and `survived` with the solver's
//! answers, so a diff of two renderings across profiles shows why. Under the Z3 profile it also
//! names the Z3 build the answers came from (the document's `z3`): `z3_version`, Z3's own version
//! string, and `z3_library_sha256`, the SHA-256 of the library file Z3's code comes from (k-rust
//! `z3_build`; the archive of a static link, the shared library of a dynamic one). Whether a
//! resource-bounded query is decided is a function of the query, its units and the machine code
//! that counts them, so a kink build linking another Z3 can move a class, a status or a killer
//! with the same inputs and the same profile; the two lines are the profile's argument applied
//! to the build. The digest is the identity: two builds of one release (another compiler, other
//! flags, another architecture) can count units differently and report one version string, which
//! is there so that a reader sees which release moved. A build that cannot name its library (a
//! shared library replaced since it was mapped, a static link whose archive the build could not
//! name) has no `z3_library_sha256` line, the caches being off for it for the same reason
//! (kink-native `UNNAMED_Z3_BUILD`). The portable profile renders neither line. A `coverage`
//! document the KRS
//! front end annotated also has `krs_annotation`, the version of that annotation (the document's
//! `krs.version`), since an item's id spells its rule's KRS item as the annotation spells it: two
//! renderings of the same coverage under different annotation versions differ in that line and in
//! the ids, not in what is open. A run rendering names no rule, so it has no `krs_annotation`
//! line, which could only move a lock without any verdict moving.
//!
//! A `run` section names the work budget (`work_factor`) after the solver lines. A `coverage`
//! document gives its settings (`depth`, `mcdc`, `work_factor`; not the tiers computed, since a
//! lock is written only where both ran and `[flips] run` says whether tier 2 did), then per
//! family the ids of its open obligations and its argued ones, in item order (`[rules]`,
//! `[requirements]`, `[syntax]`, and `[rule_windows]` and `[syntax_paths]` where the document has
//! the family, at a depth above 1; [`crate::coverage::open_ids`], [`crate::coverage::argued_ids`]),
//! each argued one with the standing of its argument (`{ id = "<id>", standing = "<standing>" }`,
//! a standing that rests on findings of the critical-pair check that `[spec] assume_joined`
//! assumes followed by `, assuming joined` and their names;
//! [`crate::coverage::argument_standings`]), and, where it has any, its undecided ones
//! (`undecided`; [`crate::coverage::undecided_ids`]); then for the flips family whether it ran
//! and, when it ran, each flip (`[[flip]]`, in item order) with its id, the condition it negates
//! as the source writes it (`negates`) or the bit it toggles (`toggles`; the item's `text`), the
//! rules it edits by their ids in the rules family (`rules`), its status (`argued` for an argued
//! one, with its `standing`), a refused flip's reason, a distinguished flip's `killer`, and an
//! undistinguished flip's `horizon` where it rests on one, as a run rendering gives a survivor's.
//! An argued item is written once, where its family lists it, so a standing that moves changes
//! that item's line alone. A flip's id is the front end's (`flip--<sentences>--<atom>`,
//! `bitflip--<sentences>--bit<k>`), stable while the definition's guard families are, since it
//! keys the flip's recorded killer and its argued entry; `negates` and `rules` resolve it without
//! the coverage document, and are functions of the definition, as the id is.
//! It lists no programs and no counts, so that it moves only when a gap opens or closes, an
//! argument is added or removed or its standing moves, or a killer changes: a case that covers
//! nothing new renders the same bytes. An argument's text is not rendered, since it explains a
//! verdict rather than records one; its id is, since an argued obligation leaves the open ones
//! without any program covering it, and a lock that did not say so would show a gap closing that
//! no program closed. Its standing is, since it is what the argument rests on, a function of the
//! specification, the corpus and the checks the build runs: a lock that did not say so would
//! show an argument resting on its text alone the same as one a check decided. A flip's
//! killer is the recorded one (the coverage lock's) while it kills, else the first killing
//! program in the search's order, a function of the inputs and the record, as a run's is. A
//! `run` document
//! gives each mutation it judged (`[[run.mutation]]`, in list order) its status, a killed mutation's
//! `killer` (under both schedules), under `full` its `killed_by` too (every killing program in
//! corpus order), a survivor that rests on a horizon its `horizon` (each program whose
//! observation channels agreed only up to its baseline's horizon, with each channel, the number
//! of elements agreed on and why the channel opened there, `opening`: a function of the result
//! key, not of the host), and, when a corpus error stopped it, the mutation and the reason under
//! `[run.stopped]` (the mutations after it have no status). A refused specification has its
//! `stage` and `reason` under `[run.spec]` (`[coverage.spec]`), a refused mutation list its
//! `outcome` under `[run.mutation_list]` (a run document of a list that does not decode has no
//! `[run.spec]`), and a refused lock its `outcome` under `[run.lock]` (`[coverage.lock]`), with no case or mutation. A mutation its author must fix before it is
//! judged, `invalid-mutation` or `not-admitted`, has its `reason` too, as a refused specification
//! has: the reason is a function of the specification and the mutation alone (the resolution,
//! the mutant's compile, its consistency, its stop), so it is the refusal's verdict, and a lock
//! shows which refusal moved. The refusals' texts are not rendered, since they explain a refusal
//! rather than record a verdict ([`refusal_details`] gives them, and `kink-flow` prints them on
//! stderr). `report --output verdicts` renders the stored run document,
//! so it prints what `run --output verdicts` printed; when there is no stored run document to
//! render, the reason is the error ([`verdicts`]).
//!
//! Left out, each because it is not a function of the specification, the corpus, the budget, the
//! killer record and the solver (the profile and, under Z3, its build, in the header): timings,
//! digests, kink's own build identity, the cache's state, the schedule, and the reason of any other status, since the reason
//! of `unknown` is the first exclusion in run order. A status does not depend on the order or the
//! cache while no `budget.time_ms` bound fires (README, the program order), and neither does a
//! full run's `killed_by`: it is the set of comparable programs whose cell is a proved difference,
//! each cell an outcome that does not depend on the other programs of the call, live or cached
//! under a key that names every input. A killer is the recorded one while it kills, else the
//! first killing program in the search's order, which is a function of the inputs (README, "The
//! corpus record"): so a first-kill and a full rendering state the same facts apart from the
//! `killed_by` lines, and a full rendering of a run with no kill is the first-kill rendering. A
//! `timeout` class or status depends on the host by its nature.
//!
//! Every array of strings or inline tables the rendering writes (`open`, `argued`, `undecided`,
//! `[settings] mcdc`, a flip's `rules`, `horizon`, `killed_by`) has one value per line, with a
//! trailing comma, from the key's line to a `]` on its own, an empty array included: so a lock's
//! diff of a set that changed is exactly the lines of the values that joined or left it, in the
//! set's order, and no other line moves. An `argued` entry is an inline table, one per line, so that each item's
//! line carries its standing: a standing that moves changes that item's line alone, and an
//! argument added moves its item's line from `open` to `argued`.

use serde_json::{Value, json};
use std::fmt::Write as _;

/// The `schema` of the rendering.
pub const VERDICTS_SCHEMA: &str = "kink-flow-verdicts";
/// The version of the rendering: 1, the first; 2 since CF-23 added the header's `schedule` (run
/// documents) and `profile`, and a full run's `killed_by`; 3 since a mutation's `status` names
/// the runner status version 2 rendered `invalid` `not-admitted` (run document version 18), so a
/// lock that moves from one name to the other shows a new version, not a moved verdict; 4 since
/// the header's `krs_annotation` names the front end's annotation version, which a rule's KRS
/// item is spelled by, so that a lock whose names move with the annotation shows why; 5 since an
/// `invalid-mutation` or `not-admitted` mutation has its `reason`; 6 since a killed mutation of a
/// run has its `killer` under both schedules (the recorded killer while it kills, else the first
/// in the search's order), the header no longer names the schedule, a run rendering no longer has
/// `krs_annotation`, and a refused lock has its `[lock]` section; 7 since a `results` rendering
/// lists each fired or matched rule whose guard misses an outcome (`[[guard]]`); 8 since the
/// header names the Z3 build under the Z3 profile (`z3_version`, `z3_library_sha256`), so that a
/// lock whose verdicts moved with the solver build says why, and one recorded on another build is
/// a finding under `--locked` ([`crate::lock`]); 9 since the `coverage` document replaces the
/// `results` document: its rendering (`document = "coverage"`) gives the settings and each
/// family's open obligations by id, and no case; 10 since a `coverage` rendering lists the open
/// obligations of the syntax family (`[syntax]`), so that a lock that gains the section shows a
/// new version, not a moved verdict; 11 since a `coverage` rendering whose flips ran lists each
/// flip (`[[flip]]`) with its status, a refused flip's reason and a distinguished flip's killer,
/// the recorded one while it kills, so that a `coverage.lock` records the flips' verdicts; 12 since
/// a survivor some program of which agreed only up to its baseline's observation horizon (`[observe]`)
/// has `horizon`, each such program's channels and the number of elements they agreed on, so that
/// a lock shows when a survivor rests on a prefix; 13 since
/// a `coverage` rendering lists each family's argued obligations (`argued`, beside `open`) and an
/// argued flip has status `argued`, so that a lock records which obligations are argued rather
/// than covered; 14 since each horizon names why its channel opened (`opening`: `bound`,
/// `undecided-element`, `branch`, `undecided-path`, `cycle`), so that a lock shows whether a larger budget
/// could observe more, and a `coverage` rendering gives an undistinguished flip that rests on a
/// horizon its `horizon`; 15 since
/// `[coverage] mcdc` is read: `mcdc` is the names or `true`, and a family
/// with undecided obligations lists them (`undecided`, beside `open`, which leaves them out), so
/// that a lock shows a pair the record cannot decide apart from one no program shows; 16 since a
/// `coverage` rendering's `[rules]` lists the heating rules the compile generates from `strict`
/// and `seqstrict` productions and `context` sentences by their ids
/// (`rule:<production>:heat:<position>`), so that a lock that gains them shows a new version,
/// not a moved verdict; 17 since a `coverage` rendering of a depth above 1 lists the open and
/// argued rule windows (`[rule_windows]`, every open window, on the frontier or not), where such a
/// document was refused before; 18 since such a rendering also lists the open and argued syntax
/// paths (`[syntax_paths]`, every open path and joint field value, on the frontier or not), so a
/// lock of depth above 1 shows a path opening or closing; a rendering of depth 1 is unchanged but
/// for its `version` line; 19 since a function equation's guard outcomes, and so the
/// `[[guard]]` entries and the open requirements of a `coverage` rendering, cover every
/// application its left-hand side matches whose deciding priority group is its own, whether or
/// not the run tried it there, so that a lock whose guard and requirement lists move for that
/// reason shows a new version, not a corpus change; 20 since every array of strings or inline
/// tables the rendering writes has one value per line, an empty one included (module
/// documentation), so that a lock whose layout moves shows a new version; its values are
/// unchanged; 21 since a `coverage` rendering lists each argued item with the standing of its
/// argument (`[arguments]`, one line per item, an empty section where none is argued), so that a
/// lock records what each argument rests on and a standing that moves makes it stale; 22 since an
/// equation of a function only the manifest's invariants reach is no obligation (coverage
/// document version 19), so that a lock whose open lists and flips move for that reason shows a
/// new version, not a corpus change, and since an `[arguments]` line states the assumed findings
/// a standing rests on (`"<id>" = "<standing>, assuming joined <name>, ..."`) and an argued
/// item whose invariant is not shown to be a function is `unchecked`; a run rendering differs in
/// its `version` line only.
/// 23 since an `[arguments]` line names the assumed findings a standing rests on by their names of
/// kind, sentences and digest (`root:A,B#D`, KINK-FINDING-NAMES), where 22 named them by
/// generated-K positions, so that a lock whose arguments name findings shows a new version; a lock
/// whose standings assume nothing differs in its `version` line only.
/// 24 since a rendering is the corpus record's header and its command's section (FB48-NAMES,
/// FB48-ONE-LOCK): the header is a comment saying what the file is and `schema`; the section,
/// `[run]` or `[coverage]`, states its own `version`, `profile`, Z3 build and `krs_annotation`,
/// opens with a comment naming the command whose verdicts it holds and what that command does with
/// it as a lock, holds the command's tables under its own (`[run.spec]`, `[[run.mutation]]`,
/// `[coverage.rules]`, `[[coverage.flip]]`), and writes a comment before its rows saying what a
/// row and each status is, where 23 wrote one command's rendering at the top of its file with a
/// `document`; a coverage section gives each argued item once, in its family's `argued`, with its
/// standing (`{ id, standing }`; an argued flip's `standing` on its row), where `[arguments]`
/// repeated the ids, gives each flip the condition it negates or the bit it toggles and the rules
/// it edits, and no longer writes `[settings] tiers`, which `[coverage.flips] run` states. Under
/// `--locked` a section of another version, or a lock before 24, is refused, naming the command
/// that rewrites it ([`crate::lock`]).
/// 25 since a record has a third section, `[compare]` (FB47-VERDICTS), `compare`'s verdicts, one
/// `[[compare.verdict]]` per (implementation, program, view), and the record's comment names it:
/// a `[run]` or `[coverage]` section differs in its `version` line only, and the record in its
/// comment.
/// 26 since a `[run]` section names the work budget its verdicts were decided under
/// (`work_factor`, FB45-KINK: a mutant's run is bounded by `max(work_factor × P, P_max)` polls,
/// and a run the bound cuts is `unknown`), and so does a `[coverage.settings]` table, for its
/// flips: a lock says which budget its verdicts are complete to, and one written under another
/// budget is stale. A program whose mutant run never ends is `unknown` where it was a `timeout`.
/// 27 since a record has a fourth section, `[query]` (FB54-WITNESS), `query`'s obligations, one
/// `[[query.pattern]]` per pattern of the list with its status and, for a hit, its recorded
/// `witness`, and the record's comment names it: a `[run]`, `[coverage]` or `[compare]` section
/// differs in its `version` line only, and the record in its comment.
pub const VERDICTS_VERSION: u64 = 27;

/// The comment a record opens with, before its `schema`: what the file is, which section each
/// command keeps, and that a command touches only its own, so that a reader of `kink.lock` needs
/// no README to tell what wrote it.
pub const RECORD_PREAMBLE: &[&str] = &[
    "kink's verdicts of a corpus, one section per command: [run] (`run` on a mutation list),",
    "[coverage] (`coverage`), [compare] (`compare`) and [query] (`query` on a pattern list). As a",
    "lock (`--lock FILE`; krs keeps <corpus>/kink.lock), each command reads, checks (--locked) and",
    "rewrites only its own section, and keeps the others as they are.",
];

/// The comment after `[run]`: the command whose verdicts the section holds, and what the command
/// does with it as a lock.
pub const RUN_PREAMBLE: &[&str] = &[
    "The verdicts of kink's `run` command (`krs kink run`, `kink-flow run`): the next run tries",
    "each `killer` first, a run without --locked rewrites this section, and `run --locked` checks",
    "that it is current.",
];

/// The comment after `[coverage]` ([`RUN_PREAMBLE`]'s, for `coverage`).
pub const COVERAGE_PREAMBLE: &[&str] = &[
    "The verdicts of kink's `coverage` command (`krs kink coverage`, `kink-flow coverage`): the",
    "next run tries each flip's `killer` first, a run without --locked rewrites this section, and",
    "`coverage --locked` checks that it is current.",
];

/// The comment after `[compare]` ([`RUN_PREAMBLE`]'s, for `compare`).
pub const COMPARE_PREAMBLE: &[&str] = &[
    "The verdicts of kink's `compare` command (`krs kink compare`, `kink-flow compare`): a run",
    "without --locked rewrites this section, and `compare --locked` checks that it is current.",
];

/// The comment after `[query]` ([`RUN_PREAMBLE`]'s, for `query`).
pub const QUERY_PREAMBLE: &[&str] = &[
    "The obligations of kink's `query` command (`krs kink query`, `kink-flow query`): the next",
    "query tries each pattern's `witness` first, a query of the whole pattern list without",
    "--locked rewrites this section, and `query --locked` checks that it is current.",
];

/// The comment before a query section's first `[[query.pattern]]`: what a row is and what each
/// status says.
pub const QUERY_LEGEND: &[&str] = &[
    "Each [[query.pattern]] is a pattern of the list, by its id, and its obligation, that some",
    "program's run reaches a state that matches it: hit (`witness` names one such program, kept",
    "while it still hits), open (every program's run reaches none: each answered a final no) or",
    "undecided (no program hits, and some program's answer is not a final no).",
];

/// The comment before a compare section's first `[[compare.verdict]]`: what a row is, what each
/// verdict says, and what the digests name.
pub const COMPARE_LEGEND: &[&str] = &[
    "Each [[compare.verdict]] is one view of one implementation on one program, and its verdict:",
    "equal (its end agrees with the definition's under the view), different (`difference`, the",
    "first difference), could-not-apply (it declined the program; `reason`, its own words) or",
    "not-compared (`reason` says why). `request_sha256` names the request it was given, and",
    "`identity_sha256` its build (its `identity` file); a run that gave no answer keeps its rows.",
];

/// The comment before a run section's first `[[run.mutation]]`: what a row is and what each status
/// says.
pub const MUTATIONS_LEGEND: &[&str] = &[
    "Each [[run.mutation]] is a mutation of the list, by its id, and its verdict: killed (a",
    "program's result differs on the mutant; `killer` names it), survived (every program agreed;",
    "`horizon`, those that agreed only up to an observation horizon), equivalent or unkillable (no",
    "program can tell the mutant apart), timeout, unknown or error (no verdict), invalid-mutation",
    "or not-admitted (its author must fix it; `reason` says why).",
];

/// The comment before a coverage rendering's first family: what `open`, `argued` and
/// `undecided` list, and what each standing says.
pub const FAMILIES_LEGEND: &[&str] = &[
    "Each family lists its obligations by id: `open`, those no program covers; `argued`, those an",
    "argument of FLOW.toml ([[coverage.argued]]) stands in for, each with the `standing` it rests",
    "on (text: its text alone; connected, checked-on-runs or proved: its invariant's checks hold;",
    "unchecked: a check did not decide); `undecided`, those the records cannot decide.",
];

/// The comment before `[coverage.flips]` where the flips ran: what a `[[coverage.flip]]` is and what each status
/// says.
pub const FLIPS_LEGEND: &[&str] = &[
    "Each [[coverage.flip]] is a condition flip: a mutant kink generates from the definition by",
    "negating one condition (`negates`, as the source writes it) or toggling one bit of an encoding",
    "(`toggles`) in the `rules` it lists, and runs as `run` runs a mutation. Its status:",
    "distinguished (a program's result differs on it; `killer` names it), undistinguished (every",
    "comparable program agreed), unreached (no program reaches the condition), argued (an",
    "argument stands in for a program; its `standing`), equivalent (no program can tell it",
    "apart), refused (the flipped definition is not admitted; `reason`), unknown (no verdict).",
];

/// The comment before `[coverage.flips]` where they did not run.
pub const FLIPS_NOT_RUN: &[&str] =
    &["No condition flip ran: the front end derives none, or `--tier 1` runs none."];

/// The rendering of a `coverage` or `run` document (module documentation). The error names what
/// the document is when it is neither: for `report`'s document saying why there is no stored run
/// document (`kink-flow-report`), why there is none, so that `report --output verdicts` states
/// the reason where the rendering would have been.
pub fn verdicts(document: &Value) -> Result<String, String> {
    render(document, true)
}

/// The text of a lock that holds only `document`'s section: the rendering without `killed_by`
/// (a run's), so that a first-kill and a full run of the same inputs write the same bytes, and for
/// a first-kill run `run --output verdicts` and `report --output verdicts` are the bytes of a lock
/// only `run` has written; `coverage --output verdicts` those of a lock only `coverage` has. The
/// error names what the document is when it is neither.
pub fn lock_text(document: &Value) -> Result<String, String> {
    lock_section(document).map(|section| format!("{}\n{section}", record_header()))
}

/// The section of a lock that `document`'s command keeps (`[run]`, `[coverage]` and its
/// sub-tables, [`crate::lock`]): its part of [`lock_text`] after the record's header, from its
/// `[run]` or `[coverage]` line, ending with one newline. The error names what the document is
/// when it is neither a run nor a coverage document.
pub fn lock_section(document: &Value) -> Result<String, String> {
    let schema = &document["schema"];
    if schema != crate::report::RUN_SCHEMA
        && schema != crate::coverage::COVERAGE_SCHEMA
        && schema != crate::compare::COMPARE_SCHEMA
        && schema != crate::query::QUERY_SCHEMA
    {
        return Err(
            "a lock is the rendering of a run, coverage, compare or query document".to_owned(),
        );
    }
    let kind = section_name(document)?;
    Ok(section(document, kind, false))
}

/// The header of a record, before its first section: [`RECORD_PREAMBLE`] and `schema`. It holds
/// only what is the same for every section by construction: each section states its own version,
/// solver profile, Z3 build and specification, since each command writes its section at its own
/// time, on the build it runs on, and keeps the other section as it is.
#[must_use]
pub fn record_header() -> String {
    let mut text = String::new();
    comment(&mut text, RECORD_PREAMBLE);
    line(&mut text, "schema", &string(VERDICTS_SCHEMA));
    text
}

fn render(document: &Value, killed_by: bool) -> Result<String, String> {
    let kind = section_name(document)?;
    Ok(format!(
        "{}\n{}",
        record_header(),
        section(document, kind, killed_by)
    ))
}

/// The section a document renders as (`run`, `coverage`), or why it renders as none.
fn section_name(document: &Value) -> Result<&'static str, String> {
    match document["schema"].as_str() {
        Some(crate::coverage::COVERAGE_SCHEMA) => Ok("coverage"),
        Some(crate::report::RUN_SCHEMA) => Ok("run"),
        Some(crate::compare::COMPARE_SCHEMA) => Ok("compare"),
        Some(crate::query::QUERY_SCHEMA) => Ok("query"),
        Some(crate::report::MISSING_SCHEMA) => Err(match document["outcome"].as_str() {
            Some(outcome) => format!(
                "{outcome} run report {}: {}",
                document["path"].as_str().unwrap_or("?"),
                document["detail"].as_str().unwrap_or("no detail")
            ),
            // The manifest, or what a front end needs before it, was refused.
            None => format!(
                "no run report is read: {}",
                refusal_details(document).join("; ")
            ),
        }),
        other => Err(format!(
            "--output verdicts renders a coverage, run or compare document, not {}",
            other.map_or_else(|| "a document with no schema".to_owned(), str::to_owned)
        )),
    }
}

/// The section `kind` (`run`, `coverage`) of `document` (module documentation).
fn section(document: &Value, kind: &str, killed_by: bool) -> String {
    let mut text = format!("[{kind}]\n");
    comment(
        &mut text,
        match kind {
            "coverage" => COVERAGE_PREAMBLE,
            "compare" => COMPARE_PREAMBLE,
            "query" => QUERY_PREAMBLE,
            _ => RUN_PREAMBLE,
        },
    );
    line(&mut text, "version", &VERDICTS_VERSION.to_string());
    if let Some(value) = document["profile"].as_str() {
        line(&mut text, "profile", &string(value));
    }
    // The Z3 build, which a document has under the Z3 profile only (`crate::with_z3_build`); its
    // digest when the build could name its library.
    if let Some(version) = document["z3"]["version"].as_str() {
        line(&mut text, "z3_version", &string(version));
    }
    if let Some(digest) = document["z3"]["library_sha256"].as_str() {
        line(&mut text, "z3_library_sha256", &string(digest));
    }
    // FB45-KINK: the work budget a run's verdicts were decided under (a coverage section names
    // it in its settings).
    if kind == "run"
        && let Some(factor) = document["work_factor"].as_u64()
    {
        line(&mut text, "work_factor", &factor.to_string());
    }
    if kind == "coverage"
        && let Some(annotation) = document["krs"]["version"].as_u64()
    {
        line(&mut text, "krs_annotation", &annotation.to_string());
    }
    // The protocol every request of the section was written in and every answer read by.
    if kind == "compare"
        && let Some(protocol) = document["protocol"].as_str()
    {
        line(&mut text, "protocol", &string(protocol));
    }
    // A compare document refused before any run says so under `[compare.refusal]`.
    let tables: &[&str] = match kind {
        "compare" => &["spec", "refusal", "lock"],
        "query" => &["spec", "lock"],
        _ => &["spec", "mutation_list", "lock"],
    };
    for &table in tables {
        let Some(object) = document[table].as_object() else {
            continue;
        };
        // A run's lock is rendered only when it was refused; otherwise it is the run's state,
        // not a verdict.
        if table == "lock" && object.get("outcome").and_then(Value::as_str) != Some("refused") {
            continue;
        }
        let _ = write!(text, "\n[{kind}.{table}]\n");
        for key in ["outcome", "stage", "reason"] {
            if let Some(value) = object.get(key).and_then(Value::as_str) {
                line(&mut text, key, &string(value));
            }
        }
    }
    match kind {
        "coverage" => coverage(&mut text, document),
        "compare" => compare(&mut text, document),
        "query" => obligations(&mut text, document),
        _ => mutations(&mut text, document, killed_by),
    }
    if let Some(stopped) = document["stopped"].as_object() {
        let _ = write!(text, "\n[{kind}.stopped]\n");
        for key in ["mutation", "reason"] {
            if let Some(value) = stopped.get(key).and_then(Value::as_str) {
                line(&mut text, key, &string(value));
            }
        }
    }
    text
}

/// The texts of a document's refusals and of the stop of its run, which [`verdicts`] leaves out
/// (`spec`, `mutation_list`: `<section>: <stage or outcome> <reason>: <detail>`; a mutation its
/// author must fix: `mutation <id>: <status> <reason>: <detail>`, its `action` when it has no
/// `detail`; a stopped run: `stopped at
/// <mutation>: <reason>: <detail>`), for a front end to print beside the rendering (`kink-flow`
/// prints them on stderr).
#[must_use]
pub fn refusal_details(document: &Value) -> Vec<String> {
    let mut details = Vec::new();
    for section in ["spec", "mutation_list", "lock"] {
        let object = &document[section];
        if object["outcome"] != "refused" {
            continue;
        }
        let what = [&object["stage"], &object["reason"]]
            .into_iter()
            .filter_map(Value::as_str)
            .collect::<Vec<_>>()
            .join(" ");
        let what = if what.is_empty() {
            "refused".to_owned()
        } else {
            what
        };
        details.push(format!(
            "{section}: {what}: {}",
            object["detail"].as_str().unwrap_or("no detail")
        ));
    }
    for row in document["mutations"].as_array().into_iter().flatten() {
        if refused_mutation(row) {
            details.push(format!(
                "mutation {}: {} {}: {}",
                row["id"].as_str().unwrap_or("?"),
                row["status"].as_str().unwrap_or("?"),
                row["reason"].as_str().unwrap_or("?"),
                row["detail"]
                    .as_str()
                    .or_else(|| row["action"].as_str())
                    .unwrap_or("no detail")
            ));
        }
    }
    if let Some(stopped) = document["stopped"].as_object() {
        let mutation = stopped.get("mutation").and_then(Value::as_str);
        let row = document["mutations"]
            .as_array()
            .into_iter()
            .flatten()
            .find(|row| mutation.is_some_and(|id| row["id"] == id));
        details.push(format!(
            "stopped at {}: {}: {}",
            mutation.unwrap_or("?"),
            stopped.get("reason").and_then(Value::as_str).unwrap_or("?"),
            row.and_then(|row| row["detail"].as_str())
                .unwrap_or("no detail")
        ));
    }
    details
}

/// A coverage document's settings, each family's open, argued and undecided ids, and the flips
/// (module documentation); nothing for a refused specification, which has no families.
fn coverage(text: &mut String, document: &Value) {
    let settings = &document["settings"];
    if settings.is_object() {
        // No `tiers`: a lock is written only where both tiers ran, and `[flips] run` says whether
        // tier 2 did.
        text.push_str("\n[coverage.settings]\n");
        line(text, "depth", &settings["depth"].to_string());
        let mcdc = if settings["mcdc"] == true {
            "true".to_owned()
        } else {
            strings(
                &settings["mcdc"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .filter_map(Value::as_str)
                    .map(str::to_owned)
                    .collect::<Vec<_>>(),
            )
        };
        line(text, "mcdc", &mcdc);
        // FB45-KINK: the work budget a flip's verdict was decided under.
        if let Some(factor) = settings["work_factor"].as_u64() {
            line(text, "work_factor", &factor.to_string());
        }
    }
    if !document["families"].is_object() {
        return;
    }
    let standings = crate::coverage::argument_standings(document)
        .into_iter()
        .collect::<std::collections::BTreeMap<_, _>>();
    let standing = |id: &str| {
        standings
            .get(id)
            .map_or(crate::coverage::STANDING_TEXT, String::as_str)
    };
    let argued = crate::coverage::argued_ids(document);
    let undecided = crate::coverage::undecided_ids(document);
    text.push('\n');
    comment(text, FAMILIES_LEGEND);
    let mut first = true;
    for (((family, open), (_, argued)), (_, undecided)) in crate::coverage::open_ids(document)
        .into_iter()
        .zip(argued)
        .zip(undecided)
    {
        if !first {
            text.push('\n');
        }
        first = false;
        let _ = writeln!(text, "[coverage.{family}]");
        line(text, "open", &strings(&open));
        // Each argued item once, with the standing its argument rests on.
        let argued = argued
            .iter()
            .map(|id| {
                format!(
                    "{{ id = {}, standing = {} }}",
                    string(id),
                    string(standing(id))
                )
            })
            .collect::<Vec<_>>();
        line(text, "argued", &list(&argued));
        if !undecided.is_empty() {
            line(text, "undecided", &strings(&undecided));
        }
    }
    let flips = &document["families"]["flips"];
    if flips.is_object() {
        let ran = flips["run"].as_bool().unwrap_or(false);
        text.push('\n');
        comment(text, if ran { FLIPS_LEGEND } else { FLIPS_NOT_RUN });
        text.push_str("[coverage.flips]\n");
        line(text, "run", &ran.to_string());
    }
    for item in flips["items"].as_array().into_iter().flatten() {
        text.push_str("\n[[coverage.flip]]\n");
        let id = item["id"].as_str().unwrap_or_default();
        line(text, "id", &string(id));
        // What the mutant changes: the condition as the source writes it, and the rules it edits
        // by their ids in the rules family, so that the id needs no other document to resolve.
        if let Some(condition) = item["text"].as_str() {
            let key = if item["operator"] == "bitflip" {
                "toggles"
            } else {
                "negates"
            };
            line(text, key, &string(condition));
        }
        if let Some(sentences) = item["sentences"].as_array() {
            let rules = sentences
                .iter()
                .filter_map(|sentence| sentence["rule"].as_str().map(str::to_owned))
                .collect::<Vec<_>>();
            line(text, "rules", &strings(&rules));
        }
        let rendered = rendered_flip(item);
        for key in ["status", "reason", "killer"] {
            if let Some(value) = rendered[key].as_str() {
                line(text, key, &string(value));
            }
        }
        if rendered["status"] == crate::coverage::ARGUED {
            line(text, "standing", &string(standing(id)));
        }
        if let Some(horizons) = rendered["horizon"].as_array() {
            line(text, "horizon", &rendered_horizons(horizons));
        }
    }
}

/// What a coverage rendering writes of a flip item, beside its id: `{status, killer, reason,
/// horizon}`, a refused flip's `reason`, a distinguished flip's `killer` and an undistinguished
/// flip's `horizon` (its run row's, [`rendered_horizons`]), null where the rendering writes none
/// (module documentation).
#[must_use]
pub fn rendered_flip(item: &Value) -> Value {
    let status = item["status"].as_str().unwrap_or_default();
    let only = |wanted: &str, key: &str| {
        if status == wanted {
            item[key].as_str().map_or(Value::Null, |value| json!(value))
        } else {
            Value::Null
        }
    };
    json!({
        "status": status,
        "killer": only(crate::flips::DISTINGUISHED, "killer"),
        "reason": only(crate::flips::REFUSED, "reason"),
        "horizon": if status == crate::flips::UNDISTINGUISHED {
            item["horizon"].clone()
        } else {
            Value::Null
        },
    })
}

/// A survivor's agreements up to a horizon (a run row's `horizon`, `[{program, horizon:
/// {<channel>: {elements, opening}}}]`) as a rendering writes them: one inline table per program
/// and channel, `{ program, channel, elements, opening }`, one per line ([`list`]).
fn rendered_horizons(horizons: &[Value]) -> String {
    let items = horizons
        .iter()
        .flat_map(|entry| {
            let program = entry["program"].as_str().unwrap_or_default();
            entry["horizon"]
                .as_object()
                .into_iter()
                .flatten()
                .map(move |(channel, at)| {
                    format!(
                        "{{ program = {}, channel = {}, elements = {}, opening = {} }}",
                        string(program),
                        string(channel),
                        at["elements"].as_u64().unwrap_or_default(),
                        string(at["opening"].as_str().unwrap_or_default())
                    )
                })
        })
        .collect::<Vec<_>>();
    list(&items)
}

/// Whether a run document's row is of a mutation its author must fix before it is judged:
/// `invalid-mutation` or `not-admitted` ([`crate::cli::invalid_mutations`]).
fn refused_mutation(row: &Value) -> bool {
    matches!(
        row["status"].as_str(),
        Some(crate::search::INVALID_MUTATION | "not-admitted")
    )
}

/// The reason a rendering writes for a run document's row: the reason of a mutation its author
/// must fix ([`refused_mutation`]), else none (module documentation).
#[must_use]
pub fn rendered_reason(row: &Value) -> Value {
    if refused_mutation(row) {
        row["reason"].clone()
    } else {
        Value::Null
    }
}

/// Each mutation's id and status, the reason of one its author must fix ([`refused_mutation`]),
/// a killed mutation's `killer`, and with `killed_by` a full row's `killed_by` (module
/// documentation).
fn mutations(text: &mut String, document: &Value, killed_by: bool) {
    let rows = document["mutations"]
        .as_array()
        .map_or(&[][..], Vec::as_slice);
    if !rows.is_empty() {
        text.push('\n');
        comment(text, MUTATIONS_LEGEND);
    }
    for (index, row) in rows.iter().enumerate() {
        text.push_str(if index == 0 {
            "[[run.mutation]]\n"
        } else {
            "\n[[run.mutation]]\n"
        });
        line(text, "id", &string(row["id"].as_str().unwrap_or_default()));
        line(
            text,
            "status",
            &string(row["status"].as_str().unwrap_or_default()),
        );
        if let Some(reason) = rendered_reason(row).as_str() {
            line(text, "reason", &string(reason));
        }
        // A survivor some program of which agreed only up to its baseline's horizon: each such
        // program's channels, the elements they agreed on and why each opened.
        if let Some(horizons) = row["horizon"].as_array() {
            line(text, "horizon", &rendered_horizons(horizons));
        }
        if row["status"] != "killed" {
            continue;
        }
        if let Some(killer) = row["killer"].as_str() {
            line(text, "killer", &string(killer));
        }
        if killed_by && let Some(killers) = row["killed_by"].as_array() {
            let killers = killers
                .iter()
                .filter_map(Value::as_str)
                .map(str::to_owned)
                .collect::<Vec<_>>();
            line(text, "killed_by", &strings(&killers));
        }
    }
}

/// A compare section's rows (`[[compare.verdict]]`), in the order [`crate::compare::verdict_rows`]
/// gives them: each row's `implementation`, `program`, `view`, `required` and `verdict`, then its
/// `reason`, `difference`, `request_sha256` and `identity_sha256` where it has them. The rows are
/// `document`'s `verdicts` where a lock set them ([`crate::compare::keep`]), else its live rows.
fn compare(text: &mut String, document: &Value) {
    let rows = match document["verdicts"].as_array() {
        Some(rows) => rows.clone(),
        None => crate::compare::verdict_rows(document),
    };
    if !rows.is_empty() {
        text.push('\n');
        comment(text, COMPARE_LEGEND);
    }
    for (index, row) in rows.iter().enumerate() {
        text.push_str(if index == 0 {
            "[[compare.verdict]]\n"
        } else {
            "\n[[compare.verdict]]\n"
        });
        for key in ["implementation", "program", "view"] {
            line(text, key, &string(row[key].as_str().unwrap_or_default()));
        }
        line(text, "required", &(row["required"] == true).to_string());
        line(
            text,
            "verdict",
            &string(row["verdict"].as_str().unwrap_or_default()),
        );
        if let Some(reason) = row["reason"].as_str() {
            line(text, "reason", &string(reason));
        }
        if let Some(difference) = row["difference"].as_str() {
            line(text, "difference", &literal(difference));
        }
        for key in ["request_sha256", "identity_sha256"] {
            if let Some(digest) = row[key].as_str() {
                line(text, key, &string(digest));
            }
        }
    }
}

/// A query section's rows (`[[query.pattern]]`), one per obligation of `document`, in the pattern
/// list's order: each row's `id` and `status`, and its `witness` where it has one.
fn obligations(text: &mut String, document: &Value) {
    let rows = document["obligations"]
        .as_array()
        .map_or(&[][..], Vec::as_slice);
    if !rows.is_empty() {
        text.push('\n');
        comment(text, QUERY_LEGEND);
    }
    for (index, row) in rows.iter().enumerate() {
        text.push_str(if index == 0 {
            "[[query.pattern]]\n"
        } else {
            "\n[[query.pattern]]\n"
        });
        for key in ["id", "status", "witness"] {
            if let Some(value) = row[key].as_str() {
                line(text, key, &string(value));
            }
        }
    }
}

/// A TOML literal string of `value` where it can be one (no `'` and no control character), so
/// that a JSON text reads as itself; else a basic string.
fn literal(value: &str) -> String {
    if value.contains('\'') || value.chars().any(char::is_control) {
        string(value)
    } else {
        format!("'{value}'")
    }
}

fn line(text: &mut String, key: &str, value: &str) {
    let _ = writeln!(text, "{key} = {value}");
}

/// `lines` as TOML comments, each `# <line>` (`#` alone for an empty one).
fn comment(text: &mut String, lines: &[&str]) {
    for line in lines {
        if line.is_empty() {
            text.push_str("#\n");
        } else {
            let _ = writeln!(text, "# {line}");
        }
    }
}

/// A TOML basic string.
fn string(value: &str) -> String {
    toml::Value::String(value.to_owned()).to_string()
}

/// A TOML array of basic strings, one per line ([`list`]).
fn strings(values: &[String]) -> String {
    let items = values.iter().map(|value| string(value)).collect::<Vec<_>>();
    list(&items)
}

/// A TOML array of rendered values, opening on its key's line, each value on a line of its own
/// with a trailing comma, and `]` on its own line, an empty array included (`key = [` then `]`):
/// adding or removing a value adds or removes its line and moves no other, and the transitions to
/// and from an empty array do too, so a lock's diff is the lines of the values that changed.
pub(crate) fn list(items: &[String]) -> String {
    let mut text = "[\n".to_owned();
    for item in items {
        let _ = writeln!(text, "  {item},");
    }
    text.push(']');
    text
}
