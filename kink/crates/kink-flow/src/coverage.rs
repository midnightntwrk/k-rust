//! `coverage`: what the corpus covers of the obligations the specification states, family by
//! family, each obligation covered or open, and each open one stated as a target an agent can
//! act on (README, "kink-flow coverage").
//!
//! An obligation is an item derived from the definition alone, before any program runs, so each
//! family's universe is a function of the definition and the document states its size. An
//! obligation is covered when the cached baseline run of some comparable program shows the
//! family's predicate ([`crate::results`], the result cache): a program that cannot be compared
//! can kill nothing, so it tests nothing, and an item only such programs touch lists them as
//! `touched_only_by`, its target then being to make one comparable. Coverage of a family is set
//! arithmetic over the records, so adding a program runs that program alone.
//!
//! # Families
//!
//! Every family shares one scope ([`scope`]): a simplification, `symbolic` or ceil equation, a
//! rule k-rust's coverage cannot name, and a claim helper are no obligation of any family, each
//! read from the definition and the front end's marks before any program runs.
//!
//! - `rules`: every authored rewrite rule and function equation (`owise`, `anywhere` and the
//!   authored equations of an overloaded function included), and every heating rule the compile
//!   generates from a `strict` or `seqstrict` production (one per argument position the
//!   attribute names, and per context alias it uses) or a `context` sentence, attributed to that
//!   sentence and position ([`heating_item`]). An item's status is named for the
//!   predicate it tests ([`FIRED`], [`MATCHED`], [`UNMATCHED`]), read from the records as the
//!   result cache keeps them, or from the front end's reading where it reads a sentence's match
//!   at its own level (`krs.status`); a rule is covered when it is `fired`. A heating rule fires
//!   where a run put a term that is not a result at its position, the one situation the
//!   attribute governs; its cooling rule follows wherever that term's evaluation reaches a
//!   result, and is shown with the item, not counted. The family's counts give the heating items
//!   apart (`counts.heating`). Simplification,
//!   `symbolic` and ceil equations are [`OUT_OF_SCOPE`]: they state facts of the definition's
//!   functions that the definition means the same without, so no program's run of one tests
//!   anything a step computes. A claim helper ([`CLAIM_HELPER`]) serves the claims, which a
//!   proof checks, and a rule k-rust's coverage cannot name ([`NO_COVERAGE_SIGNAL`]) cannot be
//!   shown matched; neither is an obligation. These three exclusions are the scope every family
//!   shares ([`scope`]), read from the definition and the front end's marks alone, so a claim
//!   helper a typed input applied is still no obligation. The measure is fired / (fired +
//!   matched + unmatched).
//! - `requirements`: for each guarded rule of the rules universe whose condition has an
//!   authored conjunct, each distinct (node, truth) pair of the condition's root and of each
//!   authored operand node with outcomes of its own (an atom, or an exclusive connective;
//!   [`crate::guards::own_outcomes`]): the root `held` and `refuted`, a node `true` and `false`.
//!   A node's truth is covered when some comparable program reached the node with that truth, a
//!   node being reached, in written order, only where the operands before it decide nothing yet
//!   (a conjunction's earlier operands `true`, a disjunction's `false`); so the reached truths
//!   per node encode the short-circuit outcome classes of every connective, and one unit serves
//!   them all. A function equation's condition is reached at every application its left-hand
//!   side matches whose deciding priority group is its own, whether or not the run tried it
//!   there (k-rust's untried entries), so its requirements do not depend on the order in which
//!   the backend tries the equations of a group; an untried entry the evaluation left open is
//!   undecided (cause `untried`), never covered. Where the root's truth is reached exactly where
//!   a node is reached with a truth (a root that is itself an atom, a conjunction's `held` and
//!   its last conjunct `true`, a condition's only conjunct), the two are one obligation, listed
//!   once as the root's, with the node (`node`, `node_truth`) and the programs of both.
//!   Undefined and undecided outcomes, the tests a front end inserted and a pattern's templates
//!   are shown apart and never counted.
//!   Where a front end grouped a guard by its own constructs (`guard.krs`), its authored operands
//!   and its reading of the author's condition are read; a condition with no authored conjunct
//!   states no requirement. The nodes are read from the definition's skeleton of the condition
//!   ([`crate::guards::row_guard`]), so the universe does not depend on which programs entered
//!   it; a condition whose skeleton cannot be read shows no node and says why
//!   (`guard.operands_reason`), its requirements being its root's alone.
//! - `syntax` (depth 1): each production of an authored sort, reached or unreached. The
//!   authored sorts are a front end's where it gives them (`FlowManifest::syntax`), else every
//!   sort the specification's own sentences declare and no library sentence does; a production
//!   is an obligation when it builds a term with a constructor of the compiled definition (no
//!   function, token, bracket, subsort, macro or cell does), so the universe is a function of the
//!   definition and the front end's selection. A production is reached when a fired instance of
//!   an authored rule of the rules universe, in some comparable program's run, touched it (a
//!   heating step touches its own production by construction, which its rules item already
//!   states, so it does not count here): the
//!   production is at a non-variable position of the sentence's left-hand side (inspected), it
//!   is the head, through injections, of a value the instance bound to a left-hand-side variable
//!   that the sentence reads elsewhere (an operand), or it is at a non-variable position of the
//!   right-hand side (built). A production elsewhere in a state was carried, not touched, and so
//!   was the value of a variable the sentence binds and never reads (`_` in a cell it
//!   overwrites): the step is the same whatever it holds. The initial state holds the whole
//!   program, so "anywhere in a reached state" would read every production of a branch no run
//!   took as reached, and "at the head of `<k>`" would miss the values a step passes to a
//!   function or keeps in a cell. Only the head of a bound value counts, so a continuation,
//!   whose head is the sequence's, never counts the rest of a program. Inspected and built are
//!   static per axiom alternative (kink-native `syntax_facts`), joined with the run's fired
//!   sentences, and, for an axiom with several alternatives (a disjunctive left-hand side, a
//!   function equation's readings, a rewrite rule's disjunctive right-hand side), with the
//!   alternatives its fired instances took; the operand heads and those alternatives are
//!   recorded by the backend at the fired instance (the result record's `bindings`). The measure is reached / obligations, productions and field values counted
//!   together and each apart. kink-flow's K front end has no notion of a `k::bits!` template, so
//!   it selects no template binder and builds no field-value item: a front end that has
//!   templates selects their binders (`SyntaxSelection::binders`), whose values the records keep
//!   and the family lists (`binders`), and adds an item of kind [`FIELD_VALUE`] per field value
//!   of its universe, with its status, its target's text, and the binder it reads with the
//!   binder's values at which the field has the value (`binder = {axiom, variable, encodings}`,
//!   the encodings hexadecimal points and runs `0xA-0xB`), before [`derive`].
//! - `rule_windows` (depth `d` above 1, `[coverage] depth` or `--depth`; `null` at depth 1): each
//!   window of length `2..=d` of the may-follow graph of the rules family's authored rewrite
//!   rules, covered or open. A window is a sequence of rewrite rules some path takes as
//!   consecutive committed steps; its windows of length 1 are the rules family's fired rules, so
//!   the family starts at 2. Equations take no step, so none is in a window. Rule `B` may follow
//!   rule `A` when `A`'s right-hand side unifies with `B`'s left-hand side, every function
//!   application, builtin-domain value and collection read as a fresh variable, conditions
//!   ignored (kink-native `coverage::may_follow`): the successor of a step of `A` keeps every
//!   free constructor of `A`'s right-hand side, so a rule that can take the next step has a
//!   left-hand side that unifies with it, and the universe over-approximates what can be taken.
//!   A window that no run can take is argued (`[[coverage.argued]]`); a window containing a part
//!   that is argued while open (a rule, or a shorter window) is `argued` by it (`argued_by`),
//!   since a path that takes the window takes the part. The universe is a function of the
//!   definition; its size is computed before any program runs, and a universe above
//!   `[coverage] max_obligations` is refused (reason `max-obligations`) with its counts by
//!   length. A window is covered when a comparable program's record holds it (the record's
//!   `coverage.windows`, which k-rust collects exactly, a state-set run's merged arrivals
//!   included). The measure is covered / obligations over every length (`counts.by_length` per
//!   length). A record collected at depth `D` lists every window up to `D`, so it answers every
//!   depth up to `D`; a command of a greater depth runs the program again and replaces the
//!   record (`crate::results::record_answers`). A window of authored rules that a comparable
//!   record holds and the graph lacks would be a failure of the over-approximation; it is listed
//!   as `outside_universe` and not counted.
//! - `syntax_paths` (depth `d` above 1; `null` at depth 1): each path of length `2..=d` of the
//!   grammar graph of the syntax family's productions, reached or unreached. A path `(P1, i1,
//!   P2, ..., Pn)` is a sequence of productions along consecutive argument positions, `P(j+1)`
//!   at argument `ij` (0-based) of `Pj`. It is reached when a fired instance of a sentence of the
//!   rules universe (so in the shared scope: a claim helper's instance reaches none), in some
//!   comparable program's run, touched it: it starts at a position the
//!   syntax family counts as touched (a non-variable position of the left-hand or right-hand
//!   side, or the root of a value bound to a variable the sentence reads) and descends through
//!   argument positions of the left-hand side or the right-hand side under the instance's
//!   substitution (k-rust's `bindings.paths`, which the record's `coverage.bindings.paths`
//!   keeps). So the paths of length 1 are the syntax family's reached productions, and a path
//!   lies within `d - 1` positions below a touched one: a value is walked no further than the
//!   paths it can start or continue need, and nothing below its root starts a path, since the
//!   step touched the root only. A function application, a cell, a `K` sequence, a collection
//!   or a builtin value breaks a path: its elements are items of their own at depth 1, where the
//!   sentence writes them. Every length is read the same way at every depth, so a record
//!   collected at `D` answers every depth up to `D`, as for the rule windows. `Q` may stand at
//!   argument `i` of `P` when `Q`'s sort is at or below the sort of `P`'s argument `i` (kink-native
//!   `coverage::grammar_graph`): a well-sorted term holds `Q` there directly or below a subsort
//!   injection, so every path a run records is a walk of the graph, which over-approximates what
//!   a run can touch; a path a comparable record holds and the graph lacks would be a failure of
//!   that argument, listed as `outside_universe` and not counted. The universe is a function of
//!   the definition and the front end's selection; its size is computed before any program
//!   runs and held to `[coverage] max_obligations` as the rule windows' is. A path is on the
//!   frontier when it is unreached and its prefix of length `n - 1` is reached (a production of
//!   the syntax family for `n = 2`); only those have targets. A path whose first production, or
//!   one of whose prefixes, is argued while open is argued by it (`argued_by`): an instance
//!   records only paths that start at a position it touched, and with a path each of its
//!   prefixes. A later production of a path is no such part, since it lies below a touched
//!   position without being touched. A front end with templates adds, at depth 2 and above, the
//!   joint values of each template's fields as items of kind [`FIELD_VALUES`] (the paths of
//!   length 2 through the template: its fields are its arguments), each with its frontier, its
//!   target's text and the field values it joins (`krs.parts`), an argued one of which argues it.
//!   The measure is reached / obligations over every length (`counts.by_length`), the paths and
//!   the joint field values also apart (`counts.paths`, `counts.field_values`).
//! - `flips` (tier 2, condition flips; [`crate::flips`]): each flip a front end derives from the
//!   definition's source ([`crate::cli::FrontEnd::derived`]) that changes only sentences in the
//!   scope is an obligation (one that changes a sentence outside it is listed under
//!   `not_generated`, decided before any run), `distinguished`
//!   where the kill search kills its mutant (with its `killer`), `undistinguished` where it runs
//!   on every comparable program without a kill, `unreached` where no comparable program reached
//!   an occurrence of the flipped atom (deduced from the guard rows and the front end's match,
//!   with no mutant run), `unknown` without a verdict (with each executed program's cause),
//!   `refused` by a judge, and `equivalent`
//!   where kink proves no program distinguishes it. The measure is distinguished over the
//!   obligations less the refused and equivalent ones, which no program can meet. The family runs
//!   under tier 2 (the default) where the front end derives the flips; otherwise, and under
//!   `--tier 1`, it has `run: false`, the reason, and under `--tier 1` its number of obligations,
//!   with no status.
//!
//! The measure is per family. No weighted total is given, since nothing weighs a rule against an
//! operand's truth; `summary.open`, the count of open targets, is the one scalar, and zero
//! means done (an open rule window off the frontier has no target of its own: it extends an open
//! rule or window, whose target comes first, and so does an open syntax path off the frontier).
//! Every item has a stable `id`: `rule:<name>`, `requirement:<name>:<detail>`,
//! `syntax:<production>`, `window:<rule>,<rule>,...` (each rule by its name) and
//! `path:<production>/<position>/<production>...` (each production by the name its syntax id
//! gives it, a front end's joint field values by the front end's name), the rule's name being its
//! KRS item where the front end named it, else
//! its label, else its `file:line` (with `:<label>` added where two rules share a name), a
//! heating rule's its production's (`<production>:heat:<position>`) or its context's
//! (`<context>:heat`, [`rule_name`]), the
//! detail `held`, `refuted`, or the node's text (with `@<path>` added where two nodes of one
//! condition share a text) and its truth, and the production its front end's name, else its K
//! label (with `@<sort>` added where two share one).
//!
//! # Targets
//!
//! One per open obligation, in tier, family, then sentence order: `{family, item, text, file,
//! line, programs, pattern, fuzz}`, a syntax target also with the `rules` that inspect or build
//! its production. An `unmatched` rule asks for a case whose run reaches a state
//! the rule matches; a `matched` one for a case that enters it with its condition holding,
//! naming the requirement that is open; a requirement for a case that enters the rule with the
//! valuation that reaches the node with the missing truth, read from the condition's structure,
//! each step an author's node and its truth (a negation restated as its operand with the other
//! truth, so an `else` reads as the condition before it `false`);
//! an unreached production for a case in which a step takes it as an operand, or inspects or
//! builds it, naming the rules that inspect or build it, each a concrete thing to make fire.
//! An open heating rule asks for a case whose run brings the production to the front of the
//! computation with a term that is not a result at its position (for a context, reaches a
//! state the context matches with such a term in its hole).
//! `programs` are the comparable programs that entered the rule, the templates of a fuzz job;
//! `fuzz` spells the fuzz job that looks for a program: for a rewrite rule `--matched` or
//! `--fired` with the rule, for a requirement, a production, a field value whose item names its
//! binder, a heating rule and a function equation `--cover` with the obligation's id
//! (`crate::fuzz_goal`), and `null` where none applies (a unique-cause requirement, which a pair
//! of entries covers, and a field value without a binder). A flip's target follows in tier 2: an
//! `undistinguished` flip asks for a case whose result changes when the atom is negated (a bit
//! toggled) in its sentences, naming the values of the atom the corpus reached, the programs that
//! reached it, and `fuzz --kill`; an `unreached` one asks for a case that reaches it and names
//! the open tier-1 obligations that explain it (`waits_on`); an `unknown` one asks for a
//! comparable run of its mutant, with kink's reason, else its status, and each executed
//! program's cause. `pattern` is, for an `unmatched` rewrite rule, its
//! left-hand side as a `PATTERNS.toml` pattern ([`rule_pattern`]), which `query` and
//! `fuzz --pattern` take; `null` for every other target, and where the rule's text cannot be
//! read or a front end matched the sentence through templates.
//!
//! A rule window's target is listed only on the frontier: an open window whose window of its
//! first rules is covered (for a window of two rules, whose first rule fired), so that a target
//! extends what the corpus already does; the measure counts every window. It asks for a case whose
//! run takes a step of the window's last rule right after its other rules, names the programs that
//! took those (the templates), and carries as `pattern` the unifier of the right-hand side of its
//! last rule but one with the left-hand side of its last rule, printed as K: the configurations a
//! step of the one leaves that the other can match. Its `fuzz` is `null`: no fuzz job's facts
//! name a window.
//!
//! A syntax path's target is likewise listed only on the frontier: it asks for a case in which a
//! fired step touches the path's first production holding the next at its argument, and so on,
//! names the programs that reached its prefix (the templates), and is placed at its first
//! production's declaration. A front end's joint field values state their target's text. Its
//! `pattern` and its `fuzz` are `null`: no fuzz job's facts name a path.
//!
//! # Argued obligations
//!
//! `[[coverage.argued]]` names obligations by id, each with an argument that stands in for the
//! program no one can write (`FlowManifest::coverage`). An argued open obligation has status
//! [`ARGUED`]: it stays in its family's obligations, so the measure (covered / obligations) does
//! not move, since an argument is no program and the measure states what the programs cover; it
//! is neither covered nor open, so it has no target, and `summary.open` counts only what is left
//! to cover or argue. The verdicts rendering lists the argued ids, so adding or removing an
//! argument moves the coverage lock. An entry no family lists is refused before any mutant runs
//! ([`stale_argued`]). An entry whose item a program covers, or that is no obligation, is a
//! needless argument, a finding ([`argue`]): kept, it would turn the item's next regression into
//! `argued` instead of `open`, hiding the gap the family exists to show.
//!
//! An entry's argument can rest on an invariant (`[[coverage.invariant]]`, named by the entry's
//! `invariant`): a Bool function of cells claimed of every state the baseline definition reaches.
//! Every argued item states what its argument rests on (`argument_check`) and its standing:
//! [`STANDING_TEXT`] without an invariant, else the outcome of the invariant's checks. A rewrite
//! rule's left-hand side is a whole configuration, so an invariant reads its cells there and
//! argues a `rule:` item of a rewrite rule or a held, refuted or node requirement of one; on any
//! other item it is refused before any mutant runs ([`unsupported_kind`]), and so is an invariant
//! no entry names ([`invariant_refusal`]). The front end then resolves each invariant's function
//! and cells to the definition's KORE symbol and cell paths ([`InvariantResolver`]), refusing one
//! it cannot resolve (`invariant-unresolved`, with the front end's message), one whose function's
//! result is not Bool (`invariant-not-bool`), and every invariant where it resolves none
//! (`invariant-unsupported-front-end`). Each argued item under an invariant is checked by its
//! connection (`invariants`, "The connection"): whether the invariant excludes, at the left-hand
//! side of each axiom of the item's rule, the valuation of each fact of a run's records that
//! would cover the item. A connection that holds shows only that the invariant excludes the item,
//! not that it holds of any state (an invariant false everywhere excludes everything), so the
//! item stays [`STANDING_UNCHECKED`], with the reason that the evidence is not run; one that is
//! undecided leaves it [`STANDING_UNCHECKED`] with the cause. The command then exits 3, since
//! nothing confirmed the claim it is done by; [`STANDING_CONNECTED`] needs the evidence on runs
//! too, which this build does not check. A connection that fails refutes the
//! argument: a state the rule matches satisfies the invariant and has the item's valuation, so the
//! argument stands in for nothing. The item goes back to its status, with its target, carries
//! `argument_failed` (`{check, detail}`), and the summary lists it in `failed_arguments`; the
//! command exits 1. The evidence of an invariant on runs is not checked
//! ([`CHECK_NOT_RUN`]). The verdicts rendering gives each argued item's standing, so a standing
//! that moves moves the coverage lock.
//!
//! # Unique-cause MC/DC
//!
//! `[coverage] mcdc` selects guarded rules by name (`true` selects every one), and each selected
//! rule whose condition states requirements gains a deeper level of them (`level` `mcdc`, id
//! `requirement:<name>:<operand>:mcdc`): one per authored atom of its condition. The obligation
//! of an atom `a` is a unique-cause pair: two valuation combinations the comparable programs'
//! runs recorded ([`crate::guards`], `guard.combinations`), one where the condition held and one
//! where it was refuted, in which `a` has the two truths and every other atom of the condition,
//! the tests a front end inserted and the conjuncts the compile added included, has one decided
//! truth. Such a pair shows `a` deciding the condition by itself: the condition with `a`
//! replaced by either constant differs from the condition on one of the pair's entries, so a
//! corpus that has the pair tells the condition from both conditions in which `a` decides
//! nothing. A pair in
//! which another atom also changes does not: in `A andThenBool B`, (true, true) held and (false,
//! false) refuted do not tell the condition from `B`. That is why every other atom is fixed, and
//! not only masked as the short-circuit reading would let it be: the outcome classes of the
//! default level already state what masking pairs would, and the deeper level states what they
//! cannot. A combination's atoms carry the strict reading's truths, also of an atom the
//! short-circuit reading did not reach, so the pair is read from the records with no run; an
//! `undecided` atom has no known truth, so it fixes nothing.
//!
//! An atom with a pair is `covered` by the programs of the pair (`pair`: each side's valuation,
//! outcome and programs). One without is `open`, or [`UNDECIDED`] where a comparable program's
//! record of the condition left a combination out (`truncated_by`): a record keeps the least
//! combinations up to a bound, so the pair may be among those it left out. An undecided
//! requirement is neither covered nor open (`counts.undecided`); it keeps its target, so
//! `summary.open`, what is left to settle, counts it. Its target and an open one's name the
//! valuation needed (`needed`): a recorded combination with the atom's truth negated, where the
//! condition, evaluated on the definition's skeleton of it, then takes the other outcome,
//! against the combination it pairs with. Where the atom is a function of the other atoms
//! (`X >Int 0` beside `X >Int 10`), no valuation can pair, and the obligation is argued
//! (`[[coverage.argued]]`). The requirements family gains `mcdc` (`rules`, the rule ids
//! selected, and the level's `obligations` and `covered`) and its counts `undecided`; a selected
//! rule's guard keeps its combinations and every other guard drops them, so without a selection
//! the document is what it was. A name that selects no rule whose condition states requirements
//! is refused before any mutant runs ([`stale_mcdc`]).
//!
//! The derived part of the document (every family but the rules' items, the targets and the
//! summary) is a function of the rules' items as the front end annotated them ([`derive`]), so a
//! front end that names rules and groups guards at its own level has its names in every id,
//! target and count.

use crate::{
    admit::admit_spec,
    cli::{CommandSpelling, FrontEnd, Verb, shell_word},
    digest::ExecutionDigest,
    evidence::EndReader,
    flips::{Derived, DerivedList, FLIPS_TIER_ONE, Judged},
    lock::{Lock, LockKind, Settle},
    manifest::FlowManifest,
    results::{
        BaselineRunner, ProgramRow, RESULT_SCHEMA_VERSION, ResultClass, cache_directory,
        data_marked, result_cache_value, runner_refusal, sentence_value, update_results,
    },
};
use k_rust::{
    definition::{AttributeKey, Sentence},
    kast::Term,
};
use kink_corpus::admission::{AdmissionRecord, AdmissionRefusal};
use kink_native::execution::SolverProfile;
use kink_patch::{SentenceRef, Sha256Digest};
use serde_json::{Map, Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    num::NonZeroU64,
    path::{Path, PathBuf},
};

mod invariants;
mod paths;
pub(crate) mod scope;
pub use invariants::{
    CONNECTION_FAILS, CONNECTION_HOLDS, CONNECTION_UNDECIDED, InvariantRefusal, InvariantResolver,
    KInvariants, ResolvedInvariant,
};
pub use paths::{FIELD_VALUES, PATH};
mod windows;

/// The `schema` of the coverage document.
pub const COVERAGE_SCHEMA: &str = "kink-flow-coverage";
/// The version of the coverage document: 1, the first, which replaces the results document (its
/// last version 11), whose program rows, rule rows and guard outcomes it holds; 2 since the
/// syntax family is built (`families.syntax`, its items, binders, counts and targets, and its
/// line of the summary), where version 1 had `null`; 3 since the flips family runs where a front
/// end derives the flips (`settings.tiers` `[1, 2]`, the family's items, counts, measure and
/// search, its targets and `summary.per_family.flips`); 4 since the document has its coverage
/// lock (`lock`, null without `--lock`) and each flip its `recorded_killer` and `killer_change`,
/// and `settings.depth` is the depth computed (`--depth`, else `[coverage] depth`); 5 since
/// `[observe]`: a corpus with observation channels names the declaration (`observe`, absent
/// without one), a program row carries the channels its baseline recorded and their horizons
/// (`observations`), and a program whose baseline its deterministic bounds cut is
/// `comparable-prefix`, a program that can kill by its channels; 6 since
/// `[[coverage.argued]]` is read: `settings.argued`, an argued item's status `argued` with its
/// `argument` and `unargued_status`, a needless argument's `argument_needless`, each family's
/// `argued` and `counts.argued`, and the summary's `covered` and `needless_arguments`; 7 since
/// each horizon names why its channel opened (a program row's `observations.horizon` is
/// `{<channel>: {elements, opening}}`, and each open channel's `open` has `opening`), each flip
/// has `horizon` (an undistinguished flip's agreements up to a horizon, null otherwise), a
/// prefix program none of whose channels kept an element within its budget or closed by a cycle
/// is `unknown`, and a program row's channel can be `closed` by `cycle`; 8 since
/// `[coverage] mcdc` is read: `settings.mcdc` may be `true`, and under a selection the selected
/// rules' guards keep their valuation combinations (`guard.combinations`), the requirements
/// family lists their unique-cause requirements (`level` `mcdc`, status `covered`, `open` or
/// `undecided`, with `pair`, `needed` and `truncated_by`), its counts have `undecided`, and it
/// has `mcdc`; without one the document is version 7's; 9 since the rules family lists the
/// heating rules the compile generates from `strict` and `seqstrict` productions and `context`
/// sentences: each rules item has `kind` (`rule`, or `heating` with `heating`), a heating item is
/// an obligation named `rule:<production>:heat:<position>` (`rule:<context>:heat`), its status
/// read from the records' `strictness`, and the family's counts have `heating`, so a reader of
/// version 8 would count obligations it does not know as rules; 10 since a program row's
/// `observations` for a run with several paths gives its prefix sets' facts, `{paths, real,
/// channels: [{name, complete_to}], horizon}`, where version 9 showed each channel open at 0 by
/// `branch` whatever was explored; 11 since a target's `fuzz` spells `fuzz --cover <item>` for
/// every open requirement but a unique-cause one, every unreached production, every unreached
/// field value whose item names its `binder` (`{axiom, variable, encodings}`, a front end's),
/// every open heating rule and every open function equation, where version 10 had `null`; 12
/// since a document of depth above 1 is computed instead of refused (`depth-unsupported`): it has
/// the rule windows family (`families.rule_windows`, its items, counts, measure, frontier
/// targets and `summary.per_family.rule_windows`), and a universe above `[coverage]
/// max_obligations` is refused (`max-obligations`); 13 since every family shares one static
/// scope: a claim helper is `claim-helper` whatever the programs did (in version 12 one some
/// program matched or fired was an obligation), with its `reason`, and a front end's flip that
/// changes only sentences outside the scope is listed under the flips family's `not_generated`
/// (`{reason, id, atom, sentences, pair, detail}`) instead of counted, so the denominators of the
/// rules, requirements, syntax and flips families can differ from version 12's on the same
/// definition; an `unknown` flip has `causes` (`[{program, cause}]`), which its target states
/// after its reason or its kink status; and a requirement's `reaching` restates each step
/// through negations (an `else`'s negation `true` is the condition before it `false`); 14 since
/// a document of depth above 1 also has the syntax paths family (`families.syntax_paths`, its
/// items, counts, measure, frontier targets and `summary.per_family.syntax_paths`), where
/// version 13 had `null`, its universe is held to `max_obligations` as well, and the text
/// rendering says a depth-dependent family is computed above depth 1 only where version 13 said
/// it was not built; 15 since a function equation is matched, and its requirements are
/// covered, at every application its left-hand side matches whose deciding priority group is its
/// own, whether or not the run tried it there (result schema v25), where version 14 read the
/// tried equations only, so that of two complementary equations the one tried second was never
/// refuted and, where the other applied, not matched; a rule's `matched_by`, and so its status, a
/// requirement's `entered_by` and a flip's reached occurrences, list the programs whose run
/// entered its condition, and an undecided requirement program can have the cause `untried`; 16
/// since an argued entry can name an invariant (`[[coverage.invariant]]`): `settings.invariants`
/// lists the declared invariants (`{name, function, cells, identity}`), each `settings.argued`
/// entry has `invariant`, every argued item has `argument_check`, what its argument rests on
/// (`{standing: "text"}`, or under an invariant `{invariant, standing: "unchecked", connection,
/// evidence, proof}`, no check yet run), the summary has `argued_by_standing` and
/// `failed_arguments`, a coverage lock's state has `argument_changes`, and the text rendering
/// states each argued item's standing; 17 since an argued item's invariant is checked by its
/// connection: each `settings.invariants` entry has the `identity` its front end resolved
/// (`{definition, symbol, cells}`, with the front end's own members), the document has
/// `argument_checks` (by item id, `{invariant, connection}`), an argued item's
/// `argument_check` has `reason` and `connection`, `{status, axioms, reason, model, cached,
/// smt_unknown}` with status `holds` or `undecided`, its standing `unchecked` either way while
/// the evidence is not run, and an item whose
/// connection `fails` is not argued: it keeps its status and target, has `argument_failed`
/// (`{check, detail}`), is listed in `summary.failed_arguments`, and the text lists it under
/// `failed arguments`.
pub const COVERAGE_VERSION: u64 = 17;

/// The status of a rule some comparable program fired.
pub const FIRED: &str = "fired";
/// The status of a rule some comparable program matched and none fired.
pub const MATCHED: &str = "matched";
/// The status of a rule no comparable program matched.
pub const UNMATCHED: &str = "unmatched";
/// The status of a simplification, `symbolic` or ceil equation: no obligation.
pub const OUT_OF_SCOPE: &str = "out-of-scope";
/// The status of a claim helper, an equation of a function only claims apply, whatever the
/// programs did: no obligation of any family ([`scope`]).
pub const CLAIM_HELPER: &str = "claim-helper";
/// The status of a rule none of whose compiled ids k-rust's run coverage can name: no
/// obligation.
pub const NO_COVERAGE_SIGNAL: &str = "no-coverage-signal";
/// The status of an obligation of any family that no program covers and `[[coverage.argued]]`
/// argues: counted in its family's obligations, neither covered nor open, and no target.
pub const ARGUED: &str = "argued";
/// The status of a unique-cause requirement no recorded pair covers while some program's record
/// of the condition left a valuation combination out: the record cannot say whether it is
/// covered. Not covered, not open; it keeps its target.
pub const UNDECIDED: &str = "undecided";
/// The standing of an argued item whose argument is its text alone: no invariant is named, so
/// nothing is checked (`argument_check.standing`; module documentation, "Argued obligations").
pub const STANDING_TEXT: &str = "text";
/// The standing of an argued item whose connection holds and whose evidence is vacuous.
pub const STANDING_CONNECTED: &str = "connected";
/// The standing of an argued item whose connection holds and whose evidence holds.
pub const STANDING_CHECKED_ON_RUNS: &str = "checked-on-runs";
/// The standing of an argued item whose invariant also has a valid proof.
pub const STANDING_PROVED: &str = "proved";
/// The standing of an argued item that names an invariant whose checks did not decide: a
/// connection not run or undecided, or an evidence not run or incomplete.
pub const STANDING_UNCHECKED: &str = "unchecked";
/// Every standing, in the order the summary's `argued_by_standing` lists them.
pub const STANDINGS: [&str; 5] = [
    STANDING_TEXT,
    STANDING_CONNECTED,
    STANDING_CHECKED_ON_RUNS,
    STANDING_PROVED,
    STANDING_UNCHECKED,
];
/// The status of a check of an argued item's invariant that this build does not run.
pub const CHECK_NOT_RUN: &str = "not-run";
/// The document member that holds, by argued item id, the connection of the item's invariant
/// (`{invariant, connection}`), which [`derive`] reads into each item's `argument_check`.
pub const ARGUMENT_CHECKS: &str = "argument_checks";
/// The check of an argued item whose refutation `argument_failed` names: the connection.
pub const CHECK_CONNECTION: &str = "connection";

/// Why an argued item's argument is needless (`argument_needless`): a program covers it.
pub const NEEDLESS_COVERED: &str = "covered";
/// Why an argued item's argument is needless: the item is listed but is no obligation.
pub const NEEDLESS_NOT_OBLIGATION: &str = "not-an-obligation";

/// The families of the document, in target order.
pub const FAMILIES: [&str; 6] = [
    "rules",
    "requirements",
    "syntax",
    "rule_windows",
    "syntax_paths",
    "flips",
];

/// The tiers a `coverage` command asks for. A document states only the tiers it computed
/// (`settings.tiers`): tier 2's one family, condition flips, is computed only where the front end
/// derives the flips ([`crate::flips`]).
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum Tier {
    /// `--tier 1`: the families read from the baseline runs alone; no mutant runs.
    One,
    /// `--tier 2` (the default): tier 1, and the condition flips run by the kill search.
    #[default]
    Two,
}

/// Options of the `coverage` command.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct CoverageOptions {
    /// Re-run every program that has a current record and compare (README 5.3).
    pub verify: bool,
    /// The cache directory; default `<directory of FLOW.toml>/.kink-flow`.
    pub cache: Option<PathBuf>,
    /// The tiers asked for.
    pub tier: Tier,
    /// `--depth N`: the depth asked for instead of `[coverage] depth`, for exploration.
    pub depth: Option<NonZeroU64>,
    /// `--lock FILE`: the coverage lock ([`crate::lock`], [`LockKind::Coverage`]), read for each
    /// flip's recorded killer and rewritten after a run with the manifest's own settings
    /// ([`command`]).
    pub lock: Option<PathBuf>,
    /// `--locked`: compare the run with its lock, and leave the lock unwritten.
    pub locked: bool,
}

impl CoverageOptions {
    /// The depth the command computes: `--depth`, else `[coverage] depth`.
    #[must_use]
    pub fn depth(&self, manifest: &FlowManifest) -> NonZeroU64 {
        self.depth.unwrap_or(manifest.coverage.depth)
    }
}

/// `kink-flow coverage`: the coverage document and whether the command found no corpus or
/// infrastructure error; the exit status joins it with the status the document gives
/// (`crate::cli::coverage_status`). The derived part ([`derive`]) is left for the caller to add
/// once a front end has annotated the rules, `spelling` saying how its fuzz jobs are spelled.
/// kink-flow's own front end derives no flips, so the flips family does not run
/// ([`coverage_front`]). No lock is read or written: `options.lock` is the command's
/// ([`command`]).
pub fn coverage(manifest: &FlowManifest, options: &CoverageOptions) -> (Value, bool) {
    coverage_front(manifest, options, &FrontEnd::default(), None)
}

/// The command `coverage` for a front end: [`coverage_front`] with the lock `options.lock`
/// names, annotated and derived, and the lock settled ([`settle_lock`]). A lock that does not
/// decode refuses the command before the specification is admitted, with no family and no
/// program ([`lock_refused`]).
pub fn command(
    manifest: &FlowManifest,
    options: &CoverageOptions,
    front: &FrontEnd<'_>,
) -> (Value, bool) {
    let lock = match options
        .lock
        .as_deref()
        .map(|path| Lock::read_kind(path, LockKind::Coverage))
        .transpose()
    {
        Ok(lock) => lock,
        Err(detail) => {
            let path = options.lock.as_deref().unwrap_or_else(|| Path::new(""));
            return (front.annotated(lock_refused(path, &detail)), false);
        }
    };
    // The derived part reads the rules as the front end named them, so it follows the
    // annotation; `derive` and the annotation are idempotent.
    let (document, mut ok) = coverage_front(manifest, options, front, lock.as_ref());
    let mut document = front.annotated(document);
    derive(&mut document, front.spelling);
    if let Some(lock) = &lock {
        ok &= settle_lock(&mut document, lock, manifest, options);
    }
    (document, ok)
}

/// Settle the coverage lock of a command whose document is `document` (annotated and derived,
/// since the rendering names rules as the front end does): set the document's `lock` and return
/// whether no write failed. The lock is compared and written only after a run with the
/// manifest's own settings, which judged every flip: under `--tier 1` (no flip runs) it is left
/// as it is with reason `tier-1`, under a `--depth` other than `[coverage] depth` with reason
/// `depth`, and after a search a corpus error stopped with reason `stopped`; otherwise as
/// [`Lock::settle`] settles a run's (`--locked` compares, `--verify` writes nothing).
pub fn settle_lock(
    document: &mut Value,
    lock: &Lock,
    manifest: &FlowManifest,
    options: &CoverageOptions,
) -> bool {
    let partial = if document["spec"]["outcome"] == "refused" {
        None
    } else if options.tier == Tier::One {
        Some("tier-1")
    } else if options.depth(manifest) != manifest.coverage.depth {
        Some("depth")
    } else {
        None
    };
    if let Some(reason) = partial {
        document["lock"] = lock.not_written(reason);
        return true;
    }
    let store = kink_corpus::Store::new(cache_directory(manifest, options.cache.as_deref()));
    let stopped = !document["families"]["flips"]["search"]["stopped"].is_null();
    let (value, written) = lock.settle(
        &store,
        document,
        Settle {
            locked: options.locked,
            verify: options.verify,
            only: &[],
            stopped,
        },
    );
    document["lock"] = value;
    written
}

/// The coverage document of a command whose lock at `path` does not decode: it names the refused
/// lock (`lock: {path, outcome: "refused", detail}`), and has no specification, no program and
/// no family, since the lock is read before admission. Under the Z3 profile it names the Z3 build
/// (`z3`, [`crate::with_z3_build`]), as every coverage document does.
#[must_use]
pub fn lock_refused(path: &Path, detail: &str) -> Value {
    crate::with_z3_build(json!({
        "schema": COVERAGE_SCHEMA,
        "version": COVERAGE_VERSION,
        "k_rust_revision": crate::k_rust_revision(),
        "profile": SolverProfile::BUILD.name(),
        "lock": crate::lock::refused_value(path, detail),
    }))
}

/// [`coverage`] for a front end: under tier 2, the flips it derives
/// ([`FrontEnd::derived`]) are deduced unreached or run by the kill search
/// ([`crate::flips`]), reading the rules' items as the front end annotates them, each flip's
/// recorded killer read from `lock` (tried first while it kills); the document is returned
/// annotated, with no `lock` settled ([`command`] settles it).
pub fn coverage_front(
    manifest: &FlowManifest,
    options: &CoverageOptions,
    front: &FrontEnd<'_>,
    lock: Option<&Lock>,
) -> (Value, bool) {
    // Every document names the stop, a refused specification's too, as `check` and `run` do.
    let stopped = |mut document: Value| {
        if let Some(stop) = manifest.stop_value() {
            document["stop"] = stop;
        }
        if let Some(observe) = manifest.observe_value() {
            document["observe"] = observe;
        }
        document
    };
    // Tier 2 is computed only where it runs: the front end derives the flips and tier 1 alone
    // was not asked for.
    let tier_two = matches!(front.derived, Derived::Flips(_)) && options.tier == Tier::Two;
    let depth = options.depth(manifest);
    let settings = settings(manifest, depth, tier_two);
    let refused = |record: &AdmissionRecord| {
        stopped(document(
            record,
            None,
            settings.clone(),
            Vec::new(),
            None,
            Vec::new(),
            Value::Null,
        ))
    };
    let (mut record, admitted) = admit_spec(manifest);
    let Some((spec, mut inputs)) = admitted else {
        return (refused(&record), false);
    };
    // The one scope of every family; a front end's flip that changes a sentence outside it is
    // moved to the list's `not_generated` before anything reads the list.
    let scope = scope::Scope::of(&spec, manifest);
    let scoped = match front.derived {
        Derived::Flips(list) => Some(crate::flips::scoped(list, &spec, &scope)),
        Derived::None(_) => None,
    };
    let derived = scoped.as_ref().map_or(front.derived, Derived::Flips);
    let flips = scoped.as_ref().filter(|_| tier_two);
    // Above depth 1, the rule windows family's universe, from the definition alone; a universe
    // larger than `[coverage] max_obligations` is refused with its counts before any program
    // runs.
    let window_depth = usize::try_from(depth.get()).unwrap_or(usize::MAX);
    let universe = (window_depth > 1).then(|| windows::Universe::of(&spec, &scope, window_depth));
    // The syntax paths family's universe likewise, each universe against the budget.
    let path_universe =
        (window_depth > 1).then(|| paths::Universe::of(&spec, manifest, window_depth));
    let max = manifest.coverage.max_obligations.get();
    let refusals = [
        universe
            .as_ref()
            .and_then(|universe| universe.as_ref().ok())
            .and_then(|universe| universe.refusal(max)),
        path_universe
            .as_ref()
            .and_then(|universe| universe.as_ref().ok())
            .and_then(|universe| universe.refusal(max)),
    ]
    .into_iter()
    .flatten()
    .collect::<Vec<_>>();
    if let Some(first) = refusals.first() {
        // Every universe above the budget, each with its counts.
        record.refusal = Some(AdmissionRefusal {
            stage: first.stage.clone(),
            reason: first.reason.clone(),
            detail: refusals
                .iter()
                .map(|refusal| refusal.detail.as_str())
                .collect::<Vec<_>>()
                .join("; "),
        });
        return (refused(&record), false);
    }
    let mut inputs = inputs.session(&spec);
    let cache = cache_directory(manifest, options.cache.as_deref());
    let runner = match BaselineRunner::with_depth(&spec, manifest, depth) {
        Ok(runner) => runner,
        Err(e) => {
            record.refusal = Some(runner_refusal(e));
            return (refused(&record), false);
        }
    };
    let update = update_results(
        &spec,
        manifest,
        &mut inputs,
        &runner,
        &cache,
        options.verify,
        None,
    );
    let mut ok = update.ok();
    let items = rule_items(&spec, manifest, &scope, &update.rows);
    let syntax = syntax_family(&spec, manifest, &update.rows, &items);
    let execution: ExecutionDigest = update.execution;
    let programs = data_marked(
        update.rows.iter().map(|row| row.row.clone()).collect(),
        &spec.data,
    );
    let mut document = stopped(document(
        &record,
        Some(update.spec_digest),
        settings.clone(),
        programs,
        Some((items, syntax)),
        update.mismatches.clone(),
        runner.baseline_runs(),
    ));
    document["spec"]["execution_digest"] = execution.value();
    document["result_cache"] = result_cache_value(manifest.budget.backend_options());
    document["data"] = spec.data.value();
    document["result"] = spec.result.value();
    document["spec"]["exclusion"] = runner.definition_exclusion();
    document["spec"]["short_circuit"] = runner.short_circuit();
    // The syntax paths read the productions kink-flow reached, before a front end adds its
    // joint field values to the family.
    if let Some(universe) = &path_universe {
        document["families"]["syntax_paths"] = match universe {
            Ok(universe) => paths::family(
                universe,
                window_depth,
                &update.rows,
                &manifest.programs,
                document["families"]["rules"]["items"]
                    .as_array()
                    .map_or(&[][..], Vec::as_slice),
                document["families"]["syntax"]["items"]
                    .as_array()
                    .map_or(&[][..], Vec::as_slice),
            ),
            Err(reason) => paths::unread(window_depth, reason),
        };
    }
    let mut document = front.annotated(document);
    // The rule windows read the rules as the front end annotated them: which single rules fired.
    if let Some(universe) = &universe {
        document["families"]["rule_windows"] = match universe {
            Ok(universe) => windows::family(
                universe,
                window_depth,
                &update.rows,
                &manifest.programs,
                document["families"]["rules"]["items"]
                    .as_array()
                    .map_or(&[][..], Vec::as_slice),
                &runner,
            ),
            Err(reason) => windows::unread(window_depth, reason),
        };
    }
    // The ids the argued entries name are the derived document's: derived once for both checks.
    let section = &manifest.coverage;
    let probe = (!section.argued.is_empty() || !section.invariants.is_empty()).then(|| {
        let mut probe = document.clone();
        derive(&mut probe, front.spelling);
        probe
    });
    if let Some(refusal) = probe
        .as_ref()
        .and_then(|probe| {
            stale_argued(probe, manifest, derived).or_else(|| invariant_refusal(probe, manifest))
        })
        .or_else(|| stale_mcdc(&document, manifest, front.spelling))
    {
        record.refusal = Some(refusal);
        return (refused(&record), false);
    }
    // Each invariant resolved by the front end, and each argued item's connection to its own,
    // before any mutant runs (module documentation, "Argued obligations").
    if let Some(probe) = probe.as_ref().filter(|_| !section.invariants.is_empty()) {
        let checked = invariants::resolve(manifest, &spec, front.invariants, &execution).and_then(
            |resolved| {
                for (index, invariant) in section.invariants.iter().enumerate() {
                    if let Some((_, identity)) = resolved.get(&invariant.name) {
                        document["settings"]["invariants"][index]["identity"] = identity.clone();
                    }
                }
                invariants::connections(
                    probe,
                    &spec,
                    manifest,
                    &resolved,
                    inputs.backend(),
                    &execution,
                    &cache,
                    options.verify,
                )
            },
        );
        match checked {
            Ok(checks) => document[ARGUMENT_CHECKS] = checks,
            Err(refusal) => {
                record.refusal = Some(refusal);
                return (refused(&record), false);
            }
        }
    }
    document["families"]["flips"] = match (flips, derived) {
        (Some(list), _) => {
            let (family, searched) = run_flips(
                &mut document,
                list,
                crate::search::DerivedContext {
                    spec: &spec,
                    manifest,
                    inputs: &mut inputs,
                    runner: &runner,
                    update: &update,
                    cache: &cache,
                    mode: if options.verify {
                        crate::search::RunMode::Verify
                    } else {
                        crate::search::RunMode::Search
                    },
                    recorded: lock.map(Lock::killers).unwrap_or_default(),
                    spelling: front.spelling,
                },
            );
            ok &= searched;
            family
        }
        (None, Derived::Flips(list)) => flips_not_run(Some(list.entries.len()), FLIPS_TIER_ONE),
        (None, Derived::None(reason)) => flips_not_run(None, reason),
    };
    (document, ok)
}

/// The tier-1 obligations of the admitted specification `spec` (`record` its admission) under
/// `manifest`'s syntax selection, as no program covers any: the coverage document of a corpus
/// with no program and the default `[coverage]` section, annotated by `front` and derived with
/// its spelling, so that every item has the id `coverage` gives it. A family's universe is a
/// function of the definition and the front end's selection, so this lists every obligation of
/// the families tier 1 reads (`fuzz --cover` resolves an id in it, `crate::fuzz_goal`), each open;
/// nothing runs and no cache is read.
pub(crate) fn universe(
    spec: &crate::admit::AdmittedSpec,
    record: &AdmissionRecord,
    manifest: &FlowManifest,
    front: &FrontEnd<'_>,
) -> Value {
    let mut empty = manifest.clone();
    empty.programs = Vec::new();
    empty.coverage = crate::manifest::CoverageSection::default();
    let items = rule_items(spec, &empty, &scope::Scope::of(spec, &empty), &[]);
    let syntax = syntax_family(spec, &empty, &[], &items);
    let mut document = document(
        record,
        None,
        settings(&empty, empty.coverage.depth, false),
        Vec::new(),
        Some((items, syntax)),
        Vec::new(),
        Value::Null,
    );
    document["families"]["flips"] = flips_not_run(None, FLIPS_TIER_ONE);
    let mut document = front.annotated(document);
    derive(&mut document, front.spelling);
    document
}

/// The flips family of a document whose flips do not run: how many obligations it has, where
/// the front end derived them, and why it does not run. No status is shown: a rendering must not
/// depend on what the cache holds.
fn flips_not_run(obligations: Option<usize>, reason: &str) -> Value {
    json!({
        "tier": 2,
        "run": false,
        "obligations": obligations,
        "reason": reason,
        "items": [],
    })
}

/// The flips family of `list` ([`crate::flips`]), its items before [`derive`] names their
/// sentences and counts them, and whether the search found no corpus error and no failure.
/// Each admitted flip is resolved against the specification first (resolution only loads): one
/// that does not resolve is `refused` by kink-flow; one whose occurrences no comparable program
/// reached is `unreached` with no run; every other one runs, in the list's order, through the
/// kill search ([`crate::search::search_derived`]). `--verify`'s mismatches join the document's.
fn run_flips(
    document: &mut Value,
    list: &DerivedList,
    context: crate::search::DerivedContext<'_, '_>,
) -> (Value, bool) {
    // The rules' items as the front end annotated them, by sentence.
    let rules = document["families"]["rules"]["items"]
        .as_array()
        .map_or(&[][..], Vec::as_slice)
        .iter()
        .filter_map(|item| {
            Some((
                (item["module"].as_str()?.to_owned(), item["index"].as_u64()?),
                item,
            ))
        })
        .collect::<BTreeMap<_, _>>();
    // A comparable program whose recorded coverage is not complete covers only what its run
    // explored before it stopped, so it may have reached every occurrence.
    let incomplete = context
        .manifest
        .programs
        .iter()
        .zip(&context.update.rows)
        .filter(|(_, row)| {
            row.class()
                .is_some_and(|class| ResultClass::can_kill(&json!(class)))
        })
        .filter(|(_, row)| {
            row.record
                .as_ref()
                .is_none_or(|record| record["coverage"]["complete"] != true)
        })
        .map(|(program, _)| program.id.clone())
        .collect::<Vec<_>>();
    let mut items = Vec::new();
    let mut runs = Vec::new();
    for entry in &list.entries {
        let occurrences = entry
            .occurrences
            .iter()
            .map(|occurrence| {
                let key = (
                    occurrence.sentence.module.clone(),
                    u64::from(occurrence.sentence.index),
                );
                crate::flips::occurrence_value(occurrence, rules.get(&key).copied(), &incomplete)
            })
            .collect::<Vec<_>>();
        let unreached = crate::flips::unreached(&occurrences);
        let mut item = crate::flips::item_value(entry, occurrences);
        match &entry.judged {
            Judged::Refused {
                reason,
                next,
                detail,
            } => {
                item["status"] = json!(crate::flips::REFUSED);
                item["judge"] = json!("front-end");
                item["reason"] = json!(reason);
                item["next"] = json!(next);
                item["detail"] = json!(detail);
            }
            Judged::Admitted { .. } => {
                let mutation = entry.mutation().expect("an admitted flip has its edits");
                let resolution =
                    crate::mutation::resolve(context.manifest, &context.spec.loaded, &mutation);
                match &resolution {
                    Err(invalid) => {
                        item["status"] = json!(crate::flips::REFUSED);
                        item["kink_status"] = json!(invalid.reason.status());
                        item["judge"] = json!("kink-flow");
                        item["reason"] = json!(invalid.reason.as_str());
                        item["detail"] = json!(invalid.detail);
                    }
                    Ok(resolved) => {
                        item["digest"] = json!(resolved.digest.to_string());
                        if unreached {
                            item["status"] = json!(crate::flips::UNREACHED);
                        } else {
                            runs.push((items.len(), mutation, resolution));
                        }
                    }
                }
            }
        }
        items.push(item);
    }
    // A flip decided before any run (refused or unreached) keeps no killer: its recorded one,
    // if any, was not run (`killer_change` `not-run`, as a run's row decided before any run).
    for item in &mut items {
        if let Some(killer) = item["id"].as_str().and_then(|id| context.recorded.get(id)) {
            item["recorded_killer"] = json!(killer);
            item["killer_change"] = json!("not-run");
        }
    }
    let selected = runs
        .iter()
        .map(|(_, mutation, resolution)| (mutation, resolution))
        .collect::<Vec<_>>();
    let searched = crate::search::search_derived(context, &selected);
    let mut rows = searched.rows.iter();
    for (index, mutation, _) in &runs {
        let item = &mut items[*index];
        match rows.next() {
            Some(row) => crate::flips::fill_from_row(item, row),
            None => {
                item["status"] = json!(crate::flips::UNKNOWN);
                item["reason"] = json!("not-run");
                item["detail"] = json!(format!(
                    "the search stopped at a corpus error before `{}` ran",
                    mutation.id
                ));
            }
        }
    }
    if let Some(mismatches) = document["mismatches"].as_array_mut() {
        mismatches.extend(searched.mismatches.iter().cloned());
    }
    let live_runs = items
        .iter()
        .filter_map(|item| item["live_runs"].as_u64())
        .sum::<u64>();
    let family = json!({
        "tier": 2,
        "run": true,
        "obligations": list.entries.len(),
        "reason": null,
        "none": list.none,
        "items": items,
        "not_generated": list.not_generated,
        "search": {
            "outcome_cache": searched.outcome_cache,
            "live_runs": live_runs,
            "stopped": searched.stopped,
        },
    });
    (family, searched.ok)
}

/// The document's `settings`: the tiers computed (tier 2 where the flips run), the depth
/// computed (`--depth`, else `[coverage] depth`), `[coverage]`'s other values, and whether the
/// manifest declared them (`source`). An invariant's `identity`, what its checks are about once
/// resolved (the definition, the symbol and the cell paths), is null here: [`coverage_front`]
/// sets it once the front end resolved the invariant.
fn settings(manifest: &FlowManifest, depth: NonZeroU64, flips: bool) -> Value {
    let section = &manifest.coverage;
    json!({
        "tiers": if flips { json!([1, 2]) } else { json!([1]) },
        "depth": depth.get(),
        "mcdc": section.mcdc.value(),
        "max_obligations": section.max_obligations.get(),
        "invariants": section
            .invariants
            .iter()
            .map(|invariant| {
                json!({
                    "name": invariant.name,
                    "function": invariant.function,
                    "cells": invariant.cells,
                    "identity": null,
                })
            })
            .collect::<Vec<_>>(),
        "argued": section
            .argued
            .iter()
            .map(|argued| {
                json!({
                    "item": argued.item,
                    "argument": argued.argument,
                    "invariant": argued.invariant,
                })
            })
            .collect::<Vec<_>>(),
        "source": if section.declared { "manifest" } else { "default" },
    })
}

/// The refusal of `[[coverage.argued]]` entries that name no item, or `None`. `probe` is the
/// coverage document as the front end annotated it, before the flips run, as [`derive`] derives
/// it, so that the ids are those [`derive`] gives it, and a flip's are the front end's derived list's (`derived`), whatever the
/// tier, so that a manifest valid under tier 2 is valid under tier 1. An entry no family lists
/// argues nothing: it is a misspelling, or an item the definition no longer has, and either way
/// the argument it carries is about no obligation the document counts. It is refused before any
/// mutant runs (stage `coverage`, reason `argued-stale`), naming every such entry.
fn stale_argued(
    probe: &Value,
    manifest: &FlowManifest,
    derived: Derived<'_>,
) -> Option<AdmissionRefusal> {
    let argued = &manifest.coverage.argued;
    if argued.is_empty() {
        return None;
    }
    let mut listed = BTreeSet::new();
    for family in [
        "rules",
        "requirements",
        "syntax",
        "rule_windows",
        "syntax_paths",
    ] {
        for item in probe["families"][family]["items"]
            .as_array()
            .into_iter()
            .flatten()
        {
            if let Some(id) = item["id"].as_str() {
                listed.insert(id.to_owned());
            }
        }
    }
    let no_flips = match derived {
        Derived::Flips(list) => {
            listed.extend(list.entries.iter().map(|entry| entry.id.clone()));
            None
        }
        Derived::None(reason) => Some(reason),
    };
    let stale = argued
        .iter()
        .filter(|argued| !listed.contains(&argued.item))
        .map(|argued| {
            let mut detail = format!("`{}`: no family lists it", argued.item);
            if let Some(reason) = no_flips.filter(|_| argued.item.starts_with("flip")) {
                detail.push_str(&format!(" ({reason})"));
            }
            detail
        })
        .collect::<Vec<_>>();
    if stale.is_empty() {
        return None;
    }
    Some(AdmissionRefusal {
        stage: "coverage".into(),
        reason: "argued-stale".into(),
        detail: format!(
            "[[coverage.argued]] names {} that no family lists: {}; an argued item is named by \
             its `id` in the coverage document, so correct the id or remove the entry",
            if stale.len() == 1 { "an item" } else { "items" },
            stale.join("; ")
        ),
    })
}

/// The refusal of `[[coverage.invariant]]` tables and of the entries that name them, or `None`,
/// once every entry names an item ([`stale_argued`]); `probe` is the derived document
/// [`stale_argued`] reads. It is refused before any mutant runs, at stage `coverage`:
///
/// - Where an entry names an invariant on an item the connection cannot be stated for (reason
///   `argued-invariant-unsupported`, naming each such entry with what its item is,
///   [`unsupported_kind`]).
/// - Where a table no entry names, apart from those entries, would be checked on no item's
///   behalf (reason `invariant-unused`, naming each such table): it is a misspelt name or a
///   leftover. Under the first reason these tables are named too, since the first refusal's
///   remedy, removing each such entry's `invariant`, leaves them unused: one run names both.
fn invariant_refusal(probe: &Value, manifest: &FlowManifest) -> Option<AdmissionRefusal> {
    let section = &manifest.coverage;
    if section.invariants.is_empty() {
        return None;
    }
    let unsupported = section
        .argued
        .iter()
        .filter(|argued| argued.invariant.is_some())
        .filter_map(|argued| {
            unsupported_kind(probe, &argued.item)
                .map(|kind| (argued, format!("`{}` ({kind})", argued.item)))
        })
        .collect::<Vec<_>>();
    let unused = section
        .invariants
        .iter()
        .filter(|invariant| {
            !section.argued.iter().any(|argued| {
                argued.invariant.as_ref() == Some(&invariant.name)
                    && !unsupported
                        .iter()
                        .any(|(entry, _)| std::ptr::eq(*entry, argued))
            })
        })
        .map(|invariant| format!("`{}`", invariant.name))
        .collect::<Vec<_>>();
    let unused_text = |what: &str| {
        format!(
            "[[coverage.invariant]] declares {} no{what} [[coverage.argued]] entry names: {}; \
             name it in the `invariant` of the entries whose argument rests on it, or remove the \
             table",
            if unused.len() == 1 {
                "an invariant"
            } else {
                "invariants"
            },
            unused.join(", ")
        )
    };
    let (reason, detail) = if !unsupported.is_empty() {
        let mut detail = format!(
            "[[coverage.argued]] names an invariant for {}: {}; an invariant is read at a \
             rewrite rule's left-hand side, so it argues only the `rule:` items and the \
             held, refuted and node requirements of rewrite rules: remove the entry's \
             `invariant`",
            if unsupported.len() == 1 {
                "an item it cannot argue"
            } else {
                "items it cannot argue"
            },
            unsupported
                .iter()
                .map(|(_, named)| named.as_str())
                .collect::<Vec<_>>()
                .join("; ")
        );
        if !unused.is_empty() {
            detail.push_str("; then ");
            detail.push_str(&unused_text(" other"));
        }
        ("argued-invariant-unsupported", detail)
    } else if !unused.is_empty() {
        ("invariant-unused", unused_text(""))
    } else {
        return None;
    };
    Some(AdmissionRefusal {
        stage: "coverage".into(),
        reason: reason.into(),
        detail,
    })
}

/// What the item `id` of the derived document `probe` is, where an invariant cannot argue it, or
/// `None` where it can (module documentation, "Argued obligations"). An invariant is a property
/// of states, and an item's argument rests on it through a rewrite rule's left-hand side, a whole
/// configuration whose cells the invariant reads, with the valuation that defines the item: the
/// rule's whole condition, its negation, a node's truth with the truths that reach it, or the
/// left-hand side alone. So it argues a `rule:` item of a rewrite rule and a requirement of one
/// that is held, refuted or a node's truth. It cannot argue:
///
/// - a function equation's items (`equation`), whose left-hand side binds the function's
///   arguments, not cells;
/// - a rule that is no obligation of the family (its status: `out-of-scope`, `claim-helper`,
///   `no-coverage-signal`), and a requirement of one;
/// - a unique-cause requirement (`mcdc`), whose obligation is a pair of runs showing one operand's
///   independent effect, not a valuation at one left-hand side;
/// - a syntax item, a rule window or a syntax path (its family: `syntax`, `rule_windows`,
///   `syntax_paths`), none of which is one left-hand side with a valuation;
/// - a flip (`flip`), which changes the definition, of whose runs an invariant of the baseline
///   says nothing. A listed id no tier-1 family has is a flip's ([`stale_argued`]).
fn unsupported_kind(probe: &Value, id: &str) -> Option<&'static str> {
    let items = |family: &str| {
        probe["families"][family]["items"]
            .as_array()
            .map_or(&[][..], Vec::as_slice)
    };
    let find = |family: &str, id: &str| items(family).iter().find(|item| item["id"] == id);
    let rule_kind = |rule: &Value| match rule["status"].as_str() {
        Some(OUT_OF_SCOPE) => Some(OUT_OF_SCOPE),
        Some(CLAIM_HELPER) => Some(CLAIM_HELPER),
        Some(NO_COVERAGE_SIGNAL) => Some(NO_COVERAGE_SIGNAL),
        _ if rule["rewrite"] == true => None,
        _ => Some("equation"),
    };
    if let Some(rule) = find("rules", id) {
        return rule_kind(rule);
    }
    if let Some(requirement) = find("requirements", id) {
        if requirement["level"] == MCDC {
            return Some(MCDC);
        }
        return match requirement["rule"]
            .as_str()
            .and_then(|rule| find("rules", rule))
        {
            Some(rule) => rule_kind(rule),
            None => Some("requirements"),
        };
    }
    for family in ["syntax", "rule_windows", "syntax_paths"] {
        if find(family, id).is_some() {
            return Some(family);
        }
    }
    Some("flip")
}

/// The refusal of `[coverage] mcdc` names that select no rule, or `None`. A name selects a rule
/// when it is the name the document's ids give a rule whose condition states requirements
/// ([`derive`]): a name that is a misspelling, a rule the definition no longer has, or a rule
/// with no authored condition asks for obligations no condition has, and a document that
/// silently left them out would read as if the author's selection had none open. It is refused
/// before any mutant runs (stage `coverage`, reason `mcdc-stale`), naming every such name.
fn stale_mcdc(
    document: &Value,
    manifest: &FlowManifest,
    spelling: &dyn CommandSpelling,
) -> Option<AdmissionRefusal> {
    let crate::manifest::Mcdc::Rules(names) = &manifest.coverage.mcdc else {
        return None;
    };
    if names.is_empty() {
        return None;
    }
    let mut probe = document.clone();
    derive(&mut probe, spelling);
    let selected = probe["families"]["requirements"]["mcdc"]["rules"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(Value::as_str)
        .collect::<BTreeSet<_>>();
    let stale = names
        .iter()
        .filter(|name| !selected.contains(format!("rule:{name}").as_str()))
        .map(|name| format!("`{name}`"))
        .collect::<Vec<_>>();
    if stale.is_empty() {
        return None;
    }
    Some(AdmissionRefusal {
        stage: "coverage".into(),
        reason: "mcdc-stale".into(),
        detail: format!(
            "[coverage] mcdc names {} that no rule whose condition states requirements has: {}; \
             a rule is named as its id `rule:<name>` in the coverage document spells it, so \
             correct the name or remove it",
            if stale.len() == 1 { "a rule" } else { "rules" },
            listed(&stale)
        ),
    })
}

/// The left-hand side of a rule as K text, a pattern `query` and `fuzz --pattern` take
/// (README, "PATTERNS.toml"): the text of its body as written, each rewrite replaced by the text
/// of its left side, without its `requires`, and each variable written without a sort given the
/// sort the rule's parse inferred for it. A pattern denotes the configurations its left side
/// matches and refuses a variable that occurs only on a rewrite's right side, so the right sides
/// are left out; the sorts keep what the right side and the condition told the parse about the
/// variables, so the pattern matches what the rule's left-hand side matches. `text` is the
/// rule's text in its file's K view, starting at byte `start` of that view, which the spans of
/// the rule's terms index. `None` where a term the text needs has no span inside the rule's text.
fn left_side_text(sentence: &Sentence, text: &str, start: usize) -> Option<String> {
    use k_rust::kast::TermSpan;
    use std::ops::Range;
    type Edits = Vec<(Range<usize>, String)>;
    let slice = |range: Range<usize>| -> Option<&str> {
        text.get(range.start.checked_sub(start)?..range.end.checked_sub(start)?)
    };
    // A term's span: its annotation's, or, for a cast the parse inserted (which has none), its
    // variable's.
    fn span(term: &Term) -> Option<TermSpan> {
        match term {
            Term::Annotated { term, metadata } => metadata.span.or_else(|| span(term)),
            Term::Apply { label, arguments } if label.semantic_cast_sort().is_some() => {
                match arguments.as_slice() {
                    [argument] => span(argument),
                    _ => None,
                }
            }
            _ => None,
        }
    }
    // `range` of the text with `edits` (sorted, disjoint, inside it) applied.
    let apply = |range: Range<usize>, mut edits: Edits| -> Option<String> {
        edits.sort_by_key(|(at, _)| at.start);
        let mut out = String::new();
        let mut at = range.start;
        for (edited, replacement) in edits {
            if edited.start < at || edited.end > range.end {
                return None;
            }
            out.push_str(slice(at..edited.start)?);
            out.push_str(&replacement);
            at = edited.end;
        }
        out.push_str(slice(at..range.end)?);
        Some(out)
    };
    // The edits of `term`, `around` the span of the annotation directly around it.
    fn edits<'t>(
        term: &Term,
        around: Option<TermSpan>,
        apply: &dyn Fn(Range<usize>, Edits) -> Option<String>,
        slice: &dyn Fn(Range<usize>) -> Option<&'t str>,
        found: &mut Edits,
    ) -> Option<()> {
        match term {
            Term::Annotated { term, metadata } => {
                edits(term, metadata.span.or(around), apply, slice, found)
            }
            Term::Rewrite { left, .. } => {
                // A span ends after the layout that follows it: the rewrite's is kept, after the
                // left side's text.
                let whole = around?;
                let left_span = span(left)?;
                let mut inner = Vec::new();
                edits(left, None, apply, slice, &mut inner)?;
                let rendered = apply(left_span.start..left_span.end, inner)?;
                let written = slice(whole.start..whole.end)?;
                let layout = &written[written.trim_end().len()..];
                found.push((
                    whole.start..whole.end,
                    format!("{}{layout}", rendered.trim_end()),
                ));
                Some(())
            }
            Term::Variable {
                name,
                sort: Some(sort),
            } => {
                if let Some(at) = around {
                    let written = slice(at.start..at.end)?;
                    if written.trim_end() == name {
                        let end = at.start + written.trim_end().len();
                        found.push((end..end, format!(":{sort}")));
                    }
                }
                Some(())
            }
            // The parse states a variable's inferred sort as a cast around it.
            Term::Apply { label, arguments }
                if label.semantic_cast_sort().is_some()
                    && matches!(
                        arguments.as_slice(),
                        [argument] if matches!(argument.unannotated(), Term::Variable { .. })
                    ) =>
            {
                let (Some(sort), [argument]) = (label.semantic_cast_sort(), arguments.as_slice())
                else {
                    return Some(());
                };
                // A cast the parse inserted has no span of its own; its variable has.
                let Some(at) = around.or_else(|| span(argument)) else {
                    return Some(());
                };
                let Term::Variable { name, .. } = argument.unannotated() else {
                    return Some(());
                };
                let written = slice(at.start..at.end)?;
                if written.trim_end() == name {
                    let end = at.start + written.trim_end().len();
                    found.push((end..end, format!(":{sort}")));
                }
                Some(())
            }
            Term::As { pattern, alias } => {
                edits(pattern, None, apply, slice, found)?;
                edits(alias, None, apply, slice, found)
            }
            Term::Apply { arguments, .. } | Term::Sequence(arguments) => arguments
                .iter()
                .try_for_each(|argument| edits(argument, None, apply, slice, found)),
            Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => Some(()),
        }
    }
    let Sentence::Rule { body, .. } = sentence else {
        return None;
    };
    let whole = span(body)?;
    let mut found = Vec::new();
    edits(body, None, &apply, &slice, &mut found)?;
    let pattern = apply(whole.start..whole.end, found)?;
    let pattern = pattern.trim();
    (!pattern.is_empty()).then(|| pattern.to_owned())
}

/// The cells of a definition's configuration, as far as a rule's left-hand side as a pattern
/// needs them ([`rule_pattern`]): every cell's label, and the main cell's tokens.
struct Cells {
    labels: BTreeSet<String>,
    /// The main cell's opening and closing tokens, where the configuration has exactly one.
    main: Option<(String, String)>,
}

impl Cells {
    fn of(definition: &k_rust::definition::Definition) -> Self {
        use k_rust::definition::ProductionItem;
        let mut labels = BTreeSet::new();
        let mut mains = BTreeSet::new();
        for module in &definition.modules {
            for sentence in &module.local_sentences {
                let Sentence::Production {
                    label: Some(label),
                    items,
                    attributes,
                    ..
                } = &**sentence
                else {
                    continue;
                };
                if !attributes.has(AttributeKey::Cell) {
                    continue;
                }
                labels.insert(label.name.clone());
                if attributes.has(AttributeKey::Maincell) {
                    let terminals = items
                        .iter()
                        .filter_map(|item| match item {
                            ProductionItem::Terminal(token) => Some(token.clone()),
                            _ => None,
                        })
                        .collect::<Vec<_>>();
                    if let [open, close] = terminals.as_slice() {
                        mains.insert((open.clone(), close.clone()));
                    }
                }
            }
        }
        let main = (mains.len() == 1)
            .then(|| mains.into_iter().next())
            .flatten();
        Self { labels, main }
    }

    /// The items of a body as the configuration's cells read it: the operands of the internal
    /// joins of cells, else the body.
    fn items(term: &Term) -> Vec<&Term> {
        match term.unannotated() {
            Term::Apply { label, arguments } if label.is(k_rust::kast::InternalLabel::Cells) => {
                arguments.iter().flat_map(Self::items).collect()
            }
            _ => vec![term],
        }
    }

    fn cell(&self, term: &Term) -> bool {
        matches!(term.unannotated(), Term::Apply { label, .. } if self.labels.contains(&label.name))
    }

    /// Whether the compile places the body of `sentence`, a rewrite rule, in the main cell: a
    /// rule that is not macro-like, `anywhere` or a simplification, whose body is one item that
    /// is not a cell and, for a rewrite, whose sides hold no cell. Its left-hand side then
    /// matches at the head of the main cell's contents.
    fn wrapped(&self, sentence: &Sentence) -> bool {
        let Sentence::Rule {
            body, attributes, ..
        } = sentence
        else {
            return false;
        };
        if attributes.has_any(&AttributeKey::MACRO_LIKE)
            || attributes.has(AttributeKey::Anywhere)
            || attributes.has(AttributeKey::Simplification)
        {
            return false;
        }
        match Self::items(body).as_slice() {
            [item] if !self.cell(item) => match item.unannotated() {
                Term::Rewrite { left, right } => Self::items(left)
                    .into_iter()
                    .chain(Self::items(right))
                    .all(|term| !self.cell(term)),
                _ => true,
            },
            _ => false,
        }
    }
}

/// A rewrite rule's left-hand side as a pattern ([`left_side_text`]), placed at the head of the
/// main cell where the compile places the rule there ([`Cells::wrapped`]), since a pattern's cells
/// are completed but a pattern with none is not placed in one. `None` where the text cannot be
/// read, or the rule is placed in a main cell the configuration does not single out.
fn rule_pattern(sentence: &Sentence, text: &str, start: usize, cells: &Cells) -> Option<String> {
    let left = left_side_text(sentence, text, start)?;
    if cells.wrapped(sentence) {
        let (open, close) = cells.main.as_ref()?;
        Some(format!("{open} {left} ...{close}"))
    } else {
        Some(left)
    }
}

/// Every authored rule of the specification, in sentence order, as the rules family's items
/// before [`derive`]: its position ([`sentence_value`]), its status, the comparable programs
/// whose coverage matches it (`matched_by`: k-rust `matched`, and the programs whose run entered
/// its condition, [`crate::guards::entered_sentences`], so that a function equation is matched
/// wherever an application's arguments matched its left-hand side and its group decided,
/// whatever the order in which the equations of the group were tried) and fires it (`fired_by`:
/// for a rewrite rule k-rust `committed`, some path of the run takes the rule's step; for an
/// equation k-rust `applied`, an instance gave a result), whether it compiles to a rewrite rule
/// (`rewrite`), the programs that are not comparable and match or fire it (`uncounted`), the
/// outcomes of its guard ([`crate::guards::row_guard`]), and, for an `unmatched` rewrite rule,
/// its left-hand side as a pattern (`pattern`, [`left_side_text`]; `null` otherwise).
///
/// The statuses partition the rules with the precedence [`OUT_OF_SCOPE`],
/// [`NO_COVERAGE_SIGNAL`], [`CLAIM_HELPER`], [`FIRED`], [`MATCHED`], [`UNMATCHED`]; firing
/// implies matching. The first three are the scope every family shares ([`scope::Scope`]), so
/// they are read from the definition and the front end's marks alone: a claim helper
/// (`FlowManifest::claim_helpers`), an equation of a function only claims apply, is no
/// obligation whatever the programs did, and one a typed input applied keeps the programs that
/// matched and fired it as information. No program text reaches a function nothing applies
/// either, but such a sentence stays `unmatched`, since neither a run nor a claim accounts for it.
///
/// Each such item has `kind` [`RULE`]; each `strict` or `seqstrict` production and each
/// `context` gives its heating items ([`HEATING`], [`heating_item`]) at its own place in that
/// order.
fn rule_items(
    spec: &crate::admit::AdmittedSpec,
    manifest: &FlowManifest,
    scope: &scope::Scope<'_>,
    rows: &[ProgramRow],
) -> Vec<Value> {
    type Lists<'p> = BTreeMap<(String, u64), Vec<&'p str>>;
    let mut lists: [Lists<'_>; 4] = Default::default();
    let mut comparable = Vec::new();
    let mut others = Vec::new();
    for (program, row) in manifest.programs.iter().zip(rows) {
        let Some(record) = &row.record else {
            continue;
        };
        let counted = ResultClass::can_kill(&record["class"]);
        if counted {
            comparable.push((program.id.as_str(), record));
        } else {
            others.push((program.id.as_str(), record));
        }
        let offset = if counted { 0 } else { 2 };
        for (key, slot) in [("sentences", offset), ("fired_sentences", offset + 1)] {
            for sentence in record["coverage"][key].as_array().into_iter().flatten() {
                if let (Some(module), Some(index)) =
                    (sentence["module"].as_str(), sentence["index"].as_u64())
                {
                    lists[slot]
                        .entry((module.to_owned(), index))
                        .or_default()
                        .push(&program.id);
                }
            }
        }
        // A sentence whose condition the run entered was matched, also where the run did not
        // try it (`guards::entered_sentences`).
        for (module, index) in crate::guards::entered_sentences(record) {
            let programs = lists[offset].entry((module.to_owned(), index)).or_default();
            if !programs.contains(&program.id.as_str()) {
                programs.push(&program.id);
            }
        }
    }
    let [matched, fired, others_matched, others_fired] = lists;
    // The heating and cooling rules each program matched and fired, by id.
    let mut by_id: [BTreeMap<&str, Vec<&str>>; 4] = Default::default();
    for (program, row) in manifest.programs.iter().zip(rows) {
        let Some(record) = &row.record else {
            continue;
        };
        let offset = if ResultClass::can_kill(&record["class"]) {
            0
        } else {
            2
        };
        for (key, slot) in [("matched", offset), ("fired", offset + 1)] {
            for id in record["coverage"]["strictness"][key]
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(Value::as_str)
            {
                by_id[slot].entry(id).or_default().push(&program.id);
            }
        }
    }
    let guards = crate::guards::SentenceGuards::of(comparable.iter().copied());
    let other_guards = crate::guards::SentenceGuards::of(others.iter().copied());
    let printer = EndReader::of(&spec.compiled);
    let rewrites = crate::fuzz::rewrite_ids(&spec.compiled);
    let authors = kink_native::coverage::RuleAuthors::of(&spec.compiled);
    let mut strictness = BTreeMap::<SentenceRef, Vec<kink_native::coverage::StrictnessRule>>::new();
    for rule in kink_native::coverage::strictness_rules(&spec.compiled, &authors) {
        strictness
            .entry(rule.source.at().clone())
            .or_default()
            .push(rule);
    }
    let texts = crate::mutation::rule_texts(manifest, &spec.loaded)
        .into_iter()
        .filter_map(|rule| Some(((rule.at.module, rule.at.index), (rule.text?, rule.start?))))
        .collect::<BTreeMap<_, _>>();
    let cells = Cells::of(spec.loaded.baseline.definition());
    let mut items = Vec::new();
    for (at, sentence) in spec.loaded.baseline.authored_sentences() {
        let Sentence::Rule { requires, .. } = sentence else {
            for rule in strictness.get(&at).into_iter().flatten() {
                items.push(heating_item(spec, sentence, rule, &by_id));
            }
            continue;
        };
        let mut value = sentence_value(spec, &at);
        value["kind"] = json!(RULE);
        let key = (at.module.clone(), u64::from(at.index));
        let list = |lists: &Lists<'_>| -> Vec<String> {
            lists
                .get(&key)
                .into_iter()
                .flatten()
                .map(|program| (*program).to_owned())
                .collect()
        };
        let (programs, firing) = (list(&matched), list(&fired));
        let excluded = scope.excludes(&at, sentence);
        let status = if let Some(excluded) = excluded {
            excluded.status()
        } else if !firing.is_empty() {
            FIRED
        } else if !programs.is_empty() {
            MATCHED
        } else {
            UNMATCHED
        };
        value["status"] = json!(status);
        value["matched_by"] = json!(programs);
        value["fired_by"] = json!(firing);
        let rewrite = authors.ids_of(&at).any(|id| rewrites.contains(id));
        value["rewrite"] = json!(rewrite);
        value["pattern"] = json!(
            (rewrite && status == UNMATCHED)
                .then(|| texts.get(&(at.module.clone(), at.index)))
                .flatten()
                .and_then(|(text, start)| rule_pattern(sentence, text, *start, &cells))
        );
        value["uncounted"] = json!({
            "matched_by": list(&others_matched),
            "fired_by": list(&others_fired),
        });
        if !crate::guards::unconditional(requires) && matches!(status, FIRED | MATCHED | UNMATCHED)
        {
            let at_ref = SentenceRef {
                module: at.module.clone(),
                index: at.index,
            };
            let skeletons = match &spec.guard_skeletons {
                Ok(skeletons) => match skeletons.unreadable.get(&at_ref) {
                    Some(reason) => Err(reason.as_str()),
                    None => Ok(skeletons
                        .by_sentence
                        .get(&at_ref)
                        .map(|skeletons| crate::guards::skeleton_values(skeletons))
                        .unwrap_or_default()),
                },
                Err(reason) => Err(reason.as_str()),
            };
            value["guard"] = crate::guards::row_guard(
                guards.get(&key),
                other_guards.get(&key),
                skeletons.as_deref().map_err(|reason| *reason),
                &printer,
                !manifest.coverage.mcdc.is_off(),
            );
        }
        if let Some(excluded) = excluded {
            value["reason"] = json!(excluded.reason());
        }
        items.push(value);
    }
    items
}

/// The `kind` of a rules item that is an authored rewrite rule or function equation.
pub const RULE: &str = "rule";
/// The `kind` of a rules item that is a heating rule the compile generated from a `strict` or
/// `seqstrict` production or a `context` ([`heating_item`]).
pub const HEATING: &str = "heating";

/// The rules item of one heating rule (kind [`HEATING`]) the compile generated from the
/// authored `sentence`, a `strict` or `seqstrict` production or a `context`
/// (kink-native `strictness_rules`), its programs read from `by_id`, the programs that matched
/// and fired each heating or cooling rule by id (comparable, then not).
///
/// A context, one per argument position a production's attribute names (and per context alias it
/// uses), or a `context` sentence, says: evaluate the subterm at the hole before the construct
/// around it. The compile states it as two steps: heating moves the subterm to the front of the
/// computation while it is not a result, and cooling plugs the result back. The obligation is the
/// heating rule: it fires exactly where a run put a term that is not a result at the position,
/// the one situation the attribute governs, so a corpus whose runs never heat a position cannot
/// tell the definition from one without that position's strictness, while one that heats it
/// evaluates the position as the attribute says. Cooling follows from heating wherever the
/// subterm's evaluation reaches a result; where it does not, the step after it (the authored rule
/// that reads the result) is an open item of its own, so the cooling rule is shown with its
/// programs (`heating.cool`) and is not counted. The status is the heating rule's, as an authored
/// rule's is its own: [`FIRED`] where some comparable program's run took the step, [`MATCHED`]
/// where some matched its left-hand side with a result at the position (the condition, which is
/// that the subterm is no result, and for `seqstrict` that the positions before it are results,
/// never held), [`UNMATCHED`] otherwise, and [`NO_COVERAGE_SIGNAL`] where k-rust's coverage
/// cannot name it.
///
/// The item stands at the authored sentence (its `module`, `index`, `label`, `file` and lines),
/// with `heating = {attribute, production, position, alias, heat: {axiom, label}, cool: {axiom,
/// label, matched_by, fired_by, uncounted}}`: `attribute` is `strict`, `seqstrict` or `context`,
/// `production` the production's K label and `position` the 1-based argument position (both
/// `null` for a `context`, and `position` `null` where the compile's label does not name one),
/// `alias` the context alias sentence (`null` for the default one), and `cool` `null` where no
/// cooling rule pairs with the heating rule.
fn heating_item(
    spec: &crate::admit::AdmittedSpec,
    sentence: &Sentence,
    rule: &kink_native::coverage::StrictnessRule,
    by_id: &[BTreeMap<&str, Vec<&str>>; 4],
) -> Value {
    use kink_native::coverage::StrictnessSource;
    let list = |slot: usize, id: &str| -> Vec<String> {
        by_id[slot]
            .get(id)
            .into_iter()
            .flatten()
            .map(|program| (*program).to_owned())
            .collect()
    };
    let at = rule.source.at();
    let mut value = sentence_value(spec, at);
    let (attribute, production, position, alias) = match &rule.source {
        StrictnessSource::Production {
            sequential,
            position,
            alias,
            ..
        } => (
            if *sequential { "seqstrict" } else { "strict" },
            match sentence {
                Sentence::Production {
                    label: Some(label), ..
                } => json!(label.name),
                _ => Value::Null,
            },
            json!(position),
            alias
                .as_ref()
                .map_or(Value::Null, |alias| sentence_value(spec, alias)),
        ),
        StrictnessSource::Context { .. } => ("context", Value::Null, Value::Null, Value::Null),
    };
    let (programs, firing) = (list(0, &rule.heat), list(1, &rule.heat));
    let status = if !rule.signal {
        NO_COVERAGE_SIGNAL
    } else if !firing.is_empty() {
        FIRED
    } else if !programs.is_empty() {
        MATCHED
    } else {
        UNMATCHED
    };
    value["kind"] = json!(HEATING);
    value["heating"] = json!({
        "attribute": attribute,
        "production": production,
        "position": position,
        "alias": alias,
        "heat": {"axiom": rule.heat, "label": rule.heat_label},
        "cool": rule.cool.as_ref().map(|cool| json!({
            "axiom": cool,
            "label": rule.cool_label,
            "matched_by": list(0, cool),
            "fired_by": list(1, cool),
            "uncounted": {"matched_by": list(2, cool), "fired_by": list(3, cool)},
        })),
    });
    value["status"] = json!(status);
    value["matched_by"] = json!(programs);
    value["fired_by"] = json!(firing);
    value["rewrite"] = json!(true);
    value["pattern"] = Value::Null;
    value["uncounted"] = json!({
        "matched_by": list(2, &rule.heat),
        "fired_by": list(3, &rule.heat),
    });
    if status == NO_COVERAGE_SIGNAL {
        value["reason"] = json!(
            "the heating rule is an smt-lemma or non-executable axiom, which k-rust's run \
             coverage has no recording site for"
        );
    }
    value
}

/// The status of a production some comparable program's fired instance touched.
pub const REACHED: &str = "reached";
/// The status of a production no comparable program's fired instance touched.
pub const UNREACHED: &str = "unreached";
/// The `kind` of a syntax item kink-flow builds: a production of an authored sort.
pub const PRODUCTION: &str = "production";
/// The `kind` of a syntax item a front end adds ([`derive`]): a value of a template's field.
pub const FIELD_VALUE: &str = "field-value";

/// The ways a fired instance touches a production, in the order the items list them: at a
/// non-variable position of its left-hand side, as the head of a value one of its left-hand
/// side's variables bound, and at a non-variable position of its right-hand side.
const TOUCHES: [&str; 3] = ["inspected_by", "operand_of", "built_by"];

/// One production of the syntax family's universe ([`productions`]).
struct UniverseProduction {
    at: SentenceRef,
    sort: String,
    /// The production's K label.
    label: String,
    /// The symbol a term built by it applies, by KORE name.
    symbol: String,
    /// The production as K writes it: `Sort ::= items`.
    text: String,
}

/// The sorts the specification itself declares (kink-flow's reading, without a front end's
/// [`crate::manifest::SyntaxSelection`]): every sort a syntax sentence with a source position
/// declares or gives a production, except those a library sentence (one whose source is the
/// compiler's builtin catalogue) declares or gives one. A library sort's meaning is the library's;
/// a production an author adds to it extends a sort the author did not define.
fn own_sorts(spec: &crate::admit::AdmittedSpec) -> BTreeSet<String> {
    let prefixes = &spec.compiled.compile_options().builtin_source_prefixes;
    let mut own = BTreeSet::new();
    let mut library = BTreeSet::new();
    for module in &spec.loaded.baseline.definition().modules {
        for sentence in &module.local_sentences {
            let (Sentence::SyntaxSort { sort, .. } | Sentence::Production { sort, .. }) =
                &**sentence
            else {
                continue;
            };
            let attributes = sentence.attributes();
            if attributes
                .source()
                .is_some_and(|source| prefixes.iter().any(|prefix| source.starts_with(prefix)))
            {
                library.insert(sort.name.clone());
            } else if attributes.location().is_some() {
                own.insert(sort.name.clone());
            }
        }
    }
    own.retain(|sort| !library.contains(sort));
    own
}

/// The syntax family's universe, a function of the definition and the front end's selection:
/// each production of an authored sort (the front end's [`crate::manifest::SyntaxSelection`]
/// sorts, else [`own_sorts`]) that builds a term with a constructor of the compiled definition
/// (`facts.constructors`), in sentence order. A function, a token, a bracket, a subsort, a macro
/// and a cell build no constructor application of their own sort, so none is an obligation:
/// a function's application is evaluated away, a token is a domain value, a bracket and a
/// subsort are erased, and a cell is the configuration's, not the author's syntax. Two
/// declarations of one label (a production two modules both declare) build terms of one
/// symbol, so they are one production, listed at its first declaration.
fn productions(
    spec: &crate::admit::AdmittedSpec,
    manifest: &FlowManifest,
    facts: &kink_native::coverage::SyntaxFacts,
) -> Vec<UniverseProduction> {
    use k_rust::definition::ProductionItem;
    let sorts = manifest
        .syntax
        .as_ref()
        .map_or_else(|| own_sorts(spec), |selection| selection.sorts.clone());
    let mut universe = Vec::new();
    for module in &spec.loaded.baseline.definition().modules {
        for (index, sentence) in module.local_sentences.iter().enumerate() {
            let Sentence::Production {
                label: Some(label),
                sort,
                items,
                attributes,
                ..
            } = &**sentence
            else {
                continue;
            };
            if !sorts.contains(&sort.name) || attributes.has(AttributeKey::Cell) {
                continue;
            }
            let symbol = k_rust::kast::identifier::encode_label(&label.name);
            if !facts.constructors.contains(&symbol)
                || universe
                    .iter()
                    .any(|production: &UniverseProduction| production.symbol == symbol)
            {
                continue;
            }
            let Ok(index) = u32::try_from(index) else {
                continue;
            };
            let written = items
                .iter()
                .map(|item| match item {
                    ProductionItem::Terminal(token) => format!("{token:?}"),
                    ProductionItem::NonTerminal { sort, .. } => sort.to_string(),
                    ProductionItem::RegexTerminal { regex } => format!("r{regex:?}"),
                })
                .collect::<Vec<_>>();
            universe.push(UniverseProduction {
                at: SentenceRef::new(module.name.clone(), index),
                sort: sort.name.clone(),
                label: label.name.clone(),
                symbol,
                text: format!("{sort} ::= {}", written.join(" ")),
            });
        }
    }
    universe
}

/// The bindings every baseline run of the command records (kink-native
/// `ResultRun::bindings`): the symbols of the syntax family's productions ([`productions`]),
/// recorded where one is the head of an operand of a fired instance, and the front end's template
/// binders. kink-flow's own reading selects no binder: a K sentence has no notion of a template's
/// field, so the field values of the syntax family are a front end's to add ([`derive`]). The
/// collection names no depth: the run's tables carry the command's (kink-native
/// `DefinitionTables::with_depth`), which a run at a depth above 1 sends with it, so that the
/// bindings also record the syntax paths through these symbols.
#[must_use]
pub fn binding_collection(
    spec: &crate::admit::AdmittedSpec,
    manifest: &FlowManifest,
) -> kink_native::execution::BindingCollection {
    let symbols = spec
        .syntax
        .as_ref()
        .map(|facts| {
            productions(spec, manifest, facts)
                .into_iter()
                .map(|production| production.symbol)
                .collect::<BTreeSet<_>>()
        })
        .unwrap_or_default();
    kink_native::execution::BindingCollection {
        symbols: symbols.into_iter().collect(),
        binders: manifest
            .syntax
            .iter()
            .flat_map(|selection| &selection.binders)
            .map(
                |(axiom, variable, cap)| kink_native::execution::BinderSelection {
                    axiom: axiom.clone(),
                    variable: variable.clone(),
                    cap: *cap,
                },
            )
            .collect(),
        depth: None,
    }
}

/// A sentence position of a record or a document, `{module, index}`.
fn at_of(value: &Value) -> Option<SentenceRef> {
    Some(SentenceRef::new(
        value["module"].as_str()?.to_owned(),
        u32::try_from(value["index"].as_u64()?).ok()?,
    ))
}

/// The syntax family before [`derive`] (module documentation, "Syntax"): its production items in
/// sentence order and the values the front end's template binders took.
///
/// A production is reached when a fired instance of an authored rule of the rules universe
/// (kind [`RULE`], status [`FIRED`], [`MATCHED`] or [`UNMATCHED`]) in some comparable program's
/// baseline run touched it:
/// the production is at a non-variable position of the sentence's left-hand side
/// (`inspected_by`), it is the head of a value the instance bound to a left-hand-side variable
/// that the sentence reads elsewhere (`operand_of`, k-rust's bindings as the record keeps them),
/// or it is at a non-variable position of the right-hand side (`built_by`). The first and the
/// last are static per axiom alternative (kink-native `syntax_facts`): an axiom with one
/// alternative of each side is joined with the record's `fired_sentences`, and an alternative
/// of an axiom with several with the record's `bindings.alternatives`, the ones its fired
/// instances took; the second is the record's. `inspecting` and `building` list the sentences of the rules universe that inspect
/// and build the production, a function of the definition: the sentences to make fire. The
/// programs that are not comparable and touch it are listed under `uncounted`.
fn syntax_family(
    spec: &crate::admit::AdmittedSpec,
    manifest: &FlowManifest,
    rows: &[ProgramRow],
    rules: &[Value],
) -> Value {
    let facts = match &spec.syntax {
        Ok(facts) => facts,
        Err(reason) => {
            return json!({"tier": 1, "items": [], "binders": [], "reason": reason});
        }
    };
    let universe = productions(spec, manifest, facts);
    let symbols = universe
        .iter()
        .map(|production| production.symbol.as_str())
        .collect::<BTreeSet<_>>();
    // The authored rules only: a heating item's sentence is the production (or `context`) whose
    // strictness it states, and its step touches that production by construction, which the
    // heating item already states; what the syntax family adds is whether the definition's
    // rules took a step with the production.
    let counted = rules
        .iter()
        .filter(|rule| rule["kind"] != HEATING)
        .filter(|rule| matches!(rule["status"].as_str(), Some(FIRED | MATCHED | UNMATCHED)))
        .filter_map(at_of)
        .collect::<BTreeSet<_>>();
    // Per symbol, the programs that touched it each way ([`TOUCHES`]), comparable then not.
    type Touches<'p> = BTreeMap<&'p str, [Vec<&'p str>; 3]>;
    let mut touches: [Touches<'_>; 2] = Default::default();
    // Per binder, its sentences and, comparable then not, the programs behind each value and
    // those that bound a value the cap left out or a value that is no literal.
    #[derive(Default)]
    struct Binder<'p> {
        sentences: Vec<Value>,
        values: [BTreeMap<String, Vec<&'p str>>; 2],
        truncated: [Vec<&'p str>; 2],
        nonliteral: [Vec<&'p str>; 2],
    }
    let mut binders = BTreeMap::<(String, String), Binder<'_>>::new();
    for (program, row) in manifest.programs.iter().zip(rows) {
        let Some(record) = &row.record else {
            continue;
        };
        let slot = usize::from(!ResultClass::can_kill(&record["class"]));
        let coverage = &record["coverage"];
        let mut seen: [BTreeSet<&str>; 3] = Default::default();
        for at in coverage["fired_sentences"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(at_of)
            .filter(|at| counted.contains(at))
        {
            if let Some(sentence) = facts.single.get(&at) {
                seen[0].extend(sentence.inspected.iter().map(String::as_str));
                seen[2].extend(sentence.built.iter().map(String::as_str));
            }
        }
        // An axiom with several alternatives touched what the alternatives its fired instances
        // took inspect and build, which the record's bindings name.
        for alternative in coverage["bindings"]["alternatives"]
            .as_array()
            .into_iter()
            .flatten()
        {
            let counted_sentence = alternative["sentences"]
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(at_of)
                .any(|at| counted.contains(&at));
            let index = |side: &str| {
                alternative[side]
                    .as_u64()
                    .and_then(|index| usize::try_from(index).ok())
            };
            let Some(axiom) = alternative["axiom"].as_str().filter(|_| counted_sentence) else {
                continue;
            };
            let key = kink_native::coverage::AlternativeKey {
                axiom: axiom.to_owned(),
                lhs: index("lhs"),
                rhs: index("rhs"),
            };
            if let Some(symbols) = facts.by_alternative.get(&key) {
                seen[0].extend(symbols.inspected.iter().map(String::as_str));
                seen[2].extend(symbols.built.iter().map(String::as_str));
            }
        }
        for operand in coverage["bindings"]["operands"]
            .as_array()
            .into_iter()
            .flatten()
        {
            if at_of(operand).is_some_and(|at| counted.contains(&at)) {
                seen[1].extend(
                    operand["symbols"]
                        .as_array()
                        .into_iter()
                        .flatten()
                        .filter_map(Value::as_str),
                );
            }
        }
        for (way, symbols_seen) in seen.iter().enumerate() {
            for symbol in symbols_seen {
                if let Some(symbol) = symbols.get(symbol) {
                    touches[slot].entry(symbol).or_default()[way].push(&program.id);
                }
            }
        }
        for binder in coverage["bindings"]["binders"]
            .as_array()
            .into_iter()
            .flatten()
        {
            let (Some(axiom), Some(variable)) =
                (binder["axiom"].as_str(), binder["variable"].as_str())
            else {
                continue;
            };
            let entry = binders
                .entry((axiom.to_owned(), variable.to_owned()))
                .or_default();
            if entry.sentences.is_empty() {
                entry.sentences = binder["sentences"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .filter_map(at_of)
                    .map(|at| sentence_value(spec, &at))
                    .collect();
            }
            for value in binder["values"]
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(Value::as_str)
            {
                entry.values[slot]
                    .entry(value.to_owned())
                    .or_default()
                    .push(&program.id);
            }
            if binder["truncated"] == true {
                entry.truncated[slot].push(&program.id);
            }
            if binder["nonliteral"] == true {
                entry.nonliteral[slot].push(&program.id);
            }
        }
    }
    // The sentences of the rules universe that inspect and build each symbol.
    let mut statics = BTreeMap::<&str, [Vec<Value>; 2]>::new();
    for (at, sentence) in &facts.by_sentence {
        if !counted.contains(at) {
            continue;
        }
        for (way, set) in [&sentence.inspected, &sentence.built]
            .into_iter()
            .enumerate()
        {
            for symbol in set {
                if let Some(symbol) = symbols.get(symbol.as_str()) {
                    statics.entry(symbol).or_default()[way]
                        .push(json!({"module": at.module, "index": at.index}));
                }
            }
        }
    }
    let lists = |touched: Option<&[Vec<&str>; 3]>| {
        let mut value = Map::new();
        for (way, name) in TOUCHES.iter().enumerate() {
            value.insert(
                (*name).to_owned(),
                json!(touched.map(|lists| lists[way].clone()).unwrap_or_default()),
            );
        }
        Value::Object(value)
    };
    let items = universe
        .iter()
        .map(|production| {
            let symbol = production.symbol.as_str();
            let counted_touches = touches[0].get(symbol);
            let mut reached_by = Vec::<&str>::new();
            for list in counted_touches.into_iter().flatten() {
                for program in list {
                    if !reached_by.contains(program) {
                        reached_by.push(program);
                    }
                }
            }
            // In manifest order.
            reached_by
                .sort_by_key(|program| manifest.programs.iter().position(|p| p.id == *program));
            let mut value = sentence_value(spec, &production.at);
            value["kind"] = json!(PRODUCTION);
            value["sort"] = json!(production.sort);
            value["production"] = json!(production.label);
            value["symbol"] = json!(production.symbol);
            value["text"] = json!(production.text);
            value["status"] = json!(if reached_by.is_empty() {
                UNREACHED
            } else {
                REACHED
            });
            value["reached_by"] = json!(reached_by);
            if let (Value::Object(item), Value::Object(lists)) =
                (&mut value, lists(counted_touches))
            {
                item.extend(lists);
            }
            value["uncounted"] = lists(touches[1].get(symbol));
            let [inspecting, building] = statics.remove(symbol).unwrap_or_default();
            value["inspecting"] = json!(inspecting);
            value["building"] = json!(building);
            value
        })
        .collect::<Vec<_>>();
    let binder_values = |values: &BTreeMap<String, Vec<&str>>| {
        let mut values = values.iter().collect::<Vec<_>>();
        // In the order of the integers.
        values.sort_by(|(left, _), (right, _)| integer_order(left, right));
        values
            .into_iter()
            .map(|(value, programs)| json!({"value": value, "programs": programs}))
            .collect::<Vec<_>>()
    };
    let binders = binders
        .into_iter()
        .map(|((axiom, variable), binder)| {
            json!({
                "axiom": axiom,
                "variable": variable,
                "sentences": binder.sentences,
                "values": binder_values(&binder.values[0]),
                "truncated_by": binder.truncated[0],
                "nonliteral_by": binder.nonliteral[0],
                "uncounted": {
                    "values": binder_values(&binder.values[1]),
                    "truncated_by": binder.truncated[1],
                    "nonliteral_by": binder.nonliteral[1],
                },
            })
        })
        .collect::<Vec<_>>();
    json!({"tier": 1, "items": items, "binders": binders})
}

/// The order of two integers k-rust writes in decimal (an optional `-`, no leading zero).
fn integer_order(left: &str, right: &str) -> std::cmp::Ordering {
    use std::cmp::Ordering;
    let key = |text: &'_ str| {
        let digits = text.trim_start_matches('-');
        (text.starts_with('-'), digits.len(), digits.to_owned())
    };
    let ((left_negative, left_len, left_digits), (right_negative, right_len, right_digits)) =
        (key(left), key(right));
    match (left_negative, right_negative) {
        (true, false) => Ordering::Less,
        (false, true) => Ordering::Greater,
        (false, false) => (left_len, left_digits).cmp(&(right_len, right_digits)),
        (true, true) => (right_len, right_digits).cmp(&(left_len, left_digits)),
    }
}

/// The coverage document before [`derive`]: `families` are the rules family's items and the
/// syntax family ([`syntax_family`]), `None` for a refused specification (every family is then
/// `null`).
fn document(
    record: &AdmissionRecord,
    digest: Option<Sha256Digest>,
    settings: Value,
    programs: Vec<Value>,
    families: Option<(Vec<Value>, Value)>,
    mismatches: Vec<Value>,
    baseline_runs: Value,
) -> Value {
    let refusal = record.refusal.as_ref();
    let families = families.map_or(
        Value::Null,
        |(rules, syntax)| json!({"rules": {"tier": 1, "items": rules}, "syntax": syntax}),
    );
    // Under the Z3 profile `z3`, the Z3 build the classes were decided on
    // (`crate::with_z3_build`), which the verdicts rendering names.
    crate::with_z3_build(json!({
        "schema": COVERAGE_SCHEMA,
        "version": COVERAGE_VERSION,
        "k_rust_revision": crate::k_rust_revision(),
        "profile": SolverProfile::BUILD.name(),
        "result_schema_version": RESULT_SCHEMA_VERSION,
        "spec": {
            "outcome": if refusal.is_some() { "refused" } else { "admitted" },
            "stage": refusal.map(|r| &r.stage),
            "reason": refusal.map(|r| &r.reason),
            "detail": refusal.map(|r| &r.detail),
            "digest": digest.map(|d| d.to_string()),
            "files": record
                .files
                .iter()
                .map(|f| json!({"name": f.name, "sha256": f.sha256.to_string()}))
                .collect::<Vec<_>>(),
            // The definition exclusion and the rules the short-circuit analysis flags
            // (`crate::exclusion`), set once the specification is admitted.
            "exclusion": null,
            "short_circuit": null,
        },
        "settings": settings,
        "programs": programs,
        "families": families,
        "targets": [],
        "summary": null,
        "mismatches": mismatches,
        "baseline_runs": baseline_runs,
        "data": null,
        "result": null,
        "lock": null,
    }))
}

/// A rule item's name: its KRS item where a front end named it (`krs.item`), its label, or its
/// `file:line` (`module#index` without a file). A heating item ([`HEATING`]) is named by what
/// it states: the production (its KRS item, else its K label) or the `context` (as a rule is),
/// then `heat`, then the position (the front end's field name `krs.field`, else the 1-based
/// argument position) and the context alias it uses where it uses one (its label, else its
/// `module#index`): `add:heat:1`, `crate::Exp::Add:heat:lhs`.
#[must_use]
pub fn rule_name(rule: &Value) -> String {
    if rule["kind"] == HEATING {
        let heating = &rule["heating"];
        let base = match (rule["krs"]["item"].as_str(), heating["production"].as_str()) {
            (Some(item), _) => item.to_owned(),
            (None, Some(production)) => production.to_owned(),
            (None, None) => authored_name(rule),
        };
        let mut name = format!("{base}:heat");
        if let Some(field) = rule["krs"]["field"].as_str() {
            name.push_str(&format!(":{field}"));
        } else if let Some(position) = heating["position"].as_u64() {
            name.push_str(&format!(":{position}"));
        }
        if heating["alias"].is_object() {
            name.push_str(&format!(":{}", authored_name(&heating["alias"])));
        }
        return name;
    }
    authored_name(rule)
}

/// The name of an authored sentence: its KRS item, its label, or its `file:line`
/// (`module#index` without a file).
fn authored_name(rule: &Value) -> String {
    if let Some(item) = rule["krs"]["item"].as_str() {
        return item.to_owned();
    }
    if let Some(label) = rule["label"].as_str() {
        return label.to_owned();
    }
    match (rule["file"].as_str(), rule["start_line"].as_u64()) {
        (Some(file), Some(line)) => format!("{file}:{line}"),
        _ => format!(
            "{}#{}",
            rule["module"].as_str().unwrap_or_default(),
            rule["index"]
        ),
    }
}

/// A rule item's status: the front end's (`krs.status`, which reads a sentence's match at its own
/// level) where it gave one, else kink-flow's.
#[must_use]
pub fn rule_status(rule: &Value) -> Option<&str> {
    rule["krs"]["status"]
        .as_str()
        .or_else(|| rule["status"].as_str())
}

/// The program ids of a JSON list, each a string or a `{program}` object.
fn ids(value: &Value) -> Vec<String> {
    value
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|entry| entry.as_str().or_else(|| entry["program"].as_str()))
        .map(str::to_owned)
        .collect()
}

/// `programs` without the ones `covered` already lists, in their order, each once.
fn without(programs: Vec<String>, covered: &[String]) -> Vec<String> {
    let mut kept = Vec::new();
    for program in programs {
        if !covered.contains(&program) && !kept.contains(&program) {
            kept.push(program);
        }
    }
    kept
}

/// Where a target or a requirement points: the KRS position where a front end named the rule,
/// else the K one.
fn position(rule: &Value) -> (Value, Value) {
    let krs = &rule["krs"];
    if krs["file"].is_string() {
        (krs["file"].clone(), krs["line"].clone())
    } else {
        (rule["file"].clone(), rule["start_line"].clone())
    }
}

/// A family's measure: covered / obligations, `null` without obligations.
fn measure(covered: usize, obligations: usize) -> Value {
    if obligations == 0 {
        Value::Null
    } else {
        let ratio = covered as f64 / obligations as f64;
        json!(ratio)
    }
}

/// Whether `text` reads as one operand after a prefix operator: an identifier or a path of them
/// (`halted`, `self.halted`, `crate::m::x`), optionally followed by one parenthesized argument
/// list that closes at its end (`ready(x, y)`). Anything else (`x<0`, `a + b`, `x[0]`) is read
/// as one operand only in parentheses, whatever its spacing.
fn one_operand(text: &str) -> bool {
    let path = text
        .find(|c: char| !(c.is_alphanumeric() || matches!(c, '_' | '.' | ':')))
        .unwrap_or(text.len());
    if !text
        .chars()
        .next()
        .is_some_and(|c| c.is_alphanumeric() || c == '_')
    {
        return false;
    }
    let arguments = &text[path..];
    if arguments.is_empty() {
        return true;
    }
    if !arguments.starts_with('(') {
        return false;
    }
    let mut depth = 0_usize;
    for (at, c) in arguments.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return at + 1 == arguments.len();
                }
            }
            _ => {}
        }
    }
    false
}

/// The display tree of a guard (`guard.operands`), by path.
struct Tree<'g> {
    operands: BTreeMap<&'g str, &'g Value>,
}

impl<'g> Tree<'g> {
    fn of(guard: &'g Value) -> Self {
        Self {
            operands: guard["operands"]
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(|operand| Some((operand["path"].as_str()?, operand)))
                .collect(),
        }
    }

    fn parent(path: &str) -> Option<&str> {
        path.rsplit_once('.').map(|(parent, _)| parent)
    }

    /// Whether the node at `path` is a front end's insertion or a template's conjunct, not the
    /// author's (`krs.origin` other than `authored`).
    fn generated(&self, path: &str) -> bool {
        self.operands.get(path).is_some_and(|operand| {
            operand["krs"]["origin"]
                .as_str()
                .is_some_and(|origin| origin != "authored")
        })
    }

    /// The text of the node at `path` as an author reads it: an atom's own text (`krs.text`,
    /// else its K text), a connective's operands joined by its token, a negation its operator
    /// before its operand, leaving out what a front end inserted; `None` for a node with nothing
    /// of the author's. A front end's negation is written `!`, whatever token produced it (an
    /// `else` negates the condition before it), and a K negation its connective and a space
    /// (`notBool X`); the operand is parenthesized unless it is one operand as written: a
    /// negation, or a text that is an identifier, a path or a call ([`one_operand`]).
    fn text(&self, path: &str) -> Option<String> {
        let operand = self.operands.get(path)?;
        if self.generated(path) && operand["kind"] == "atom" {
            return None;
        }
        let own = operand["krs"]["text"]
            .as_str()
            .or_else(|| operand["text"].as_str());
        let children = operand["operands"].as_array();
        let Some(children) = children.filter(|_| operand["kind"] != "atom") else {
            return own.map(str::to_owned);
        };
        if operand["kind"] == "negation"
            && let [child] = children.as_slice()
        {
            let child = child.as_str()?;
            let inner = self.text(child)?;
            let negation = self
                .operands
                .get(child)
                .is_some_and(|c| c["kind"] == "negation");
            let inner = if negation || one_operand(&inner) {
                inner
            } else {
                format!("({inner})")
            };
            return Some(if operand["krs"]["text"].is_string() {
                format!("!{inner}")
            } else {
                let connective = operand["connective"].as_str().unwrap_or("notBool");
                format!("{connective} {inner}")
            });
        }
        let token = operand["krs"]["text"]
            .as_str()
            .or_else(|| operand["connective"].as_str())
            .unwrap_or_default();
        let parts = children
            .iter()
            .filter_map(Value::as_str)
            .filter_map(|child| {
                let text = self.text(child)?;
                // A negation's text is its own operator before a delimited operand.
                let nested = self
                    .operands
                    .get(child)
                    .is_some_and(|c| c["kind"] != "atom" && c["kind"] != "negation");
                Some(if nested { format!("({text})") } else { text })
            })
            .collect::<Vec<_>>();
        match parts.as_slice() {
            [] => None,
            [one] => Some(one.clone()),
            _ => Some(parts.join(&format!(" {token} "))),
        }
    }

    /// The node at `path` with `truth` restated through negations: a negation with `truth` is
    /// its operand with the other truth, recursively, so that the node is an author's operand
    /// (a negated negation is its operand with the same truth).
    fn through_negations<'p>(&'p self, mut path: &'p str, mut truth: bool) -> (&'p str, bool) {
        while let Some(operand) = self.operands.get(path)
            && operand["kind"] == "negation"
            && let Some([child]) = operand["operands"].as_array().map(Vec::as_slice)
            && let Some(child) = child.as_str()
        {
            path = child;
            truth = !truth;
        }
        (path, truth)
    }

    /// The truths of the author's nodes that reach the node at `path`, from the root down: a
    /// conjunction's earlier operands `true`, a disjunction's `false`, an implication's left
    /// operand `true` for its right one (the reached rule of guard outcomes). Each step is
    /// restated through negations ([`Self::through_negations`]): a negation `true` is its operand
    /// `false`, which is how the author of an `else` reads the condition before it.
    fn reaching(&self, path: &str) -> Vec<(String, bool)> {
        let mut chain = Vec::new();
        let mut child = path;
        while let Some(parent) = Self::parent(child) {
            if let Some(operand) = self.operands.get(parent) {
                let siblings = operand["operands"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .filter_map(Value::as_str)
                    .collect::<Vec<_>>();
                let earlier = siblings
                    .iter()
                    .take_while(|sibling| **sibling != child)
                    .copied()
                    .collect::<Vec<_>>();
                let truth = match operand["kind"].as_str() {
                    Some("conjunction") => Some(true),
                    Some("disjunction") => Some(false),
                    Some("implication") => Some(true),
                    _ => None,
                };
                if let Some(truth) = truth {
                    let mut level = earlier
                        .iter()
                        .filter_map(|sibling| {
                            let (sibling, truth) = self.through_negations(sibling, truth);
                            Some((self.text(sibling)?, truth))
                        })
                        .collect::<Vec<_>>();
                    level.extend(chain);
                    chain = level;
                }
            }
            child = parent;
        }
        chain
    }

    /// The author's node and truth whose reached truth is the node at `path` reached with
    /// `truth`, where there is one: the node itself for an atom or an exclusive connective (whose
    /// outcomes are their own); a negation's operand with the other truth; for `true`, a
    /// conjunction's last operand, which is reached only where every operand before it is
    /// `true`; for `false`, a disjunction's last operand, dually, and an implication's right
    /// operand, reached only where its left one is `true`. `None` where the truth is a union of
    /// several nodes' (a conjunction's `false`), or rests on a node a front end inserted.
    fn restated(&self, path: &str, truth: bool) -> Option<(String, bool)> {
        let operand = self.operands.get(path)?;
        let children = operand["operands"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
            .collect::<Vec<_>>();
        match (operand["kind"].as_str()?, truth) {
            ("atom" | "exclusive", _) => (!self.generated(path)).then(|| (path.to_owned(), truth)),
            ("negation", _) => match children.as_slice() {
                [one] => self.restated(one, !truth),
                _ => None,
            },
            ("conjunction", true) | ("disjunction" | "implication", false) => {
                self.restated(children.last()?, truth)
            }
            _ => None,
        }
    }

    /// Whether the node at `path` is a conjunct of the condition: every node above it is a
    /// conjunction.
    fn conjunct(&self, path: &str) -> bool {
        let mut child = path;
        while let Some(parent) = Self::parent(child) {
            if self.operands.get(parent).map(|p| &p["kind"]) != Some(&json!("conjunction")) {
                return false;
            }
            child = parent;
        }
        true
    }
}

/// One requirement node: its display path, its text, and its outcomes' lists.
struct Node {
    path: String,
    text: String,
    true_by: Vec<String>,
    false_by: Vec<String>,
    undecided_by: Vec<String>,
}

/// The requirement nodes of `guard`, a rule item's guard: a front end's authored operands where
/// it grouped the guard (`guard.krs`), else the operands with outcomes of their own.
fn requirement_nodes(guard: &Value, tree: &Tree<'_>) -> Vec<Node> {
    let grouped = &guard["krs"];
    if grouped.is_object() {
        grouped["authored"]
            .as_array()
            .into_iter()
            .flatten()
            .map(|node| {
                let path = node["path"].as_str().unwrap_or_default().to_owned();
                Node {
                    text: node["text"]
                        .as_str()
                        .map(str::to_owned)
                        .or_else(|| tree.text(&path))
                        .unwrap_or_else(|| path.clone()),
                    path,
                    true_by: ids(&node["true_by"]),
                    false_by: ids(&node["false_by"]),
                    undecided_by: ids(&node["undecided_by"]),
                }
            })
            .collect()
    } else {
        guard["operands"]
            .as_array()
            .into_iter()
            .flatten()
            .filter(|operand| operand.get("never").is_some())
            .map(|operand| {
                let path = operand["path"].as_str().unwrap_or_default().to_owned();
                Node {
                    text: operand["text"].as_str().unwrap_or(&path).to_owned(),
                    path,
                    true_by: ids(&operand["true_by"]),
                    false_by: ids(&operand["false_by"]),
                    undecided_by: ids(&operand["undecided_by"]),
                }
            })
            .collect()
    }
}

/// The label of each node in an id: its text, with `@<path>` added where two nodes of one
/// condition share a text.
fn node_labels(nodes: &[Node]) -> Vec<String> {
    let mut seen = BTreeMap::<&str, usize>::new();
    for node in nodes {
        *seen.entry(node.text.as_str()).or_default() += 1;
    }
    nodes
        .iter()
        .map(|node| {
            if seen[node.text.as_str()] > 1 {
                format!("{}@{}", node.text, node.path)
            } else {
                node.text.clone()
            }
        })
        .collect()
}

/// The requirements of one guarded rule item, `name` its name (module documentation).
fn requirements(name: &str, rule_id: &str, rule: &Value, entered: &[String]) -> Vec<Value> {
    let guard = &rule["guard"];
    if !crate::guards::authored_condition(guard) {
        return Vec::new();
    }
    let tree = Tree::of(guard);
    let grouped = &guard["krs"];
    let nodes = requirement_nodes(guard, &tree);
    let (held, refuted) = if grouped.is_object() {
        (ids(&grouped["held_by"]), ids(&grouped["refuted_by"]))
    } else {
        (ids(&guard["held_by"]), ids(&guard["refuted_by"]))
    };
    // The outcomes the programs that are not comparable saw, which no requirement counts.
    let uncounted = &guard["uncounted"];
    let uncounted_node = |path: &str, truth: bool| {
        ids(&uncounted["nodes"][path][if truth { "true_by" } else { "false_by" }])
    };
    let (uncounted_held, uncounted_refuted) = if grouped.is_object() {
        // The author's condition: its last authored conjunct reached true, or one reached false.
        let conjuncts = nodes
            .iter()
            .filter(|node| tree.conjunct(&node.path))
            .collect::<Vec<_>>();
        (
            conjuncts
                .last()
                .map(|node| uncounted_node(&node.path, true))
                .unwrap_or_default(),
            conjuncts
                .iter()
                .flat_map(|node| uncounted_node(&node.path, false))
                .collect(),
        )
    } else {
        (ids(&uncounted["held_by"]), ids(&uncounted["refuted_by"]))
    };
    let undecided = ids(&guard["undecided_by"]);
    let (file, line) = position(rule);
    let item = |detail: String,
                node: Option<&str>,
                truth: &str,
                text: &str,
                covered_by: Vec<String>,
                undecided_by: Vec<String>,
                touched: Vec<String>| {
        let covered = !covered_by.is_empty();
        json!({
            "id": format!("requirement:{name}:{detail}"),
            "rule": rule_id,
            "node": node,
            "truth": truth,
            "text": text,
            "file": file,
            "line": line,
            "status": if covered { "covered" } else { "open" },
            "covered": covered,
            "covered_by": covered_by,
            "undecided_by": undecided_by,
            "touched_only_by": if covered { Vec::new() } else { without(touched, &[]) },
            "entered_by": entered,
        })
    };
    // The condition's own outcomes are the root's truths. Where one of them is an operand
    // node's reached truth (`Tree::restated`), the two are one obligation: it is listed once, as
    // the root's, with the node and the programs of both.
    let conjuncts = guard["operands"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|operand| operand["path"].as_str())
        .filter(|path| {
            tree.conjunct(path)
                && tree.operands.get(path).map(|o| &o["kind"]) != Some(&json!("conjunction"))
                && !tree.generated(path)
        })
        .collect::<Vec<_>>();
    // Without a front end's grouping, the condition is every conjunct the compile wrote; only
    // where the compile added none (`compiled` empty) are the shown conjuncts all of it.
    let whole = grouped.is_object()
        || guard["compiled"]
            .as_array()
            .is_none_or(|compiled| compiled.is_empty());
    let restated = |truth: bool| -> Option<(String, bool)> {
        if !whole {
            return None;
        }
        let restated = match (truth, conjuncts.as_slice()) {
            (true, [.., last]) => tree.restated(last, true),
            (false, [one]) => tree.restated(one, false),
            _ => None,
        }?;
        nodes
            .iter()
            .any(|node| node.path == restated.0)
            .then_some(restated)
    };
    let (held_node, refuted_node) = (restated(true), restated(false));
    let reaching = |path: &str| {
        Value::Array(
            tree.reaching(path)
                .into_iter()
                .map(|(text, truth)| json!({"text": text, "truth": truth}))
                .collect(),
        )
    };
    let mut items = Vec::new();
    for (outcome, programs, uncounted_programs, restated) in [
        ("held", held, uncounted_held, &held_node),
        ("refuted", refuted, uncounted_refuted, &refuted_node),
    ] {
        let value = match restated {
            None => item(
                outcome.into(),
                None,
                outcome,
                "the condition",
                programs,
                undecided.clone(),
                uncounted_programs,
            ),
            Some((path, truth)) => {
                let node = nodes
                    .iter()
                    .find(|node| &node.path == path)
                    .expect("a restated node is a requirement node");
                let by = if *truth {
                    &node.true_by
                } else {
                    &node.false_by
                };
                let mut covered_by = programs;
                covered_by.extend(by.iter().cloned());
                let mut touched = uncounted_programs;
                touched.extend(uncounted_node(path, *truth));
                let mut undecided_by = undecided.clone();
                undecided_by.extend(node.undecided_by.iter().cloned());
                let mut value = item(
                    outcome.into(),
                    Some(path.as_str()),
                    outcome,
                    &node.text,
                    without(covered_by, &[]),
                    without(undecided_by, &[]),
                    touched,
                );
                value["node_truth"] = json!(if *truth { "true" } else { "false" });
                value["reaching"] = reaching(path);
                value
            }
        };
        items.push(value);
    }
    for (node, label) in nodes.iter().zip(node_labels(&nodes)) {
        for (truth, by) in [(true, &node.true_by), (false, &node.false_by)] {
            let restates = |restated: &Option<(String, bool)>| {
                restated
                    .as_ref()
                    .is_some_and(|(path, t)| *path == node.path && *t == truth)
            };
            if restates(&held_node) || restates(&refuted_node) {
                continue;
            }
            let mut value = item(
                format!("{label}:{truth}"),
                Some(&node.path),
                if truth { "true" } else { "false" },
                &node.text,
                by.clone(),
                node.undecided_by.clone(),
                uncounted_node(&node.path, truth),
            );
            value["reaching"] = reaching(&node.path);
            items.push(value);
        }
    }
    items
}

/// The `level` of a requirement of the unique-cause level (module documentation, "Unique-cause
/// MC/DC").
pub const MCDC: &str = "mcdc";

/// The unique-cause obligations of one guarded rule item `[coverage] mcdc` selects, `name` its
/// name (module documentation, "Unique-cause MC/DC"): one per authored atom of its condition,
/// read from the guard's valuation combinations ([`crate::guards`], `guard.combinations`).
fn mcdc_requirements(name: &str, rule_id: &str, rule: &Value, entered: &[String]) -> Vec<Value> {
    let guard = &rule["guard"];
    if !crate::guards::authored_condition(guard) {
        return Vec::new();
    }
    let tree = Tree::of(guard);
    let nodes = requirement_nodes(guard, &tree);
    let labels = node_labels(&nodes);
    let combinations = &guard["combinations"];
    let atoms = combinations["atoms"]
        .as_array()
        .map_or(&[][..], Vec::as_slice);
    let rows = combinations["rows"]
        .as_array()
        .map_or(&[][..], Vec::as_slice);
    let truncated = ids(&combinations["truncated_by"]);
    // The operands: the author's atoms, each with its position in the combinations.
    let operands = nodes
        .iter()
        .zip(&labels)
        .filter(|(node, _)| {
            tree.operands.get(node.path.as_str()).map(|o| &o["kind"]) == Some(&json!("atom"))
        })
        .filter_map(|(node, label)| {
            let ordinal = atoms.iter().position(|atom| atom == node.path.as_str())?;
            Some((node, label, ordinal))
        })
        .collect::<Vec<_>>();
    let truth = |row: &Value, ordinal: usize| -> String {
        row["truths"][ordinal]
            .as_str()
            .unwrap_or_default()
            .to_owned()
    };
    // A valuation of the operands, as the document and a target state it.
    let valuation = |truths: &dyn Fn(usize) -> String| {
        operands
            .iter()
            .map(|(node, _, ordinal)| {
                json!({"node": node.path, "text": node.text, "truth": truths(*ordinal)})
            })
            .collect::<Vec<_>>()
    };
    let decided = |row: &Value| crate::guards::decided(row["outcome"].as_str().unwrap_or_default());
    let side = |row: &Value| {
        json!({
            "valuation": valuation(&|ordinal| truth(row, ordinal)),
            "outcome": row["outcome"],
            "programs": row["programs"],
        })
    };
    let (file, line) = position(rule);
    let mut items = Vec::new();
    for (node, label, ordinal) in &operands {
        let two_valued = |row: &Value| match truth(row, *ordinal).as_str() {
            "true" => Some(true),
            "false" => Some(false),
            _ => None,
        };
        // A unique-cause pair: a held and a refuted combination in which the operand has the two
        // truths and every other atom one decided truth.
        let pair = rows
            .iter()
            .filter(|held| decided(held) == Some(true))
            .flat_map(|held| rows.iter().map(move |refuted| (held, refuted)))
            .find(|(held, refuted)| {
                decided(refuted) == Some(false)
                    && two_valued(held)
                        .zip(two_valued(refuted))
                        .is_some_and(|(a, b)| a != b)
                    && (0..atoms.len())
                        .filter(|other| other != ordinal)
                        .all(|other| {
                            let value = truth(held, other);
                            value != "undecided" && value == truth(refuted, other)
                        })
            });
        // Where there is none, the valuations that would make one with a recorded combination:
        // the operand's truth negated, where the condition then takes the other outcome.
        let mut needed = Vec::<Value>::new();
        if pair.is_none() {
            for row in rows {
                let (Some(outcome), Some(own)) = (decided(row), two_valued(row)) else {
                    continue;
                };
                let flipped = match row["flipped"][node.path.as_str()].as_str() {
                    Some("held") => true,
                    Some("refuted") => false,
                    _ => continue,
                };
                if flipped == outcome {
                    continue;
                }
                let truths = |other: usize| {
                    if other == *ordinal {
                        (!own).to_string()
                    } else {
                        truth(row, other)
                    }
                };
                let wanted = valuation(&truths);
                if needed
                    .iter()
                    .any(|known| known["valuation"] == json!(wanted))
                {
                    continue;
                }
                needed.push(json!({
                    "valuation": wanted,
                    "outcome": if flipped { "held" } else { "refuted" },
                    "against": side(row),
                }));
            }
        }
        let covered_by = pair.map_or_else(Vec::new, |(held, refuted)| {
            without(
                ids(&held["programs"])
                    .into_iter()
                    .chain(ids(&refuted["programs"]))
                    .collect(),
                &[],
            )
        });
        let covered = pair.is_some();
        let status = if covered {
            "covered"
        } else if truncated.is_empty() {
            "open"
        } else {
            UNDECIDED
        };
        items.push(json!({
            "id": format!("requirement:{name}:{label}:{MCDC}"),
            "rule": rule_id,
            "level": MCDC,
            "node": node.path,
            "text": node.text,
            "file": file,
            "line": line,
            "status": status,
            "covered": covered,
            "covered_by": covered_by,
            "pair": pair.map_or(Value::Null, |(held, refuted)| json!([side(held), side(refuted)])),
            "needed": needed,
            "truncated_by": truncated,
            "entered_by": entered,
        }));
    }
    items
}

/// The target text of a unique-cause requirement `requirement` of the rule named `name`: the
/// valuation the first of its `needed` asks for, against the recorded combination it pairs with;
/// else the pair in general, and why no recorded combination gives one; and, for an undecided
/// one, why the record cannot say.
fn mcdc_target(name: &str, requirement: &Value) -> String {
    let operand = requirement["text"].as_str().unwrap_or_default();
    let stated = |valuation: &Value| {
        listed(
            &valuation
                .as_array()
                .into_iter()
                .flatten()
                .map(|step| {
                    format!(
                        "{} {}",
                        step["text"].as_str().unwrap_or_default(),
                        step["truth"].as_str().unwrap_or_default()
                    )
                })
                .collect::<Vec<_>>(),
        )
    };
    let holds = |outcome: &Value| {
        if crate::guards::decided(outcome.as_str().unwrap_or_default()) == Some(true) {
            "holds"
        } else {
            "is false"
        }
    };
    let mut text = match requirement["needed"]
        .as_array()
        .and_then(|needed| needed.first())
    {
        Some(needed) => {
            let against = &needed["against"];
            format!(
                "a case that enters {name} with {}, where its condition {}: against {}'s {}, \
                 where it {}, {operand} alone decides it",
                stated(&needed["valuation"]),
                holds(&needed["outcome"]),
                listed(&ids(&against["programs"])),
                stated(&against["valuation"]),
                holds(&against["outcome"]),
            )
        }
        None if requirement["entered_by"]
            .as_array()
            .is_none_or(Vec::is_empty) =>
        {
            format!(
                "two cases that enter {name}, differ only in {operand}, and differ in whether \
                 its condition holds"
            )
        }
        None => format!(
            "two cases that enter {name}, differ only in {operand}, and differ in whether its \
             condition holds; no recorded valuation with every other atom decided lets \
             {operand} alone change the condition: where {operand} is a function of the other \
             operands, argue the obligation"
        ),
    };
    if requirement["status"] == UNDECIDED {
        let truncated = ids(&requirement["truncated_by"]);
        text.push_str(&format!(
            "; undecided: the {} of {} {} only part of {} combinations of this condition, so \
             such a pair may be among those left out",
            if truncated.len() == 1 {
                "record"
            } else {
                "records"
            },
            listed(&truncated),
            if truncated.len() == 1 {
                "keeps"
            } else {
                "keep"
            },
            if truncated.len() == 1 { "its" } else { "their" },
        ));
    }
    text
}

/// A list of names as a sentence reads it: `a`, `a and b`, `a, b and c`.
/// The text of an open heating item's target ([`heating_item`]): a case whose run evaluates the
/// position from a term that is not a result. `matched` says some comparable program's run
/// reached the construct but never met the heating rule's condition there.
fn heating_target(item: &Value, matched: bool) -> String {
    let heating = &item["heating"];
    let construct = match (item["krs"]["item"].as_str(), heating["production"].as_str()) {
        (Some(name), _) | (None, Some(name)) => name.to_owned(),
        (None, None) => authored_name(item),
    };
    let reached = if heating["attribute"] == "context" {
        format!(
            "reaches a state the context {construct} matches with a term that is not a result in \
             its hole"
        )
    } else {
        let position = if let Some(field) = item["krs"]["field"].as_str() {
            format!("field {field}")
        } else if let Some(position) = heating["position"].as_u64() {
            format!("argument {position}")
        } else {
            "heated argument".to_owned()
        };
        let earlier = if heating["attribute"] == "seqstrict" {
            ", and results as the arguments before it"
        } else {
            ""
        };
        format!(
            "brings {construct} to the front of the computation with a term that is not a result \
             as its {position}{earlier}"
        )
    };
    let entered = if matched {
        " (the comparable runs that reached it did not)"
    } else {
        ""
    };
    format!("a case whose run {reached}, so that heating evaluates it{entered}")
}

fn listed(names: &[String]) -> String {
    match names {
        [] => String::new(),
        [one] => one.clone(),
        [init @ .., last] => format!("{} and {last}", init.join(", ")),
    }
}

/// What a target adds for programs that touch its item and are not comparable.
fn touched_note(touched: &[String]) -> String {
    if touched.is_empty() {
        String::new()
    } else {
        format!(
            "; {} {} it but {} not comparable: make one comparable (its row's cause says why)",
            listed(touched),
            if touched.len() == 1 {
                "touches"
            } else {
                "touch"
            },
            if touched.len() == 1 { "is" } else { "are" }
        )
    }
}

/// Fill the derived part of a coverage document from its rules' items (module documentation):
/// each item's `id`, `obligation`, `covered` and `touched_only_by`, the counts and measure of
/// each family, the requirements, the targets and the summary. `spelling` spells the fuzz jobs of
/// the targets. A document whose specification was refused, or that is no coverage document, is
/// left as it is. Applying it twice gives what applying it once does.
pub fn derive(document: &mut Value, spelling: &dyn CommandSpelling) {
    if document["schema"] != COVERAGE_SCHEMA {
        return;
    }
    let programs = document["programs"].as_array().cloned().unwrap_or_default();
    let summary_programs = json!({
        "programs": programs.len(),
        "comparable": programs.iter().filter(|p| ResultClass::can_kill(&p["class"])).count(),
        "computed": programs.iter().filter(|p| p["cached"] == false).count(),
        "mismatches": document["mismatches"].as_array().map_or(0, Vec::len),
    });
    unargue(document);
    // A refuted argument stands in for nothing: its item is open, with its target, wherever
    // the derived part reads the entries.
    let failed = failed_arguments(document);
    let mut argued_entries = argued_entries(document);
    argued_entries.retain(|id, _| !failed.contains_key(id));
    let mcdc = document["settings"]["mcdc"].clone();
    let mcdc_on = mcdc == true || mcdc.as_array().is_some_and(|names| !names.is_empty());
    let selects = |name: &str| {
        mcdc == true
            || mcdc
                .as_array()
                .is_some_and(|names| names.iter().any(|selected| selected == name))
    };
    let mut mcdc_rules = Vec::new();
    let Some(items) = document
        .get_mut("families")
        .and_then(|families| families.get_mut("rules"))
        .and_then(|rules| rules.get_mut("items"))
        .and_then(Value::as_array_mut)
    else {
        document["summary"] = summary_programs;
        return;
    };
    // Names: a rule's name, made unique by its label where two rules share it.
    let names = items.iter().map(rule_name).collect::<Vec<_>>();
    let mut counts = BTreeMap::<&str, usize>::new();
    for name in &names {
        *counts.entry(name.as_str()).or_default() += 1;
    }
    let fuzz = spelling.command(Verb::Fuzz);
    // The fuzz job that looks for a program covering an obligation by its id (`fuzz --cover`).
    let cover = |id: &str| json!(format!("{fuzz} --template ID --cover {}", shell_word(id)));
    let mut status_counts = BTreeMap::<&'static str, usize>::new();
    let mut requirement_items = Vec::new();
    let mut targets = Vec::new();
    let mut requirement_targets = Vec::new();
    // Each rule's id by its sentence, which the syntax family's targets name.
    let mut rule_ids = BTreeMap::<SentenceRef, String>::new();
    let mut heating_obligations = 0;
    let mut heating_fired = 0;
    for (item, name) in items.iter_mut().zip(&names) {
        let heating = item["kind"] == HEATING;
        let name = if counts[name.as_str()] > 1 {
            let label = if heating {
                &item["heating"]["heat"]["label"]
            } else {
                &item["label"]
            };
            format!("{name}:{}", label.as_str().unwrap_or_default())
        } else {
            name.clone()
        };
        let id = format!("rule:{name}");
        let status = rule_status(item).unwrap_or(UNMATCHED).to_owned();
        let obligation = matches!(status.as_str(), FIRED | MATCHED | UNMATCHED);
        let covered = status == FIRED;
        for known in [
            FIRED,
            MATCHED,
            UNMATCHED,
            OUT_OF_SCOPE,
            CLAIM_HELPER,
            NO_COVERAGE_SIGNAL,
        ] {
            if status == known {
                *status_counts.entry(known).or_default() += 1;
            }
        }
        let templated = item["guard"]["krs"]["templates"].is_object();
        let mut touched = if obligation && !covered {
            ids(&item["uncounted"]["fired_by"])
        } else {
            Vec::new()
        };
        if status == UNMATCHED && !templated {
            touched.extend(ids(&item["uncounted"]["matched_by"]));
        }
        let touched = without(touched, &[]);
        if heating {
            heating_obligations += usize::from(obligation);
            heating_fired += usize::from(covered);
        } else if let Some(at) = at_of(item) {
            rule_ids.insert(at, id.clone());
        }
        item["id"] = json!(id);
        item["obligation"] = json!(obligation);
        item["covered"] = if obligation {
            json!(covered)
        } else {
            Value::Null
        };
        item["touched_only_by"] = json!(touched);
        let entered = ids(item["krs"]
            .get("matched_by")
            .filter(|_| templated)
            .unwrap_or(&item["matched_by"]));
        let (file, line) = position(item);
        let rewrite = item["rewrite"] == true;
        let rule_spelling = item["label"].as_str().map(str::to_owned).or_else(|| {
            Some(format!(
                "{}:{}",
                item["file"].as_str()?,
                item["start_line"].as_u64()?
            ))
        });
        let held_id = format!("requirement:{name}:held");
        let mut requirements = if obligation && item.get("guard").is_some() {
            requirements(&name, &id, item, &entered)
        } else {
            Vec::new()
        };
        // The unique-cause level, for a rule `[coverage] mcdc` selects whose condition states
        // requirements; the combinations stay only in the rows it reads them from.
        if !requirements.is_empty() && selects(&name) {
            requirements.extend(mcdc_requirements(&name, &id, item, &entered));
            mcdc_rules.push(id.clone());
        } else if let Some(guard) = item.get_mut("guard").and_then(Value::as_object_mut) {
            guard.remove("combinations");
        }
        if obligation && !covered && heating {
            targets.push(json!({
                "family": "rules",
                "item": id,
                "text": format!("{}{}", heating_target(item, status == MATCHED), touched_note(&touched)),
                "file": file,
                "line": line,
                "programs": if status == MATCHED { entered.clone() } else { Vec::new() },
                "pattern": null,
                "fuzz": cover(&id),
            }));
        } else if obligation && !covered {
            let (text, job) = if status == MATCHED {
                let requirement = !argued_entries.contains_key(&held_id)
                    && requirements
                        .iter()
                        .any(|r| r["id"] == held_id.as_str() && r["covered"] == false);
                (
                    format!(
                        "a case where {name} is entered and its condition holds, so that its \
                         right-hand side is built on a path{}",
                        if requirement {
                            format!(" (requirement {held_id} is open)")
                        } else {
                            String::new()
                        }
                    ),
                    "--fired",
                )
            } else {
                (
                    format!("a case whose run reaches a state that {name} matches"),
                    "--matched",
                )
            };
            targets.push(json!({
                "family": "rules",
                "item": id,
                "text": format!("{text}{}", touched_note(&touched)),
                "file": file,
                "line": line,
                "programs": if status == MATCHED { entered.clone() } else { Vec::new() },
                // A front end's template-matched sentence has a bare variable as its K left-hand
                // side, so the K text is no pattern of its match.
                "pattern": if status == UNMATCHED && !templated {
                    item["pattern"].clone()
                } else {
                    Value::Null
                },
                "fuzz": match (rewrite, &rule_spelling) {
                    (true, Some(rule)) => json!(format!("{fuzz} --template ID {job} {rule}")),
                    // An equation's firing (an instance that gave a result) is a coverage fact
                    // the rule jobs do not target.
                    _ => cover(&id),
                },
            }));
        }
        for requirement in &requirements {
            if requirement["covered"] == true {
                continue;
            }
            if requirement["level"] == MCDC {
                requirement_targets.push(json!({
                    "family": "requirements",
                    "item": requirement["id"],
                    "text": mcdc_target(&name, requirement),
                    "file": file,
                    "line": line,
                    "programs": entered,
                    "pattern": null,
                    "fuzz": null,
                }));
                continue;
            }
            let truth = requirement["truth"].as_str().unwrap_or_default();
            // The valuation that reaches the requirement's node with its truth: the nodes before
            // it with the truths that reach it, then the node.
            let valuation = |truth: &str| {
                let mut valuation = requirement["reaching"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .map(|step| {
                        format!(
                            "{} {}",
                            step["text"].as_str().unwrap_or_default(),
                            step["truth"]
                        )
                    })
                    .collect::<Vec<_>>();
                valuation.push(format!(
                    "{} {truth}",
                    requirement["text"].as_str().unwrap_or_default()
                ));
                listed(&valuation)
            };
            let outcome = |words: &str| match requirement["node_truth"].as_str() {
                Some(node_truth) => format!(
                    "a case that enters {name} with its condition {words} ({})",
                    valuation(node_truth)
                ),
                None => format!("a case that enters {name} with its condition {words}"),
            };
            let text = match truth {
                "held" => outcome("holding"),
                "refuted" => outcome("false"),
                _ => format!("a case that enters {name} with {}", valuation(truth)),
            };
            let touched = ids(&requirement["touched_only_by"]);
            requirement_targets.push(json!({
                "family": "requirements",
                "item": requirement["id"],
                "text": format!("{text}{}", touched_note(&touched)),
                "file": file,
                "line": line,
                "programs": entered,
                "pattern": null,
                "fuzz": requirement["id"].as_str().map_or(Value::Null, cover),
            }));
        }
        requirement_items.extend(requirements);
    }
    let obligations = status_counts.get(FIRED).copied().unwrap_or(0)
        + status_counts.get(MATCHED).copied().unwrap_or(0)
        + status_counts.get(UNMATCHED).copied().unwrap_or(0);
    let fired = status_counts.get(FIRED).copied().unwrap_or(0);
    let count = |status: &str| status_counts.get(status).copied().unwrap_or(0);
    let requirement_covered = requirement_items
        .iter()
        .filter(|item| item["covered"] == true)
        .count();
    let requirement_obligations = requirement_items.len();
    let requirement_undecided = requirement_items
        .iter()
        .filter(|item| item["status"] == UNDECIDED)
        .count();
    let rules = &mut document["families"]["rules"];
    rules["obligations"] = json!(obligations);
    rules["covered"] = json!(fired);
    rules["measure"] = measure(fired, obligations);
    rules["counts"] = json!({
        "fired": count(FIRED),
        "matched": count(MATCHED),
        "unmatched": count(UNMATCHED),
        "out_of_scope": count(OUT_OF_SCOPE),
        "claim_helper": count(CLAIM_HELPER),
        "no_coverage_signal": count(NO_COVERAGE_SIGNAL),
        "heating": {"obligations": heating_obligations, "fired": heating_fired},
    });
    let families = &mut document["families"];
    families["requirements"] = json!({
        "tier": 1,
        "obligations": requirement_obligations,
        "covered": requirement_covered,
        "measure": measure(requirement_covered, requirement_obligations),
        "counts": {
            "covered": requirement_covered,
            "open": requirement_obligations - requirement_covered - requirement_undecided,
        },
        "items": requirement_items,
    });
    if mcdc_on {
        let level = requirement_items
            .iter()
            .filter(|item| item["level"] == MCDC)
            .collect::<Vec<_>>();
        let requirements = &mut families["requirements"];
        requirements["counts"]["undecided"] = json!(requirement_undecided);
        requirements["mcdc"] = json!({
            "rules": mcdc_rules,
            "obligations": level.len(),
            "covered": level.iter().filter(|item| item["covered"] == true).count(),
        });
    }
    let (syntax_counts, syntax_targets) = derive_syntax(&mut families["syntax"], &rule_ids, &fuzz);
    // The rule windows family, where the document built it (depth above 1); `null` otherwise.
    let rule_items_now = families["rules"]["items"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    let window_derived = if families["rule_windows"].is_object() {
        Some(windows::derive(
            &mut families["rule_windows"],
            &rule_items_now,
            &argued_entries,
        ))
    } else {
        families["rule_windows"] = Value::Null;
        None
    };
    // The syntax paths family, where the document built it (depth above 1), naming its paths by
    // the syntax family's derived names; `null` otherwise.
    let syntax_items_now = families["syntax"]["items"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    let path_derived = if families["syntax_paths"].is_object() {
        Some(paths::derive(
            &mut families["syntax_paths"],
            &syntax_items_now,
            &argued_entries,
        ))
    } else {
        families["syntax_paths"] = Value::Null;
        None
    };
    targets.extend(requirement_targets);
    targets.extend(syntax_targets);
    if let Some(derived) = &window_derived {
        targets.extend(derived.targets.iter().cloned());
    }
    if let Some(derived) = &path_derived {
        targets.extend(derived.targets.iter().cloned());
    }
    let rule_names = document["families"]["rules"]["items"]
        .as_array()
        .map_or(&[][..], Vec::as_slice)
        .iter()
        .filter_map(|item| {
            Some((
                (item["module"].as_str()?.to_owned(), item["index"].as_u64()?),
                item.clone(),
            ))
        })
        .collect::<BTreeMap<_, _>>();
    // An unreached flip waits on the reached truths that explain it; a unique-cause pair
    // explains no reach.
    let requirement_ids = requirement_items
        .iter()
        .filter(|item| item["covered"] == false && item["level"] != MCDC)
        .filter_map(|item| {
            Some((
                (
                    item["rule"].as_str()?.to_owned(),
                    item["node"].as_str()?.to_owned(),
                ),
                item["id"].as_str()?.to_owned(),
            ))
        })
        .fold(
            BTreeMap::<(String, String), Vec<String>>::new(),
            |mut ids, (key, id)| {
                ids.entry(key).or_default().push(id);
                ids
            },
        );
    let flips = derive_flips(
        &mut document["families"]["flips"],
        &rule_names,
        &requirement_ids,
        &fuzz,
        &argued_entries,
    );
    targets.extend(flips.iter().map(|(_, target)| target.clone()));
    let applied = argue(document, &argued_entries, &failed);
    targets.retain(|target| {
        target["item"]
            .as_str()
            .is_none_or(|id| !applied.argued.contains(id))
    });
    let argued_in = |family: &str| applied.counts.get(family).copied().unwrap_or(0);
    let per_family = |family: &str, covered: usize, obligations: usize| {
        let argued = argued_in(family);
        json!({
            "obligations": obligations,
            "covered": covered,
            "argued": argued,
            "open": obligations - covered - argued,
        })
    };
    let mut per = Map::new();
    per.insert("rules".into(), per_family("rules", fired, obligations));
    per.insert(
        "requirements".into(),
        per_family("requirements", requirement_covered, requirement_obligations),
    );
    if let Some(derived) = &window_derived {
        per.insert(
            "rule_windows".into(),
            derived.counts.map_or_else(
                || json!({"obligations": null, "covered": null, "argued": 0, "open": null}),
                |(covered, obligations)| per_family("rule_windows", covered, obligations),
            ),
        );
    }
    per.insert(
        "syntax".into(),
        syntax_counts.map_or_else(
            || json!({"obligations": null, "covered": null, "argued": 0, "open": null}),
            |(covered, obligations)| per_family("syntax", covered, obligations),
        ),
    );
    if let Some(derived) = &path_derived {
        per.insert(
            "syntax_paths".into(),
            derived.counts.map_or_else(
                || json!({"obligations": null, "covered": null, "argued": 0, "open": null}),
                |(covered, obligations)| per_family("syntax_paths", covered, obligations),
            ),
        );
    }
    let family = &document["families"]["flips"];
    if family["run"] == true {
        per.insert(
            "flips".into(),
            per_family(
                "flips",
                family["covered"].as_u64().unwrap_or(0) as usize,
                family["counted"].as_u64().unwrap_or(0) as usize,
            ),
        );
    }
    let covered = per
        .values()
        .filter_map(|counts| counts["covered"].as_u64())
        .sum::<u64>();
    let mut summary = summary_programs;
    summary["covered"] = json!(covered);
    summary["argued"] = json!(applied.argued.len());
    summary["open"] = json!(targets.len());
    summary["per_family"] = Value::Object(per);
    summary["needless_arguments"] = json!(applied.needless);
    summary["argued_by_standing"] = argued_by_standing(document);
    summary["failed_arguments"] = json!(applied.failed);
    document["targets"] = Value::Array(targets);
    document["summary"] = summary;
}

/// The families whose items an argued entry can name, in target order.
const ARGUABLE: [&str; 6] = [
    "rules",
    "requirements",
    "syntax",
    "rule_windows",
    "syntax_paths",
    "flips",
];

/// The `[[coverage.argued]]` entries a document's settings state, argument by item id.
fn argued_entries(document: &Value) -> BTreeMap<String, String> {
    document["settings"]["argued"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|entry| {
            Some((
                entry["item"].as_str()?.to_owned(),
                entry["argument"].as_str()?.to_owned(),
            ))
        })
        .collect()
}

/// The invariant each `[[coverage.argued]]` entry a document's settings state names, by item id;
/// an entry that names none is absent.
fn argued_invariants(document: &Value) -> BTreeMap<String, String> {
    document["settings"]["argued"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|entry| {
            Some((
                entry["item"].as_str()?.to_owned(),
                entry["invariant"].as_str()?.to_owned(),
            ))
        })
        .collect()
}

/// The refuted arguments of a document's connections ([`ARGUMENT_CHECKS`]): the detail of each
/// item whose invariant's connection fails, by item id.
fn failed_arguments(document: &Value) -> BTreeMap<String, String> {
    document[ARGUMENT_CHECKS]
        .as_object()
        .into_iter()
        .flatten()
        .filter(|(_, check)| check["connection"]["status"] == CONNECTION_FAILS)
        .map(|(id, check)| {
            (
                id.clone(),
                check["connection"]["reason"]
                    .as_str()
                    .unwrap_or_default()
                    .to_owned(),
            )
        })
        .collect()
}

/// An argued item's `argument_check`, what its argument rests on (module documentation, "Argued
/// obligations"): the standing [`STANDING_TEXT`] where its entry names no invariant; under the
/// invariant `invariant`, the connection `check` gives for the item ([`ARGUMENT_CHECKS`], `not-run`
/// where none was asked), the evidence not run and no proof, and the standing
/// [`STANDING_UNCHECKED`] with its `reason`. A connection that holds shows only that the
/// invariant excludes the item, not that it holds of any state (one false everywhere excludes
/// everything), and [`STANDING_CONNECTED`] also needs the evidence, which this build does not
/// run.
fn argument_check(invariant: Option<&String>, check: Option<&Value>) -> Value {
    match invariant {
        None => json!({"standing": STANDING_TEXT}),
        Some(name) => {
            let connection = check.map_or_else(
                || json!({"status": CHECK_NOT_RUN}),
                |check| check["connection"].clone(),
            );
            let reason = if connection["status"] == CONNECTION_HOLDS {
                "the connection holds, and the evidence that the invariant holds on runs is not \
                 run"
                .to_owned()
            } else {
                format!(
                    "the connection is {}: {}",
                    connection["status"].as_str().unwrap_or(CHECK_NOT_RUN),
                    connection["reason"]
                        .as_str()
                        .unwrap_or("no connection was asked")
                )
            };
            json!({
                "invariant": name,
                "standing": STANDING_UNCHECKED,
                "reason": reason,
                "connection": connection,
                "evidence": {"status": CHECK_NOT_RUN},
                "proof": null,
            })
        }
    }
}

/// The number of argued items of each standing (the summary's `argued_by_standing`, keyed by
/// [`STANDINGS`] with `_` for `-`): every item of an arguable family whose status is [`ARGUED`],
/// so that the numbers add up to the summary's `argued`.
fn argued_by_standing(document: &Value) -> Value {
    let mut counts = STANDINGS.map(|standing| (standing, 0_u64));
    for family in ARGUABLE {
        for item in document["families"][family]["items"]
            .as_array()
            .into_iter()
            .flatten()
            .filter(|item| item["status"] == ARGUED)
        {
            let standing = item["argument_check"]["standing"]
                .as_str()
                .unwrap_or(STANDING_TEXT);
            if let Some((_, count)) = counts.iter_mut().find(|(known, _)| *known == standing) {
                *count += 1;
            }
        }
    }
    Value::Object(
        counts
            .into_iter()
            .map(|(standing, count)| (standing.replace('-', "_"), json!(count)))
            .collect(),
    )
}

/// Undo [`argue`] on the items [`derive`] keeps from one application to the next (the rules',
/// the syntax family's and the flips'; the requirements are rebuilt), so that deriving twice
/// gives what deriving once does.
fn unargue(document: &mut Value) {
    for family in ARGUABLE {
        let Some(items) = document
            .get_mut("families")
            .and_then(|families| families.get_mut(family))
            .and_then(|family| family.get_mut("items"))
            .and_then(Value::as_array_mut)
        else {
            continue;
        };
        for item in items.iter_mut().filter_map(Value::as_object_mut) {
            if let Some(status) = item.remove("unargued_status") {
                item.insert("status".into(), status);
            }
            item.remove("argument");
            item.remove("argument_needless");
            item.remove("argument_check");
            item.remove("argument_failed");
        }
    }
}

/// What [`argue`] applied: the ids now `argued`, their number per family, the needless
/// arguments (`{family, item, reason}`) and the refuted ones (`{family, item, check, detail}`),
/// in family then item order.
struct Applied {
    argued: BTreeSet<String>,
    counts: BTreeMap<&'static str, usize>,
    needless: Vec<Value>,
    failed: Vec<Value>,
}

/// Apply the argued entries `entries` to the derived items of `document` (module documentation,
/// "Argued obligations"). An open obligation an entry names takes status [`ARGUED`], keeps the
/// status it had as `unargued_status`, and carries its `argument`; it stays in its family's
/// obligations, is not covered, and gives no target. An entry naming an item that is covered, or
/// that is no obligation, is needless (`argument_needless`, [`NEEDLESS_COVERED`] or
/// [`NEEDLESS_NOT_OBLIGATION`]): the item keeps its status and carries the argument, and the
/// summary lists it, since an argument kept on a covered item would turn the item's next
/// regression into `argued` instead of `open`. An open obligation whose entry's argument a check
/// refuted (`failed`, its detail by id) keeps its status, carries its argument and
/// `argument_failed` (`{check, detail}`), and the summary lists it: the argument stands in for
/// nothing, and the item gives its target. Each family's counts gain `argued`, taken from the
/// status the item had.
fn argue(
    document: &mut Value,
    entries: &BTreeMap<String, String>,
    failed: &BTreeMap<String, String>,
) -> Applied {
    use crate::flips::{
        DISTINGUISHED, UNDISTINGUISHED, UNKNOWN as FLIP_UNKNOWN, UNREACHED as FLIP_UNREACHED,
    };
    let mut applied = Applied {
        argued: BTreeSet::new(),
        counts: BTreeMap::new(),
        needless: Vec::new(),
        failed: Vec::new(),
    };
    let invariants = argued_invariants(document);
    let checks = document[ARGUMENT_CHECKS].clone();
    let all = argued_entries(document);
    for family in ARGUABLE {
        let value = &mut document["families"][family];
        if family == "flips" && value["run"] != true {
            continue;
        }
        let Some(items) = value.get_mut("items").and_then(Value::as_array_mut) else {
            continue;
        };
        let mut argued_from = Vec::<(String, Value)>::new();
        for item in items.iter_mut() {
            let Some(id) = item["id"].as_str().map(str::to_owned) else {
                continue;
            };
            if let Some(detail) = failed.get(&id) {
                if let Some(argument) = all.get(&id) {
                    item["argument"] = json!(argument);
                    item["argument_failed"] = json!({"check": CHECK_CONNECTION, "detail": detail});
                    applied.failed.push(json!({
                        "family": family,
                        "item": id,
                        "check": CHECK_CONNECTION,
                        "detail": detail,
                    }));
                }
                continue;
            }
            let Some(argument) = entries.get(&id) else {
                continue;
            };
            let status = item["status"].clone();
            let (open, covered) = if family == "flips" {
                let status = status.as_str().unwrap_or_default();
                (
                    matches!(status, UNDISTINGUISHED | FLIP_UNREACHED | FLIP_UNKNOWN),
                    status == DISTINGUISHED,
                )
            } else {
                (
                    item["obligation"] != false && item["covered"] == false,
                    item["covered"] == true,
                )
            };
            item["argument"] = json!(argument);
            if open {
                item["unargued_status"] = status.clone();
                item["status"] = json!(ARGUED);
                item["argument_check"] = argument_check(invariants.get(&id), checks.get(&id));
                applied.argued.insert(id.clone());
                *applied.counts.entry(family).or_default() += 1;
                argued_from.push((id, status));
            } else {
                let reason = if covered {
                    NEEDLESS_COVERED
                } else {
                    NEEDLESS_NOT_OBLIGATION
                };
                item["argument_needless"] = json!(reason);
                applied
                    .needless
                    .push(json!({"family": family, "item": id, "reason": reason}));
            }
        }
        // The kind of each argued syntax item, for the counts by kind.
        let kinds = items
            .iter()
            .filter(|item| item["status"] == ARGUED)
            .map(|item| item["kind"].as_str() == Some(FIELD_VALUE))
            .collect::<Vec<_>>();
        // A window argued by a part it contains (`argued_by`, `windows::derive`) is argued with
        // no entry of its own.
        // Its argument is the entry's, and so is what the argument rests on.
        for item in items
            .iter_mut()
            .filter(|item| item["argued_by"].is_string())
        {
            let by = item["argued_by"].as_str().unwrap_or_default();
            item["argument_check"] = argument_check(invariants.get(by), checks.get(by));
            if let Some(id) = item["id"].as_str() {
                applied.argued.insert(id.to_owned());
                *applied.counts.entry(family).or_default() += 1;
            }
        }
        let argued = applied.counts.get(family).copied().unwrap_or(0);
        value["argued"] = json!(argued);
        let counts = &mut value["counts"];
        if !counts.is_object() {
            continue;
        }
        counts["argued"] = json!(argued);
        // The status each argued item had leaves its count.
        let less = |counts: &mut Value, key: &str| {
            if let Some(n) = counts[key].as_u64() {
                counts[key] = json!(n.saturating_sub(1));
            }
        };
        for (_, status) in &argued_from {
            match family {
                "rules" | "flips" => {
                    if let Some(status) = status.as_str() {
                        less(counts, &status.replace('-', "_"));
                    }
                }
                "requirements" => less(counts, status.as_str().unwrap_or("open")),
                "rule_windows" => less(counts, windows::OPEN),
                _ => less(counts, "unreached"),
            }
        }
        if family == "syntax" {
            for kind_key in ["productions", "field_values"] {
                counts[kind_key]["argued"] = json!(0);
            }
            for field_value in kinds {
                let key = if field_value {
                    "field_values"
                } else {
                    "productions"
                };
                let n = counts[key]["argued"].as_u64().unwrap_or(0);
                counts[key]["argued"] = json!(n + 1);
            }
        }
    }
    applied
}

/// Fill the derived part of the syntax family `family` ([`syntax_family`]), `rule_ids` naming
/// each rule by its sentence: each item's `id`, `obligation`, `covered` and `touched_only_by`,
/// the sentences that inspect and build it by rule id (`inspecting_rules`, `building_rules`), the
/// counts and the measure, productions and field values counted together and each apart. Returns
/// `(covered, obligations)` and the family's targets, in item order. A family whose syntax facts
/// could not be read (its `reason`) has no universe to count: its counts and measure are null,
/// and so is the `(covered, obligations)` returned.
///
/// An item's name is its front end's (`krs.item`) where it gave one, else its K label. Every item
/// is an obligation, covered when its status is [`REACHED`]; an item a front end added (kind
/// [`FIELD_VALUE`]) states its own target text (`krs.target`), as only the front end knows the
/// inputs that reach a field's value.
fn derive_syntax(
    family: &mut Value,
    rule_ids: &BTreeMap<SentenceRef, String>,
    fuzz: &str,
) -> (Option<(usize, usize)>, Vec<Value>) {
    let mut targets = Vec::new();
    if family["reason"].is_string() {
        for key in ["obligations", "covered", "measure", "counts"] {
            family[key] = Value::Null;
        }
        return (None, targets);
    }
    let Some(items) = family.get_mut("items").and_then(Value::as_array_mut) else {
        return (Some((0, 0)), targets);
    };
    let name_of = |item: &Value| {
        item["krs"]["item"]
            .as_str()
            .or_else(|| item["production"].as_str())
            .unwrap_or_default()
            .to_owned()
    };
    // An item's name, qualified by its sort where two items share a name, and further by its
    // symbol where two share both (two front-end names of one sort): one id per item.
    let names = items.iter().map(name_of).collect::<Vec<_>>();
    let mut counts = BTreeMap::<&str, usize>::new();
    for name in &names {
        *counts.entry(name.as_str()).or_default() += 1;
    }
    let qualified = items
        .iter()
        .zip(&names)
        .map(|(item, name)| {
            if counts[name.as_str()] > 1 {
                format!("{name}@{}", item["sort"].as_str().unwrap_or_default())
            } else {
                name.clone()
            }
        })
        .collect::<Vec<_>>();
    let mut qualified_counts = BTreeMap::<&str, usize>::new();
    for name in &qualified {
        *qualified_counts.entry(name.as_str()).or_default() += 1;
    }
    // Per kind, (covered, obligations).
    let mut by_kind = BTreeMap::<String, (usize, usize)>::new();
    let mut unique = BTreeMap::<String, usize>::new();
    for (item, qualified) in items.iter_mut().zip(&qualified) {
        let mut name = if qualified_counts[qualified.as_str()] > 1 {
            match item["symbol"].as_str() {
                Some(symbol) => format!("{qualified}@{symbol}"),
                None => qualified.clone(),
            }
        } else {
            qualified.clone()
        };
        // A front end's items that share a name, a sort and a symbol (or have none) are told
        // apart by their position among those that share it.
        let seen = unique.entry(name.clone()).or_default();
        *seen += 1;
        if *seen > 1 {
            name = format!("{name}#{seen}");
        }
        let id = format!("syntax:{name}");
        let covered = item["status"] == REACHED;
        let kind = item["kind"].as_str().unwrap_or(PRODUCTION).to_owned();
        let tally = by_kind.entry(kind.clone()).or_default();
        tally.1 += 1;
        if covered {
            tally.0 += 1;
        }
        let touched = if covered {
            Vec::new()
        } else {
            without(
                TOUCHES
                    .iter()
                    .flat_map(|way| ids(&item["uncounted"][*way]))
                    .collect(),
                &[],
            )
        };
        let rules_of = |key: &str| -> Vec<String> {
            let mut named = Vec::new();
            for at in item[key].as_array().into_iter().flatten().filter_map(at_of) {
                if let Some(id) = rule_ids.get(&at)
                    && !named.contains(id)
                {
                    named.push(id.clone());
                }
            }
            named
        };
        let (inspecting, building) = (rules_of("inspecting"), rules_of("building"));
        item["id"] = json!(id);
        item["obligation"] = json!(true);
        item["covered"] = json!(covered);
        item["touched_only_by"] = json!(touched);
        item["inspecting_rules"] = json!(inspecting);
        item["building_rules"] = json!(building);
        if covered {
            continue;
        }
        let text = if let Some(text) = item["krs"]["target"].as_str() {
            text.to_owned()
        } else {
            let mut text = format!(
                "a case in which a step takes {name} as an operand, or inspects or builds it"
            );
            if !inspecting.is_empty() {
                text.push_str(&format!("; {} inspect it", listed(&inspecting)));
            }
            if !building.is_empty() {
                text.push_str(&format!("; {} build it", listed(&building)));
            }
            if inspecting.is_empty() && building.is_empty() {
                text.push_str(
                    "; no rule writes it, so only a step that takes it as an operand reaches it",
                );
            }
            text
        };
        let (file, line) = position(item);
        let mut sentences = inspecting.clone();
        sentences.extend(
            building
                .iter()
                .filter(|id| !inspecting.contains(id))
                .cloned(),
        );
        // A production's facts are the definition's; a field value's are its front end's binder
        // (`binder`), without which no run's fact reaches it.
        let fuzzable = kind != FIELD_VALUE || item["binder"].is_object();
        targets.push(json!({
            "family": "syntax",
            "item": id,
            "text": format!("{text}{}", touched_note(&touched)),
            "file": file,
            "line": line,
            "programs": [],
            "rules": sentences,
            "pattern": null,
            "fuzz": if fuzzable {
                json!(format!("{fuzz} --template ID --cover {}", shell_word(&id)))
            } else {
                Value::Null
            },
        }));
    }
    let (covered, obligations) = by_kind
        .values()
        .fold((0, 0), |(c, o), (kc, ko)| (c + kc, o + ko));
    let tally = |kind: &str| {
        let (covered, obligations) = by_kind.get(kind).copied().unwrap_or_default();
        json!({"obligations": obligations, "covered": covered})
    };
    family["obligations"] = json!(obligations);
    family["covered"] = json!(covered);
    family["measure"] = measure(covered, obligations);
    family["counts"] = json!({
        "reached": covered,
        "unreached": obligations - covered,
        "productions": tally(PRODUCTION),
        "field_values": tally(FIELD_VALUE),
    });
    (Some((covered, obligations)), targets)
}

/// Fill the derived part of a flips family that ran ([`crate::flips`]): each item's
/// `sentences` (the rules it flips, by rule id, name and position) and each occurrence's
/// `rule`; an `unreached` item's `waits_on`, the open tier-1 obligations that explain it (the
/// open requirements of an operand node, else the rule); the counts, `covered` (distinguished),
/// `counted` (the obligations less the refused and equivalent ones, which no program can meet)
/// and the measure. Returns each open item's id and target, in item order: an undistinguished
/// flip asks for a case whose result the flip changes, naming the values of the atom the corpus
/// reached and the programs that reached it (the templates of a fuzz job, `fuzz --kill`); an
/// unreached one for a case that reaches it, naming its tier-1 obligations; an unknown one for a
/// comparable run of its mutant. A family that did not run is left as it is.
fn derive_flips(
    family: &mut Value,
    rules: &BTreeMap<(String, u64), Value>,
    requirements: &BTreeMap<(String, String), Vec<String>>,
    fuzz: &str,
    argued: &BTreeMap<String, String>,
) -> Vec<(String, Value)> {
    use crate::flips::{DISTINGUISHED, EQUIVALENT, REFUSED, UNDISTINGUISHED, UNKNOWN, UNREACHED};
    if family["run"] != true {
        return Vec::new();
    }
    let mut targets = Vec::new();
    let empty = Vec::new();
    let items = family["items"].as_array().cloned().unwrap_or_default();
    let mut derived = Vec::new();
    for mut item in items {
        let mut sentences = Vec::<Value>::new();
        let mut waits_on = Vec::<String>::new();
        // The values the corpus reached, per occurrence: `<truth> in <rule> (<programs>)`.
        let mut values = Vec::new();
        let mut reached_by = Vec::new();
        if let Some(occurrences) = item.get_mut("occurrences").and_then(Value::as_array_mut) {
            for occurrence in occurrences {
                let key = (
                    occurrence["module"].as_str().unwrap_or_default().to_owned(),
                    occurrence["index"].as_u64().unwrap_or(0),
                );
                let rule = rules.get(&key);
                let id = rule.and_then(|rule| rule["id"].as_str()).map(str::to_owned);
                occurrence["rule"] = json!(id);
                if let (Some(rule), Some(id)) = (rule, &id)
                    && !sentences
                        .iter()
                        .any(|sentence| sentence["rule"] == id.as_str())
                {
                    let (file, line) = position(rule);
                    sentences.push(json!({
                        "rule": id, "name": rule_name(rule), "label": rule["label"],
                        "file": file, "line": line,
                    }));
                }
                let mut waits = id
                    .as_ref()
                    .zip(occurrence["path"].as_str())
                    .and_then(|(id, path)| requirements.get(&(id.clone(), path.to_owned())))
                    .unwrap_or(&empty)
                    .clone();
                if waits.is_empty()
                    && let Some(id) = &id
                {
                    waits.push(id.clone());
                }
                for wait in waits {
                    if !waits_on.contains(&wait) {
                        waits_on.push(wait);
                    }
                }
                let name = rule.map_or_else(|| "?".to_owned(), rule_name);
                for truth in ["true", "false"] {
                    let programs = ids(&occurrence[format!("{truth}_by")]);
                    if !programs.is_empty() {
                        values.push(format!("{truth} in {name} ({})", listed(&programs)));
                    }
                }
                reached_by.extend(ids(&occurrence["reached_by"]));
            }
        }
        let names = sentences
            .iter()
            .filter_map(|sentence| sentence["name"].as_str().map(str::to_owned))
            .collect::<Vec<_>>();
        item["sentences"] = json!(sentences);
        let status = item["status"].as_str().unwrap_or_default().to_owned();
        item["waits_on"] = json!(if status == UNREACHED {
            waits_on.clone()
        } else {
            Vec::new()
        });
        let id = item["id"].as_str().unwrap_or_default().to_owned();
        let text = item["text"].as_str().unwrap_or_default().to_owned();
        let (changed, changes) = if item["operator"] == "bitflip" {
            ("toggled", "toggles")
        } else {
            ("negated", "negates")
        };
        let (file, line) = sentences.first().map_or((Value::Null, Value::Null), |s| {
            (s["file"].clone(), s["line"].clone())
        });
        let target = |text: String, programs: Vec<String>, fuzz: Value| {
            json!({
                "family": "flips", "item": id, "text": text, "file": file, "line": line,
                "programs": programs, "pattern": null, "fuzz": fuzz,
            })
        };
        let in_names = if names.is_empty() {
            String::new()
        } else {
            format!(" in {}", listed(&names))
        };
        match status.as_str() {
            UNDISTINGUISHED => {
                let values = if values.is_empty() {
                    String::new()
                } else {
                    format!("; the corpus reached it {}", listed(&values))
                };
                targets.push((
                    id.clone(),
                    target(
                        format!(
                            "a case whose result changes when {text} is {changed}{in_names}{values}"
                        ),
                        without(reached_by, &[]),
                        json!(format!("{fuzz} --template ID --kill {id}")),
                    ),
                ));
            }
            UNREACHED => targets.push((
                id.clone(),
                target(
                    format!(
                        "a case that reaches {text}{in_names}: no comparable program does, so \
                         no program can tell the flip apart ({})",
                        waiting(&waits_on, argued)
                    ),
                    Vec::new(),
                    Value::Null,
                ),
            )),
            UNKNOWN => targets.push((
                id.clone(),
                target(
                    format!(
                        "a comparable run of the mutant that {changes} {text}{in_names}: kink \
                         gave no verdict ({})",
                        no_verdict(&item)
                    ),
                    Vec::new(),
                    Value::Null,
                ),
            )),
            _ => {}
        }
        derived.push(item);
    }
    let count = |status: &str| {
        derived
            .iter()
            .filter(|item| item["status"] == status)
            .count()
    };
    let distinguished = count(DISTINGUISHED);
    let counted = derived.len() - count(REFUSED) - count(EQUIVALENT);
    let not_generated = family["not_generated"].as_array().map_or(0, Vec::len);
    family["counts"] = crate::flips::counts(&derived, not_generated);
    family["covered"] = json!(distinguished);
    family["counted"] = json!(counted);
    family["measure"] = measure(distinguished, counted);
    family["items"] = Value::Array(derived);
    targets
}

/// Why the kill search gave an `unknown` flip no verdict, as its target states it: the row's
/// `reason` where it has one (a cause of the whole search), else kink's status where it is not
/// `unknown` (`timeout`, `error`), then each executed program's cause (`causes`, `<program>:
/// <cause>`), joined by `; `. A row need carry none of them (an outcome cache's `unknown` entry
/// recorded with no cause is input, not an invariant), and the text then says that kink
/// recorded no cause, rather than invent one.
fn no_verdict(item: &Value) -> String {
    let mut parts = Vec::new();
    if let Some(reason) = item["reason"].as_str() {
        parts.push(reason.to_owned());
    } else if let Some(status) = item["kink_status"]
        .as_str()
        .filter(|status| *status != "unknown")
    {
        parts.push(status.to_owned());
    }
    for cause in item["causes"].as_array().into_iter().flatten() {
        if let (Some(program), Some(cause)) = (cause["program"].as_str(), cause["cause"].as_str()) {
            parts.push(format!("{program}: {cause}"));
        }
    }
    if parts.is_empty() {
        "kink recorded no cause".to_owned()
    } else {
        parts.join("; ")
    }
}

/// The tier-1 obligations an unreached flip waits on, as its target states them: the open ones,
/// then those `[[coverage.argued]]` argues (`X open; Y argued`).
fn waiting(waits_on: &[String], argued: &BTreeMap<String, String>) -> String {
    let (argued, open): (Vec<String>, Vec<String>) = waits_on
        .iter()
        .cloned()
        .partition(|id| argued.contains_key(id));
    let mut parts = Vec::new();
    if !open.is_empty() {
        parts.push(format!("{} open", listed(&open)));
    }
    if !argued.is_empty() {
        parts.push(format!("{} argued", listed(&argued)));
    }
    parts.join("; ")
}

/// What a family's line of the text rendering adds for its argued items: `, N argued`, or
/// nothing when none is argued.
fn argued_note(family: &Value) -> String {
    match family["argued"].as_u64() {
        Some(n) if n > 0 => format!(", {n} argued"),
        _ => String::new(),
    }
}

/// A measure as text: a percentage with one decimal, `-` without obligations.
fn percent(measure: &Value) -> String {
    measure
        .as_f64()
        .map_or_else(|| "-".to_owned(), |ratio| format!("{:.1}%", ratio * 100.0))
}

/// The `--output text` rendering of a coverage document: one line per family with covered /
/// obligations and the measure, the programs that cannot count, then one line per open target
/// with its position, its pattern and its fuzz hint. It is a reading aid, not a lock: its
/// wording may change without any coverage changing (`--output verdicts` is the lock format). The error names what
/// the document is when it is no coverage document.
pub fn text(document: &Value) -> Result<String, String> {
    if document["schema"] != COVERAGE_SCHEMA {
        return Err(format!(
            "--output text renders a coverage document, not {}",
            document["schema"]
                .as_str()
                .unwrap_or("a document with no schema")
        ));
    }
    let mut out = String::new();
    if document["lock"]["outcome"] == "refused" {
        out.push_str(&format!(
            "coverage: the coverage lock is refused: {}\n",
            document["lock"]["detail"].as_str().unwrap_or("no detail"),
        ));
        return Ok(out);
    }
    if document["spec"]["outcome"] == "refused" {
        out.push_str(&format!(
            "coverage: the specification is refused at stage {}, {}: {}\n",
            document["spec"]["stage"].as_str().unwrap_or("?"),
            document["spec"]["reason"].as_str().unwrap_or("?"),
            document["spec"]["detail"].as_str().unwrap_or("no detail"),
        ));
        return Ok(out);
    }
    let summary = &document["summary"];
    out.push_str(&format!(
        "coverage: {} covered, {} argued, {} open; {} programs, {} comparable\n",
        summary["covered"],
        summary["argued"],
        summary["open"],
        summary["programs"],
        summary["comparable"]
    ));
    let families = &document["families"];
    for family in ["rules", "requirements"] {
        let value = &families[family];
        let what = if family == "rules" {
            "fired"
        } else {
            "covered"
        };
        out.push_str(&format!(
            "{family}: {} of {} {what} ({}){}",
            value["covered"],
            value["obligations"],
            percent(&value["measure"]),
            argued_note(value)
        ));
        if let Some(level) = value["mcdc"].as_object() {
            out.push_str(&format!(
                "; unique-cause: {} of {} covered, {} undecided",
                level["covered"], level["obligations"], value["counts"]["undecided"]
            ));
        }
        if family == "rules" {
            let counts = &value["counts"];
            out.push_str(&format!(
                "; {} matched, {} unmatched; heating {} of {} fired; not obligations: {} out of \
                 scope, {} claim helper, {} no coverage signal",
                counts["matched"],
                counts["unmatched"],
                counts["heating"]["fired"],
                counts["heating"]["obligations"],
                counts["out_of_scope"],
                counts["claim_helper"],
                counts["no_coverage_signal"]
            ));
        }
        out.push('\n');
    }
    let syntax = &families["syntax"];
    if let Some(reason) = syntax["reason"].as_str() {
        out.push_str(&format!("syntax: not read: {reason}\n"));
    } else if syntax.is_object() {
        let counts = &syntax["counts"];
        out.push_str(&format!(
            "syntax: {} of {} reached ({}){}; productions {} of {}, field values {} of {}",
            syntax["covered"],
            syntax["obligations"],
            percent(&syntax["measure"]),
            argued_note(syntax),
            counts["productions"]["covered"],
            counts["productions"]["obligations"],
            counts["field_values"]["covered"],
            counts["field_values"]["obligations"],
        ));
        out.push('\n');
    }
    let windows = &families["rule_windows"];
    if let Some(reason) = windows["reason"].as_str() {
        out.push_str(&format!("rule_windows: not read: {reason}\n"));
    } else if windows.is_object() {
        let counts = &windows["counts"];
        let lengths = counts["by_length"]
            .as_object()
            .into_iter()
            .flatten()
            .map(|(length, count)| {
                format!(
                    "length {length} {} of {}",
                    count["covered"], count["obligations"]
                )
            })
            .collect::<Vec<_>>()
            .join(", ");
        out.push_str(&format!(
            "rule_windows: {} of {} covered ({}){}; {lengths}; {} on the frontier; may-follow \
             graph of {} rules, {} edges\n",
            windows["covered"],
            windows["obligations"],
            percent(&windows["measure"]),
            argued_note(windows),
            counts["frontier"],
            windows["nodes"],
            windows["edges"],
        ));
    }
    let paths = &families["syntax_paths"];
    if let Some(reason) = paths["reason"].as_str() {
        out.push_str(&format!("syntax_paths: not read: {reason}\n"));
    } else if paths.is_object() {
        let counts = &paths["counts"];
        let lengths = counts["by_length"]
            .as_object()
            .into_iter()
            .flatten()
            .map(|(length, count)| {
                format!(
                    "length {length} {} of {}",
                    count["covered"], count["obligations"]
                )
            })
            .collect::<Vec<_>>()
            .join(", ");
        out.push_str(&format!(
            "syntax_paths: {} of {} reached ({}){}; {lengths}; joint field values {} of {}; {} on \
             the frontier; grammar graph of {} productions, {} edges\n",
            paths["covered"],
            paths["obligations"],
            percent(&paths["measure"]),
            argued_note(paths),
            counts["field_values"]["covered"],
            counts["field_values"]["obligations"],
            counts["frontier"],
            paths["productions"],
            paths["edges"],
        ));
    }
    // A depth-dependent family is computed above depth 1 only.
    for family in ["syntax", "rule_windows", "syntax_paths"] {
        if families[family].is_null() {
            let why = if family != "syntax" && document["settings"]["depth"] == 1 {
                "computed above depth 1 only"
            } else {
                "not computed"
            };
            out.push_str(&format!("{family}: {why}\n"));
        }
    }
    let flips = &families["flips"];
    if flips["run"] == false {
        out.push_str(&format!(
            "flips: not run: {}\n",
            flips["reason"].as_str().unwrap_or_default()
        ));
    } else if flips["run"] == true {
        let counts = &flips["counts"];
        out.push_str(&format!(
            "flips: {} of {} distinguished ({}){}; {} undistinguished, {} unreached, {} unknown; \
             not counted: {} refused, {} equivalent; {} not generated\n",
            flips["covered"],
            flips["counted"],
            percent(&flips["measure"]),
            argued_note(flips),
            counts["undistinguished"],
            counts["unreached"],
            counts["unknown"],
            counts["refused"],
            counts["equivalent"],
            counts["not_generated"],
        ));
        for item in flips["items"].as_array().into_iter().flatten() {
            if item["status"] == crate::flips::REFUSED {
                out.push_str(&format!(
                    "flip {}: refused by the {}: {}: {}\n",
                    item["id"].as_str().unwrap_or("?"),
                    if item["judge"] == "kink-flow" {
                        "kink-flow admission"
                    } else {
                        "front end's judge"
                    },
                    item["reason"].as_str().unwrap_or("?"),
                    item["detail"].as_str().unwrap_or("no detail"),
                ));
            }
        }
    }
    for program in document["programs"].as_array().into_iter().flatten() {
        if !ResultClass::can_kill(&program["class"]) {
            out.push_str(&format!(
                "program {}: {}, counts for nothing: {}\n",
                program["id"].as_str().unwrap_or("?"),
                program["class"].as_str().unwrap_or("?"),
                program["cause"].as_str().unwrap_or("no cause"),
            ));
        }
    }
    let mut argued = Vec::new();
    let mut needless = Vec::new();
    let mut failed = Vec::new();
    for family in ARGUABLE {
        for item in families[family]["items"].as_array().into_iter().flatten() {
            let Some(argument) = item["argument"].as_str() else {
                continue;
            };
            let id = item["id"].as_str().unwrap_or("?");
            if let Some(detail) = item["argument_failed"]["detail"].as_str() {
                failed.push(format!(
                    "  {id} [the {} fails]: {detail}; it is open again\n",
                    item["argument_failed"]["check"]
                        .as_str()
                        .unwrap_or(CHECK_CONNECTION)
                ));
            } else if item["status"] == ARGUED {
                let check = &item["argument_check"];
                let standing = check["standing"].as_str().unwrap_or(STANDING_TEXT);
                let rests = match check["invariant"].as_str() {
                    Some(invariant) => format!("{standing}, invariant {invariant}"),
                    None => standing.to_owned(),
                };
                argued.push(format!("  {id} [{rests}]: {argument}\n"));
            } else {
                let why = if item["argument_needless"] == NEEDLESS_COVERED {
                    "a program covers it"
                } else {
                    "it is no obligation"
                };
                needless.push(format!(
                    "  {id}: {why}; remove its [[coverage.argued]] entry\n"
                ));
            }
        }
    }
    if !argued.is_empty() {
        out.push_str("argued:\n");
        out.push_str(&argued.concat());
    }
    if !needless.is_empty() {
        out.push_str("needless arguments:\n");
        out.push_str(&needless.concat());
    }
    if !failed.is_empty() {
        out.push_str("failed arguments:\n");
        out.push_str(&failed.concat());
    }
    let targets = document["targets"]
        .as_array()
        .map_or(&[][..], Vec::as_slice);
    if !targets.is_empty() {
        out.push_str("targets:\n");
    }
    for target in targets {
        let at = match (target["file"].as_str(), target["line"].as_u64()) {
            (Some(file), Some(line)) => format!(" ({file}:{line})"),
            _ => String::new(),
        };
        out.push_str(&format!(
            "  {}{at}: {}\n",
            target["item"].as_str().unwrap_or("?"),
            target["text"].as_str().unwrap_or_default()
        ));
        if let Some(pattern) = target["pattern"].as_str() {
            out.push_str(&format!("    pattern: {pattern}\n"));
        }
        if let Some(fuzz) = target["fuzz"].as_str() {
            out.push_str(&format!("    fuzz: {fuzz}\n"));
        }
    }
    Ok(out)
}

/// The open ids of each family of a coverage document, in item order: what its verdicts
/// rendering lists ([`crate::verdicts`]). An argued item is not open, nor is an undecided one.
#[must_use]
pub fn open_ids(document: &Value) -> Vec<(&'static str, Vec<String>)> {
    tier_one_ids(document, |item| {
        item["covered"] == false && item["status"] != ARGUED && item["status"] != UNDECIDED
    })
}

/// The undecided ids of each tier-1 family of a coverage document, in item order ([`UNDECIDED`]):
/// what its verdicts rendering lists apart from the open ones ([`crate::verdicts`]).
#[must_use]
pub fn undecided_ids(document: &Value) -> Vec<(&'static str, Vec<String>)> {
    tier_one_ids(document, |item| item["status"] == UNDECIDED)
}

/// The argued ids of each tier-1 family of a coverage document, in item order: what its verdicts
/// rendering lists beside the open ones ([`crate::verdicts`]). A flip's argued status is its
/// row's.
#[must_use]
pub fn argued_ids(document: &Value) -> Vec<(&'static str, Vec<String>)> {
    tier_one_ids(document, |item| item["status"] == ARGUED)
}

/// Each argued item of a coverage document with the standing of its argument
/// (`argument_check.standing`), in the order of [`FAMILIES`], then item order: what its verdicts
/// rendering lists under `[arguments]` ([`crate::verdicts`]). The flips family's argued flips are
/// listed where it ran.
#[must_use]
pub fn argument_standings(document: &Value) -> Vec<(String, String)> {
    ARGUABLE
        .into_iter()
        .filter(|family| *family != "flips" || document["families"]["flips"]["run"] == true)
        .flat_map(|family| {
            document["families"][family]["items"]
                .as_array()
                .into_iter()
                .flatten()
        })
        .filter(|item| item["status"] == ARGUED)
        .filter_map(|item| {
            Some((
                item["id"].as_str()?.to_owned(),
                item["argument_check"]["standing"]
                    .as_str()
                    .unwrap_or(STANDING_TEXT)
                    .to_owned(),
            ))
        })
        .collect()
}

/// The ids of each tier-1 family's items that `keep` selects, in item order.
fn tier_one_ids(
    document: &Value,
    keep: impl Fn(&Value) -> bool,
) -> Vec<(&'static str, Vec<String>)> {
    [
        "rules",
        "requirements",
        "syntax",
        "rule_windows",
        "syntax_paths",
    ]
    .into_iter()
    // The rule windows and the syntax paths only where the document built them (depth above 1),
    // so that a rendering of depth 1 is what it was.
    .filter(|family| {
        !matches!(*family, "rule_windows" | "syntax_paths")
            || document["families"][family].is_object()
    })
    .map(|family| {
        let ids = document["families"][family]["items"]
            .as_array()
            .into_iter()
            .flatten()
            .filter(|item| keep(item))
            .filter_map(|item| item["id"].as_str().map(str::to_owned))
            .collect();
        (family, ids)
    })
    .collect()
}

/// The object a rule item names its sentence by, for readers that look one up by position.
#[must_use]
pub fn rule_item<'d>(document: &'d Value, at: &SentenceRef) -> Option<&'d Map<String, Value>> {
    document["families"]["rules"]["items"]
        .as_array()?
        .iter()
        .filter_map(Value::as_object)
        .find(|item| {
            item.get("module").and_then(Value::as_str) == Some(at.module.as_str())
                && item.get("index").and_then(Value::as_u64) == Some(u64::from(at.index))
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// What an invariant cannot argue is named by what it is, read from the derived document:
    /// an item of a rewrite rule, or a held, refuted or node requirement of one, is arguable; an
    /// equation's items, a rule that is no obligation, a unique-cause requirement, the deeper
    /// families and a flip are not.
    #[test]
    fn an_unsupported_item_is_named_by_its_kind() {
        let probe = json!({"families": {
            "rules": {"items": [
                {"id": "rule:r", "status": "matched", "rewrite": true},
                {"id": "rule:e", "status": "unmatched", "rewrite": false},
                {"id": "rule:s", "status": "out-of-scope", "rewrite": false},
                {"id": "rule:h", "status": "claim-helper", "rewrite": false},
            ]},
            "requirements": {"items": [
                {"id": "requirement:r:held", "rule": "rule:r", "level": "condition"},
                {"id": "requirement:r:A:mcdc", "rule": "rule:r", "level": "mcdc"},
                {"id": "requirement:e:refuted", "rule": "rule:e", "level": "condition"},
                {"id": "requirement:h:held", "rule": "rule:h", "level": "condition"},
            ]},
            "syntax": {"items": [{"id": "syntax:p"}]},
            "rule_windows": {"items": [{"id": "window:r,e"}]},
            "syntax_paths": {"items": [{"id": "path:p/0/q"}]},
        }});
        let kinds = [
            "rule:r",
            "requirement:r:held",
            "rule:e",
            "requirement:e:refuted",
            "rule:s",
            "requirement:h:held",
            "requirement:r:A:mcdc",
            "syntax:p",
            "window:r,e",
            "path:p/0/q",
            "flip--x",
        ]
        .map(|id| unsupported_kind(&probe, id));
        assert_eq!(
            kinds,
            [
                None,
                None,
                Some("equation"),
                Some("equation"),
                Some("out-of-scope"),
                Some("claim-helper"),
                Some("mcdc"),
                Some("syntax"),
                Some("rule_windows"),
                Some("syntax_paths"),
                Some("flip"),
            ]
        );

        // An entry both unsupported and the only one naming its table: one refusal names both.
        let manifest = FlowManifest::decode(
            "[spec]\nentry = \"m.k\"\nmain_module = \"M\"\n[[program]]\nid = \"a\"\ntext = \"a\"\n\
             [[coverage.invariant]]\nname = \"i\"\nfunction = \"f\"\ncells = [\"k\"]\n\
             [[coverage.invariant]]\nname = \"j\"\nfunction = \"g\"\ncells = [\"k\"]\n\
             [[coverage.argued]]\nitem = \"rule:r\"\nargument = \"x\"\ninvariant = \"i\"\n\
             [[coverage.argued]]\nitem = \"syntax:p\"\nargument = \"x\"\ninvariant = \"j\"\n",
            Path::new("corpus"),
        )
        .unwrap();
        let refusal = invariant_refusal(&probe, &manifest).unwrap();
        assert_eq!(refusal.reason, "argued-invariant-unsupported");
        assert!(
            refusal.detail.contains(": `syntax:p` (syntax); ")
                && refusal.detail.ends_with(
                    "; then [[coverage.invariant]] declares an invariant no other \
                     [[coverage.argued]] entry names: `j`; name it in the `invariant` of the \
                     entries whose argument rests on it, or remove the table"
                ),
            "{}",
            refusal.detail
        );
    }

    /// A family whose syntax facts could not be read counts nothing: its counts and measure are
    /// null, not zero obligations with nothing open, and it gives no target.
    #[test]
    fn an_unread_syntax_family_counts_nothing() {
        let mut family = json!({"tier": 1, "items": [], "binders": [], "reason": "unreadable"});
        let (counts, targets) = derive_syntax(&mut family, &BTreeMap::new(), "kink-flow fuzz");
        assert_eq!(counts, None);
        assert!(targets.is_empty());
        for key in ["obligations", "covered", "measure", "counts"] {
            assert_eq!(family[key], Value::Null, "{key}: {family:#}");
        }
        assert_eq!(family["reason"], "unreadable");
    }

    /// Every item has its own id: two items of one name are told apart by their sorts, two of
    /// one name and one sort by their symbols, and two that share all three by their position.
    #[test]
    fn every_syntax_item_has_its_own_id() {
        let item = |name: &str, sort: &str, symbol: &str| {
            json!({
                "kind": PRODUCTION,
                "production": name,
                "sort": sort,
                "symbol": symbol,
                "status": UNREACHED,
            })
        };
        let mut family = json!({
            "tier": 1,
            "items": [
                item("a", "S", "Lbla"),
                item("a", "T", "Lbla'T"),
                item("b", "S", "Lblb1"),
                item("b", "S", "Lblb2"),
                item("c", "S", "Lblc"),
                item("c", "S", "Lblc"),
                item("d", "S", "Lbld"),
            ],
            "binders": [],
        });
        let (counts, targets) = derive_syntax(&mut family, &BTreeMap::new(), "kink-flow fuzz");
        assert_eq!(counts, Some((0, 7)));
        assert_eq!(targets.len(), 7);
        let ids = family["items"]
            .as_array()
            .unwrap()
            .iter()
            .map(|item| item["id"].as_str().unwrap().to_owned())
            .collect::<Vec<_>>();
        assert_eq!(
            ids,
            [
                "syntax:a@S",
                "syntax:a@T",
                "syntax:b@S@Lblb1",
                "syntax:b@S@Lblb2",
                "syntax:c@S@Lblc",
                "syntax:c@S@Lblc#2",
                "syntax:d",
            ]
        );
    }

    /// A node of a guard tree: `(path, kind, krs text, K connective, children)`.
    type TreeNode<'n> = (
        &'n str,
        &'n str,
        Option<&'n str>,
        Option<&'n str>,
        &'n [&'n str],
    );

    /// A guard tree of `nodes`.
    fn tree_guard(nodes: &[TreeNode<'_>]) -> Value {
        json!({"operands": nodes.iter().map(|(path, kind, krs, connective, children)| {
            let mut node = json!({"path": path, "kind": kind, "operands": children});
            if let Some(text) = krs {
                node["krs"] = json!({"text": text, "origin": "authored"});
            }
            if let Some(connective) = connective {
                node["connective"] = json!(connective);
            }
            node
        }).collect::<Vec<_>>()})
    }

    /// An `if`/`else if` chain's condition: each `else` is a negation of the condition before
    /// it, and the valuation that reaches a later condition names the earlier ones `false`, not
    /// a negation spelt with its `else` token.
    #[test]
    fn reaching_reads_an_else_as_the_condition_before_it_false() {
        let guard = tree_guard(&[
            ("0", "conjunction", Some("&&"), None, &["0.0", "0.1", "0.2"]),
            ("0.0", "negation", Some("else"), None, &["0.0.0"]),
            ("0.0.0", "atom", Some("requested & 0x01 != 0"), None, &[]),
            ("0.1", "negation", Some("else"), None, &["0.1.0"]),
            ("0.1.0", "atom", Some("requested & 0x02 != 0"), None, &[]),
            ("0.2", "atom", Some("requested & 0x04 != 0"), None, &[]),
        ]);
        let tree = Tree::of(&guard);
        let earlier = |texts: &[&str]| {
            texts
                .iter()
                .map(|text| ((*text).to_owned(), false))
                .collect::<Vec<_>>()
        };
        assert_eq!(
            tree.reaching("0.2"),
            earlier(&["requested & 0x01 != 0", "requested & 0x02 != 0"])
        );
        assert_eq!(tree.reaching("0.1.0"), earlier(&["requested & 0x01 != 0"]));
        assert_eq!(
            tree.text("0.1").as_deref(),
            Some("!(requested & 0x02 != 0)")
        );
    }

    /// A compound sibling renders a negation as `!` before its operand, parenthesized unless
    /// the operand is a negation, an identifier, a path or a call, whatever its spacing; a
    /// negated negation reaching a node is its operand with the same truth; a K negation keeps
    /// its connective, with a space.
    #[test]
    fn a_negation_is_written_before_its_operand() {
        let guard = tree_guard(&[
            ("0", "conjunction", Some("&&"), None, &["0.0", "0.1", "0.2"]),
            ("0.0", "disjunction", Some("||"), None, &["0.0.0", "0.0.1"]),
            ("0.0.0", "atom", Some("ready"), None, &[]),
            ("0.0.1", "negation", Some("!"), None, &["0.0.1.0"]),
            ("0.0.1.0", "atom", Some("value < 0"), None, &[]),
            ("0.1", "negation", Some("!"), None, &["0.1.0"]),
            ("0.1.0", "negation", Some("!"), None, &["0.1.0.0"]),
            ("0.1.0.0", "atom", Some("halted"), None, &[]),
            ("0.2", "atom", Some("c"), None, &[]),
        ]);
        let tree = Tree::of(&guard);
        assert_eq!(
            tree.reaching("0.2"),
            [
                ("ready || !(value < 0)".to_owned(), true),
                ("halted".to_owned(), true)
            ]
        );
        assert_eq!(tree.text("0.1").as_deref(), Some("!!halted"));
        let unspaced = tree_guard(&[
            ("0", "negation", Some("!"), None, &["0.0"]),
            ("0.0", "atom", Some("x<0"), None, &[]),
            ("1", "negation", Some("!"), None, &["1.0"]),
            ("1.0", "atom", Some("self.ready(a, f(b))"), None, &[]),
            ("2", "negation", Some("!"), None, &["2.0"]),
            ("2.0", "atom", Some("f(a)(b)"), None, &[]),
            ("3", "negation", Some("!"), None, &["3.0"]),
            ("3.0", "atom", Some("crate::m::HALTED"), None, &[]),
        ]);
        let tree = Tree::of(&unspaced);
        assert_eq!(tree.text("0").as_deref(), Some("!(x<0)"));
        assert_eq!(tree.text("1").as_deref(), Some("!self.ready(a, f(b))"));
        assert_eq!(tree.text("2").as_deref(), Some("!(f(a)(b))"));
        assert_eq!(tree.text("3").as_deref(), Some("!crate::m::HALTED"));
        let k = json!({"operands": [
            {"path": "0", "kind": "negation", "connective": "notBool", "operands": ["0.0"]},
            {"path": "0.0", "kind": "atom", "text": "X <Int 0", "operands": []},
            {"path": "1", "kind": "negation", "connective": "notBool", "operands": ["1.0"]},
            {"path": "1.0", "kind": "atom", "text": "B", "operands": []},
        ]});
        let tree = Tree::of(&k);
        assert_eq!(tree.text("0").as_deref(), Some("notBool (X <Int 0)"));
        assert_eq!(tree.text("1").as_deref(), Some("notBool B"));
    }

    /// The target of the unknown flip whose run row is `row`.
    fn unknown_target(row: &Value) -> String {
        let mut item = json!({"id": "f", "operator": "flip", "text": "x", "occurrences": []});
        crate::flips::fill_from_row(&mut item, row);
        assert_eq!(item["status"], crate::flips::UNKNOWN, "{item:#}");
        let mut family = json!({"run": true, "items": [item], "not_generated": []});
        let targets = derive_flips(
            &mut family,
            &BTreeMap::new(),
            &BTreeMap::new(),
            "kink-flow fuzz",
            &BTreeMap::new(),
        );
        assert_eq!(targets.len(), 1, "{family:#}");
        targets[0].1["text"].as_str().unwrap().to_owned()
    }

    /// An unknown flip's target says why kink gave no verdict: the row's reason, else kink's
    /// status where it is not `unknown`, then each executed program's cause, in the search's
    /// order; a program with no cause is not named.
    #[test]
    fn an_unknown_flips_target_states_each_programs_cause() {
        let prefix = "a comparable run of the mutant that negates x: kink gave no verdict";
        let executed = json!([
            {"program": "p1", "cause": "the step bound (100) fired"},
            {"program": "p2", "outcome": "agree", "cause": null},
            {"program": "p3", "cause": "an undecided end"},
        ]);
        assert_eq!(
            unknown_target(&json!({"status": "unknown", "reason": null, "executed": executed})),
            format!("{prefix} (p1: the step bound (100) fired; p3: an undecided end)")
        );
        assert_eq!(
            unknown_target(&json!({"status": "timeout", "reason": null, "executed": [
                {"program": "p1", "cause": "the time limit fired"},
            ]})),
            format!("{prefix} (timeout; p1: the time limit fired)")
        );
        assert_eq!(
            unknown_target(&json!({"status": "unknown", "reason": "open-application",
                                   "executed": [{"program": "p1", "cause": "an open f(1)"}]})),
            format!("{prefix} (open-application; p1: an open f(1))")
        );
        assert_eq!(
            unknown_target(&json!({"status": "unknown", "reason": null, "executed": [
                {"program": "p1", "cause": null},
            ]})),
            format!("{prefix} (kink recorded no cause)"),
            "a cached unknown entry with no cause is input the target states"
        );
        let mut item = json!({"id": "f"});
        crate::flips::fill_from_row(
            &mut item,
            &json!({"status": "killed", "killer": "p1", "executed": executed}),
        );
        assert_eq!(item["causes"], json!([]));
    }
}
