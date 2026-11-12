//! Cargo-style command-line frontend for the KRS definition compiler.

use krs_cli::{
    Backend, CasesOutput, CasesRequest, ColorChoice, Command, CommandKind, CommandRequest,
    CompareOutput, CompareRequest, CompareSides, DEFAULT_VIEW_BUDGET, DiagnosticSources,
    FacetSelector, KrsCfg, MessageFormat, PackageSelector, ParseRequest, ProgramSource,
    ProveRequest, RegistrationMode, RunRequest, SearchMode, SearchRequest, SideFile, StopCriterion,
    StopRules, StopWhen, TermOutput, execute_command_reported, exit_status, supervise_prove,
};
use krs_fmt::{Edition, FormatOptions, TrailingCommentStyle};
use krs_ir::measure::Measurement;
use lexopt::Arg::{Long, Short, Value};
use std::ffi::OsString;
use std::fmt;
use std::io::{self, IsTerminal, Read, Write};
use std::num::NonZeroU64;
use std::path::{Path, PathBuf};

const USAGE: &str = "\
KRS definition compiler

Usage:
  krs <check|expand|emit-k|build> --package PACKAGE --definition NAME [OPTIONS]
  krs parse  --package P --definition D [--sort SORT] [--output kast|program|json|kore] [FILE|-]
  krs run    --package P --definition D [FILE|-] [--case FILE [--case-name NAME]]
             [--input NAME=JSON]... [-c NAME=TEXT]... [--depth N] [--stop-before NAME]...
             [--stop-after NAME]... [--stop-count N]
             [--stop-when CELL,...=FUNCTION [--observer PACKAGE:DEFINITION]]
             [--observe FILE] [--trace] [--coverage]
             [--output pretty|kast|json|kore|end|observations|none] [--color auto|always|never]
             [--smt-resource-limit UNITS | --smt-clock-ms MS] [--smt-retries N]
             [--view-budget POLLS]
  krs search --package P --definition D [FILE|-] [--case FILE [--case-name NAME]]
             [--input NAME=JSON]... [-c NAME=TEXT]...
             [--mode final|all|one-step|one-or-more-steps] [--depth N]
             [--max-solutions N] [--trace] [--output pretty|kast|json|kore]
             [--color auto|always|never]
             [--smt-resource-limit UNITS | --smt-clock-ms MS] [--smt-retries N]
             [--view-budget POLLS]
  krs cases  --package P --definition D CASES... [--jobs N] [--name PATTERN]
             [--output human|json] [--view-budget POLLS]
             [--smt-resource-limit UNITS | --smt-clock-ms MS] [--smt-retries N]
  krs compare --package P --definition D LEFT RIGHT [--compare CELL,...]...
             [--view CELL=FUNCTION]... [--observer PACKAGE:DEFINITION]
             [--output human|json] [--view-budget POLLS]
             [--smt-resource-limit UNITS | --smt-clock-ms MS] [--smt-retries N]
  krs compare --package P --definition D --expect CASE ACTUAL [--output human|json]
             [--view-budget POLLS]
             [--smt-resource-limit UNITS | --smt-clock-ms MS] [--smt-retries N]
  krs compare --package P --definition D --pairs FILE [--jobs N] [--output human|json]
             [--view-budget POLLS]
             [--smt-resource-limit UNITS | --smt-clock-ms MS] [--smt-retries N]
  krs prove  --package P --definition D [--spec-module NAME] [--claim LABEL]... [--depth N]
             [--claim-timeout SECONDS] [--output pretty|kast|json|jsonl|kore]
             [--color auto|always|never]
             [--smt-resource-limit UNITS | --smt-clock-ms MS] [--smt-retries N]
  krs kink <emit|check|coverage|run|report|query|fuzz|compare|prune> --package P --definition D
             [OPTIONS] (krs kink --help lists the corpus loop's options)
  krs fmt [--check] [--manifest-path PATH] [PATH ...]
  krs fmt --stdin [--edition YEAR]

Commands:
  check                     Judge the definition as emit-k, build, and the run commands do;
                            write nothing
  expand                    Print the selected Rust reference surface: the one changed module
                            file on stdout, or with --output each changed file at its path
  emit-k                    Emit canonical K with its symbol and source maps (definition.k,
                            spec.k when there are claims, symbols.json, sources.json)
  build                     Compile native backend artifacts
  parse                     Parse a program with the definition's grammar (kast)
  run                       Run a program on one path (krun)
  search                    Return the set of reachable final states (krun --search)
  prove                     Prove the definition's claims (kprove)
  cases                     Run a batch of cases, the definition loaded once per worker, and
                            report each case's verdict against its expectation
  compare                   Compare two sides of the definition, each an end document, an
                            observation document or a case's run (its end and its declared
                            observations), or check an end against a case's expectation
  kink                      The corpus loop over the package's kink/ corpus: what the cases
                            cover, mutations killed or survived, query and fuzz
  fmt                       Format Rust and KRS rules! bodies using the package's facade aliases

Options:
  --manifest-path PATH       Cargo manifest (default: Cargo.toml)
  --package PACKAGE          Root Cargo package name
  --package-id ID            Exact root Cargo package ID
  --definition NAME          Root package definition facet
  --dependency PACKAGE:NAME  Composed dependency facet; repeatable. Given, the flags replace
                             the facets the root facet declares
                             (package.metadata.krs.definitions.NAME.dependencies); not given,
                             every command composes the declared facets
  --cfg KEY[=VALUE]          KRS rustc cfg; repeatable. Given, the flags replace the values
                             the root facet declares (package.metadata.krs.definitions.NAME.cfg)
  --backend llvm|haskell     Native target dialect (default: llvm); with check, judge only
                             that backend's route (default: every route)
  --output DIRECTORY         Required for emit-k and build; with expand, an absent or empty
                             directory for the changed module files, whose paths stdout lists
  --output FORMAT            Result format: pretty (default of run, search, prove), program (parse), kast (default of parse), json, jsonl (prove), kore, end (run: the end document krs compare reads), observations (run: the krs-observations/1 document of the declared observations), none (run); human (default of cases and compare) or json for cases and compare
  FILE|-                     With run and search, bind the main parameter: the file's bytes
                             when its type is exactly Bytes, else its text, parsed at its sort
  --case FILE                Bind the inputs a case document (.toml or .json) gives by
                             parameter name; its file paths are relative to FILE's directory.
                             A case's run table gives the depth, stop rules, stop count and
                             stop condition, and its observe table the observations, in place
                             of the flags (a flag beside what the case gives is refused); its
                             instances table gives the starting
                             instances of optional and repeated cells; its expect table is
                             checked: met, unmet or inconclusive. --case FILE#NAME names the
                             case NAME of a document of named cases, as krs cases prints its id
  --case-name NAME           With --case, the case of that name in a document of named cases
  CASES...                   With cases, the case documents (.toml or .json) whose cases run,
                             reported in this order: one verdict per case (met, unmet,
                             inconclusive, refused, or ran for a case with no expectation),
                             then a summary
  --jobs N                   With cases and compare --pairs, run the cases or pairs on N
                             workers (default: the available parallelism), each loading its
                             own copy of the definition and of each observer it uses, so
                             memory grows with N; the output is the same for every N but for
                             a verdict a resource stop decides: the simplifier's stack budget,
                             which workers share, or the solver's limits, whose answers a
                             worker's earlier cases may have decided
  --name PATTERN             With cases, only the named cases whose name PATTERN matches
                             (`*` any text, `?` any one character)
  LEFT RIGHT                 With compare, the two sides, each an end document (halt, rule,
                             cells), an observation document (krs-observations/1, as run
                             --output observations prints it) or a case document (.toml or
                             .json), whose case is run for its end and the observations its
                             `observe` declares; FILE#NAME names a case of a document of named
                             cases. The sides are compared on what both state, ends and
                             observations. Prints equal (up to a horizon where a side's
                             observations are open at a bound), the first difference, or
                             inconclusive
  --expect CASE              With compare, check the one side ACTUAL against the expectation of
                             CASE (FILE or FILE#NAME), as run --case checks a run's end, on the
                             cells, views and observer it names: met, unmet or inconclusive
  --pairs FILE               With compare, compare each pair the document FILE (.toml or
                             .json) lists under `pair`: {left, right, compare, views,
                             observer} or {expect, actual}, its side paths relative to FILE's
                             directory; a case side is run once for the whole batch. Prints a
                             verdict per pair, then a summary
  --compare CELL,...         With compare, compare only these cells, by declared path (a group
                             names its leaves); repeatable (default: every leaf cell that is
                             not unobservable)
  --view CELL=FUNCTION       With compare, compare CELL on the value of FUNCTION, a function of
                             one parameter, at its value on each side; repeatable
  --observer PACKAGE:DEFINITION
                             With compare, the definition the views are resolved and evaluated
                             in; with run, the one --stop-when's FUNCTION is: a package that
                             depends on the definition's and that no semantics imports,
                             composed with the --dependency facets its closure holds; a facet
                             outside the definition's closure is the observer's (default: the
                             run or compared definition)
  --view-budget POLLS        With run, search, cases and compare, the polls each evaluation of
                             a view or of a stop condition may take (default: 30000000), a
                             count of its own work that the host's speed and load do not
                             change; one that spends it, or that another stop ends, makes the
                             verdict inconclusive unless a view has no value at another value,
                             which refuses it, and makes a run end stop-undecided
  --input NAME=JSON          Bind input NAME to a JSON document of the typed encoding; file
                             paths are relative to the working directory; repeatable
  -c NAME=TEXT               Bind configuration variable NAME ($ENV, ENV, or init parameter env); repeatable
  --depth N                  At most N rewrite steps
  --stop-before NAME         With run, end before a step by a rule of NAME: a KRS item by
                             its Rust path (`crate::ppu::frame_end`, or `lang::tick` in the
                             dependency crate `lang`), whose every rewrite rule it names, or a
                             K label (exact or unique suffix); repeatable
  --stop-after NAME          With run, end after a step by a rule of NAME; repeatable
  --stop-count N             With run, end at the Nth stop, taking the earlier ones as any
                             other step (default: 1); needs --stop-before or --stop-after
  --stop-when CELL,...=FUNCTION
                             With run, count as a stop only an arrival whose stop state (the
                             state before a --stop-before rule's step, after a --stop-after
                             rule's) FUNCTION, a Bool function of the CELLs in parameter order,
                             holds of; evaluated in --observer's definition; needs
                             --stop-before or --stop-after
  --observe FILE             With run, record the observations FILE (.toml or .json) declares
                             along the run's path: a document whose one key is `observe`, the
                             table a case document gives (point classes sampled before or after
                             the steps of named rules, with a stutter of collapse or count, and
                             logs of List cells, their functions evaluated in its observer); an
                             element with no value refuses the run; printed by --output
                             observations, summarized by --output json
  --trace                    Print each rewrite step with its rule and source
  --coverage                 With run, list the rules and equations the run matched, applied
                             and committed, with their sources (--output json: the report's
                             `coverage`)
  --mode MODE                Search mode (default: final)
  --max-solutions N          Stop search after N solutions
  --spec-module NAME         Prove the claims of this author spec module (default: the generated <MAIN>-SPEC)
  --claim LABEL              Prove only this claim (exact label or unique suffix); repeatable
  --claim-timeout SECONDS    With prove, cancel a claim's proof still running after SECONDS
                             (decimal) of wall-clock time; its verdict is then timeout
  --smt-resource-limit UNITS With run, search, prove, cases and compare, bound each Z3 attempt
                             by Z3 resource units, UNITS for the first and twice the previous
                             for each retry, and by no clock (the default: 370000 units)
  --smt-clock-ms MS          Bound each Z3 attempt by the clock instead, MS milliseconds for the
                             first and twice the previous for each retry; whether a query is
                             decided then depends on the machine's speed and load
  --smt-retries N            Retry an undecided Z3 answer N times (default: 3), as long as the
                             last attempt's doubled bound stays within 4294967295
  --sort SORT                Parse at SORT (default: the sort of the main parameter)
  --color WHEN               Colour pretty output (auto, always, never)
  --timings FILE             Write krs-timings/1 phase timings as JSON
  --counters FILE            Write krs-counters/1 work counters as JSON
  --message-format human|json Diagnostic output (default: human)
  --profile standard|strict  Raw K profile for every package (default: each package's `profile`)
  --no-reuse                 Run the collector and compiler even on an unchanged input
  --partition                With check, print each package's program-syntax partition
  --ir                       With emit-k, also write descriptor-bundle.json, semantic-ir.json,
                             and definition-ir.json
  --stdin                    Format stdin with facade alias k and write the result to stdout
  --edition YEAR             Rust edition for --stdin (default: 2024)
  --check                    Report files that are not canonically formatted
  --trailing-comments STYLE  aligned or gutter (default: aligned)
  -h, --help                 Show this help

Exit status of run, search, prove, cases and compare, by what the caller does next:
  0  yes, rely on the answer: the run or the search completed, the expectation is met, the
     sides are equal, every claim is proven or trusted
  1  no, act on the finding: the expectation is unmet, the sides differ, a claim is disproved
     or failed
  2  the question could not be asked, fix the input or the command: a usage error, a refused
     input, case, expectation, view or definition, or any other error
  3  no answer, retry with more budget or another approach: an inconclusive halt, search or
     verdict, a run with no one path, a claim indeterminate, bounded or timed out
A batch (cases, compare --pairs, or prove of several claims) exits 2 when a case or a pair is
refused or a claim crashed, else 1 when one is a finding, else 3 when one has no answer (in cases, a case with no
expectation whose run has no end included), else 0. A completed run of a definition with an
exit cell exits with that cell's value instead, the program's own status, which shares these
numbers: --output json tells them apart. A run with an expectation (--case) exits by its
verdict instead, 0 met, 1 unmet and 3 inconclusive, and with --output end, a run whose end has
no end document exits 2, whatever its own status. With --output observations, the
observations replace the run's own status: 0 where each element is known, the run's end, a stop
or a depth bound closing or cutting the channels; 3 where an element is undecided or the run
halted inconclusively; an expectation's verdict joins it as a batch's does. krs kink exits by the same four (krs kink
--help). Every other command exits 0 on success, 2 on a usage error and 1 otherwise. A usage
error prints its message, then the usage lines of the command it names (the list of commands
when it names none or an unknown one) and the command that lists the options; an option value
refused for itself prints its message alone.
";

/// `krs kink --help`.
#[cfg(feature = "kink")]
const KINK_USAGE: &str = "\
krs kink: the corpus loop over a KRS package, with kink as its engine

Usage:
  krs kink emit    --package P --definition D [--corpus DIR] [--check]
  krs kink check   --package P --definition D [--corpus DIR] [--mutations PATH] [--cache DIR]
                   [--locked]
  krs kink coverage --package P --definition D [--corpus DIR] [--tier 1|2] [--depth N]
                   [--verify] [--cache DIR] [--output json|text|verdicts] [--locked]
  krs kink run     --package P --definition D [--corpus DIR] [--mutations PATH] [--only ID]...
                   [--verify] [--full] [--lock FILE] [--compile-workers N] [--no-memo]
                   [--progress] [--cache DIR] [--output json|verdicts] [--locked]
  krs kink report  --package P --definition D [--corpus DIR] [--cache DIR]
                   [--output json|verdicts]
  krs kink query   --package P --definition D [--corpus DIR] [--patterns PATH] [--only ID]...
                   [--verify] [--full] [--lock FILE] [--no-explain] [--cache DIR] [--locked]
  krs kink fuzz    --package P --definition D [--corpus DIR] [--templates PATH] --template ID
                   (--kill MUTATION | --matched RULE | --fired RULE | --refuted RULE
                   | --cover ITEM | --pattern ID) [kink-flow's fuzz options] [--locked]
  krs kink compare --package P --definition D [--corpus DIR] [--only NAME]... [--cache DIR]
                   [--output json|text|verdicts] [--locked]
  krs kink prune   --package P --definition D [--corpus DIR] [--mutations PATH] [--patterns PATH]
                   [--full] [--lock FILE] [--compile-workers N] [--progress] [--cache DIR]
                   [--output json|text] [--locked]

The corpus is <package>/kink (or --corpus DIR):
  FLOW.toml         [spec] krs = { package = \"P\", definition = \"D\" }, [budget], and the
                    cases, as kink-flow's manifest: the flow names the definition its files
                    are for, so with --corpus DIR a command needs no --package and no
                    --definition, and one that selects another package or facet is refused
                    before it builds or writes; each case is a [[program]] entry, and kink's
                    documents list the cases under `programs`; a case's paths stay inside
                    the corpus directory, or, where [corpus] root = \"REL\" names the root
                    the cases are under (one tree of cases that the flows of several
                    definitions read, each case with one id in all of them), are relative
                    to that root and stay inside it; [result] cells names cells by Rust path
                    (cpu.regs), as krs compare does; each [[implementation]] is another
                    implementation of the system, which compare runs on every case and
                    compares with the definition under its views; [[patterns]] declares
                    the patterns query and fuzz --pattern ask: files = \"GLOB\" matches
                    kink pattern lists, as [[program]] files matches cases; krs = \"PACKAGE\"
                    names a KRS patterns package (k::patterns!, in a package of the Cargo
                    graph that depends on this one and declares one definition facet),
                    which query and fuzz --pattern build when they ask its patterns
  cases/            the cases' program files and typed-input documents; a program file
                    binds the main parameter, as krs run FILE does
  mutations/        <topic>.toml mutation lists, K patches anchored by `rule = <label or
                    suffix>` (else MUTATIONS.toml)
  PATTERNS.toml     patterns of interest, for query, where FLOW.toml declares no
                    [[patterns]]
  TEMPLATES.toml    case templates with holes, for fuzz
  definition.k      the package's emitted K, which kink judges; written by krs kink
  kink.lock         kink's record of the corpus, one section per command: [run], each
                    mutation's verdict and its one recorded killer, which run tries first
                    and keeps while it still kills, written by krs kink run; [coverage],
                    each family's open obligations, each condition flip's status and its
                    one recorded killer, kept by the same rule, written by krs kink coverage;
                    [compare], each implementation's verdict on each case under each view,
                    written by krs kink compare; [query], each pattern's obligation and its
                    one recorded witness, which query asks first and keeps while it still
                    hits, written by krs kink query; krs kink prune reads it and writes
                    no section
  .kink-flow/       kink-flow's caches, never committed (a .gitignore beside FLOW.toml
                    holding /.kink-flow/ keeps them out)

The loop:
  1. write cases (FLOW.toml, cases/); krs kink coverage --output text until nothing is
     open: it lists each family (rules: every rule in scope fires; requirements: each
     authored operand of a rule's condition seen true and false where reached, the
     condition seen holding and refuted) with covered / obligations, then one target per
     open obligation, named by Rust item and text: a case to write; a rule's status in
     the JSON document is fired, matched (never fired: write a case that takes its step),
     unmatched (write a case that reaches the rule), out-of-scope (a simplification,
     symbolic or ceil equation), claim-helper (the claims serve it: krs prove checks
     them) or no-coverage-signal (a macro or alias); the verdicts rendering lists each
     family's open ids, so it moves only when a gap opens or closes
  2. write mutations (mutations/<topic>.toml); krs kink check until it exits 0
  3. krs kink run; for each survivor write a case that kills it, or argue that no case
     can and drop the mutation, or keep it with the argument in its misunderstanding
     and expect = \"survive\" (its status stays survived, and run fails if a case kills
     it); run again (cached outcomes are not re-run)
  4. commit definition.k and kink.lock with the corpus; CI runs krs kink
     emit --check, krs kink run --locked and krs kink coverage --locked (and krs kink
     compare --locked where FLOW.toml declares an [[implementation]], and krs kink query
     --locked where the corpus has patterns)

A mutation (mutations/<topic>.toml; its id is <topic>/<id>):
  [[mutation]]
  id = \"drops-succ\"
  misunderstanding = \"loses one at every step\"   # required: the mistake it writes down
  expect = \"kill\"                                # optional, \"kill\" or \"survive\": run fails when unmet
    [[mutation.edit]]                            # one or more, applied together
    rule = \"plus_succ\"                           # the label, or a suffix of its -- components;
                                                 # never line =, which moves with every emission
    find = \"s ( plus ( M:Nat , N:Nat ) )\"        # exact text, once in that rule
    replace = \"plus ( M:Nat , N:Nat )\"           # its replacement
    # or, in place of find and replace: delete = true, which removes the rule
check shows each edited rule before and after with its Rust item and line, and refuses an
edit no Rust source emits (a node KRS inserted, a derived test that does not follow the
edit, an overlap KRS refuses) with the next step.
Guide: \"Mutation testing a KRS specification\", /verification/mutation-testing on KRS's
documentation site (docs-site/src/pages/verification/mutation-testing.mdx in k-rust)

Every verb but emit and report builds the package, writes kink/definition.k when it differs
from the emission (the document's `definition.status` says `written`), and runs kink-flow's
verb on it; every rule a document names gains `krs = {item, source_item, package, file,
line, column, kind, claim_helper}`. --locked refuses a stale definition.k instead of writing
it, and emit --check exits 2 when it is stale: the gate a CI runs. run of the corpus's own
mutation list (no --mutations) keeps the [run] section of kink/kink.lock (kink-flow's --lock;
--lock FILE names another): it tries each recorded killer first, keeps it while it still
kills, and rewrites its section after a run of the whole list; under --locked it leaves the
file unwritten and exits 1 when the run would change its section. coverage keeps the
[coverage] section (--lock FILE names another) by the same rule for the condition flips, and
rewrites it after a run with the manifest's own settings (not under --tier 1 or --depth);
under --locked such a run leaves it unwritten and exits 1 when it would change it. compare
keeps the [compare] section (--lock FILE names another), rewritten after a run of every
implementation (not under --only); under --locked it is left unwritten, a verdict that differs
from its row exits 1, and a run of an implementation that gave no answer (it failed, or its
time_ms cancelled it) leaves its rows as recorded, not decided on this host (3). An
implementation that declares identity has its answers cached in .kink-flow/: the same binary,
given the same request, gives the same answer. query of the corpus's own patterns
(FLOW.toml's [[patterns]], else PATTERNS.toml; no --patterns) keeps the [query] section
(--lock FILE names another): each pattern's obligation, open, undecided or hit with its one
recorded witness, which the next query asks first and keeps while it still hits; it is
rewritten after a query of the whole list (not under --only or --verify), and under --locked it
is left unwritten and a query that would change it exits 1.
Each keeps the others' sections as they are. prune reads the corpus's own mutation list and
patterns (a family whose list the layout lacks is skipped; --mutations and --patterns name
others; a report of another list holds for that list, not for the corpus, and says so) and
kink.lock (--lock FILE names another), which it never writes: it runs coverage, the kill search
and the pattern walk, asking a further cell only where a decision needs it (--full: run --full
and query --full, with the same decisions), and reports each case redundant alone, with the
other cases known to discharge what it does, one set of cases removable together, why each other
case is kept, and the kink.lock rows each removal would move; under --locked it refuses a stale
definition.k.
A kink/verdicts.lock or kink/coverage.lock of an earlier kink is read for its killers by the
command that kept it, which moves them into kink.lock and says to delete the old file; under
--locked the command is refused while it is there. report builds nothing: it
prints the last run's stored document (or its verdicts) as that run printed it, exits as
that run did, and takes no --locked. run --progress prints a line on stderr as each phase
starts (the build, the binding, the checks of the list, the specification's admission, the
baseline runner's preparation), as each case's baseline and each mutation is decided (also
without the flag when stderr is a terminal); stdout stays the document.

Exit status, by what the caller does next, as krs run's (krs --help):
  0  yes: every case is comparable and meets its expectation (coverage), every mutation
     got a verdict, killed, survived, equivalent or unkillable (run, report), every pattern
     answered (query), the fuzz found a witness or proved the mutant equivalent, verdicts
     are possible (check), definition.k is fresh (emit), the redundancy report is computed,
     unknowns only keeping cases (prune)
  1  a finding: a --verify mismatch, a kink.lock section --locked would change
     (run, coverage, compare), an unmet expectation (coverage), a refuted pattern claim (query), a
     case excluded on the baseline or a baseline without data (check)
  2  the question could not be asked: a usage error, a package krs refuses, a stale
     definition.k (--locked, emit --check), a refused manifest, specification, case,
     mutation list, lock, mutation, pattern or template, hole values the fuzz mostly
     rejected, a failed run or cache write
  3  no answer: a case or mutation that timed out or is unknown, an inconclusive
     expectation, an unknown pattern answer, a fuzz that ended without a witness kink accepts
A command with several parts exits 2 when one could not be asked, else 1 when one is a
finding, else 3 when one has no answer, else 0.
Under the Z3 solver profile, which krs builds kink with by default, query answers `no`
only where the search received no undecided solver answer, and its cause names that count;
a pair whose search received one is unknown (3), with the count in its cause, and a claim
such a pair does not reach is unconfirmed, not refuted.

The selection options (--manifest-path, --package, --package-id, --definition,
--dependency, --cfg, --profile, --message-format, --timings, --counters, and --registration,
build tooling krs --help does not list), --corpus and --locked are krs's, before or after
the verb, and so are the list flags of the Usage lines that name a kink-flow operand (run
--mutations, query --patterns, fuzz --templates); every other option is the kink-flow
verb's own. krs kink VERB --help lists the verb's options, kink-flow's included. A usage
error prints its message, the verb's usage line and where its options are listed. Every
command that builds the package builds it in process, so krs kink takes no --no-reuse.
";

/// Each verb of `krs kink` with its usage line, as [`KINK_USAGE`] lists it.
#[cfg(feature = "kink")]
const KINK_VERB_USAGE: [(&str, &str); 9] = [
    (
        "emit",
        "krs kink emit --package P --definition D [--corpus DIR] [--check]",
    ),
    (
        "check",
        "krs kink check --package P --definition D [--corpus DIR] [--mutations PATH] [--cache \
         DIR] [--locked]",
    ),
    (
        "coverage",
        "krs kink coverage --package P --definition D [--corpus DIR] [--tier 1|2] [--depth N] [--verify] \
         [--cache DIR] [--output json|text|verdicts] [--locked]",
    ),
    (
        "run",
        "krs kink run --package P --definition D [--corpus DIR] [--mutations PATH] [--only ID]... \
         [--verify] [--full] [--lock FILE] [--compile-workers N] [--no-memo] [--progress] \
         [--cache DIR] [--output json|verdicts] [--locked]",
    ),
    (
        "report",
        "krs kink report --package P --definition D [--corpus DIR] [--cache DIR] [--output \
         json|verdicts]",
    ),
    (
        "query",
        "krs kink query --package P --definition D [--corpus DIR] [--patterns PATH] [--only ID]... \
         [--verify] [--full] [--lock FILE] [--no-explain] [--cache DIR] [--locked]",
    ),
    (
        "fuzz",
        "krs kink fuzz --package P --definition D [--corpus DIR] [--templates PATH] --template ID \
         (--kill MUTATION | --matched RULE | --fired RULE | --refuted RULE | --cover ITEM | \
         --pattern ID) [kink-flow's fuzz options] [--locked]",
    ),
    (
        "compare",
        "krs kink compare --package P --definition D [--corpus DIR] [--only NAME]... [--cache \
         DIR] [--output json|text|verdicts] [--locked]",
    ),
    (
        "prune",
        "krs kink prune --package P --definition D [--corpus DIR] [--mutations PATH] [--patterns \
         PATH] [--full] [--lock FILE] [--compile-workers N] [--progress] [--cache DIR] [--output \
         json|text] [--locked]",
    ),
];

/// What a usage error prints after its message: `usage`, the shape of the command line the
/// error is corrected against, and `pointer`, where the rest is explained. The whole help would
/// bury the message; the usage line is what a misspelt option, a missing operand or a bad value
/// is corrected against.
fn usage_tail(usage: &str, pointer: &str) -> String {
    format!("usage: {usage}\n{pointer}")
}

/// The entries of [`USAGE`]'s `Usage:` block, each a command line's shape with its
/// continuation lines.
fn usage_entries() -> Vec<Vec<&'static str>> {
    let mut entries: Vec<Vec<&str>> = Vec::new();
    for line in USAGE
        .lines()
        .skip_while(|line| *line != "Usage:")
        .skip(1)
        .take_while(|line| !line.is_empty())
    {
        match entries.last_mut() {
            Some(entry) if !line.starts_with("  krs ") => entry.push(line),
            _ => entries.push(vec![line]),
        }
    }
    entries
}

/// The commands an entry of [`USAGE`]'s `Usage:` block is the shape of: `krs <check|build> ..`
/// is the shape of each command it lists, `krs run ..` of `run`.
fn entry_commands(entry: &[&'static str]) -> Vec<&'static str> {
    let word = entry[0]
        .trim_start()
        .strip_prefix("krs ")
        .and_then(|rest| rest.split_whitespace().next())
        .unwrap_or_default();
    match word
        .strip_prefix('<')
        .and_then(|word| word.strip_suffix('>'))
    {
        Some(commands) => commands.split('|').collect(),
        None => vec![word],
    }
}

/// What a usage error of `krs COMMAND` prints after its message: every shape of COMMAND's
/// command line that [`USAGE`] lists, aligned as there, and where its options are explained.
/// A command line that names no command is shown every command this krs runs: `kink` only in a
/// build with the `kink` feature.
fn command_usage_tail(command: Option<&str>) -> String {
    let entries = usage_entries();
    let shapes = command.map_or_else(Vec::new, |command| {
        entries
            .iter()
            .filter(|entry| entry_commands(entry).contains(&command))
            .collect::<Vec<_>>()
    });
    if shapes.is_empty() {
        let mut commands = Vec::new();
        for entry in &entries {
            for command in entry_commands(entry) {
                if command == "kink" && !cfg!(feature = "kink") {
                    continue;
                }
                if !commands.contains(&command) {
                    commands.push(command);
                }
            }
        }
        return usage_tail(
            &format!(
                "krs COMMAND [OPTIONS], COMMAND one of {}",
                commands.join(", ")
            ),
            "`krs --help` lists every command and its options",
        );
    }
    // `usage: ` takes the place of the entries' two-space indent, five columns more.
    let mut usage = String::new();
    for (index, entry) in shapes.iter().enumerate() {
        for (line_index, line) in entry.iter().enumerate() {
            if line_index == 0 {
                if index > 0 {
                    usage.push_str("\n       ");
                }
                usage.push_str(&line[2..]);
            } else {
                usage.push_str("\n     ");
                usage.push_str(line);
            }
        }
    }
    usage_tail(
        &usage,
        "`krs --help` lists every command's options and what each means",
    )
}

/// The usage line of `krs kink VERB`.
#[cfg(feature = "kink")]
fn kink_verb_usage(verb: &str) -> Option<&'static str> {
    KINK_VERB_USAGE
        .iter()
        .find(|(name, _)| *name == verb)
        .map(|(_, usage)| *usage)
}

/// What a `krs kink` usage error prints after its message ([`usage_tail`]): the usage line of
/// the verb the command line names (every command line's shape when it names none) and where
/// the rest is.
#[cfg(feature = "kink")]
fn kink_usage_tail(verb: Option<&str>) -> String {
    match verb.and_then(|verb| kink_verb_usage(verb).map(|usage| (verb, usage))) {
        Some((verb, usage)) => usage_tail(
            usage,
            &format!(
                "`krs kink {verb} --help` lists its options; `krs kink --help` explains the \
                 corpus loop"
            ),
        ),
        None => usage_tail(
            &format!(
                "krs kink VERB --package P --definition D [--corpus DIR] [OPTIONS], VERB one of \
                 emit, {}",
                kink_verbs()
            ),
            "`krs kink --help` explains the corpus loop; `krs kink VERB --help` lists a verb's \
             options",
        ),
    }
}

/// The lists `krs kink prune` reads, each a layout's file by default, which its help lists.
#[cfg(feature = "kink")]
const KINK_PRUNE_LISTS: [kink_flow::cli::VerbOption; 2] = [
    kink_flow::cli::VerbOption {
        spelling: "--mutations PATH",
        meaning: "the mutation list (default: the corpus's mutations/, else its MUTATIONS.toml; \
                  without either the mutations are skipped)",
    },
    kink_flow::cli::VerbOption {
        spelling: "--patterns PATH",
        meaning: "the pattern list, in place of the patterns FLOW.toml declares (default: those, \
                  else the corpus's PATTERNS.toml; without either the patterns are skipped)",
    },
];

/// `krs kink VERB --help`: what the verb does, its usage line, krs's options and, for a
/// kink-flow verb, kink-flow's options of the verb, which `krs kink` passes on.
#[cfg(feature = "kink")]
fn kink_verb_help(verb: &str) -> String {
    use std::fmt::Write as _;
    let Some(usage) = kink_verb_usage(verb) else {
        return KINK_USAGE.to_owned();
    };
    let flow = kink_flow::Verb::parse(verb);
    let summary = flow.map_or(
        "Write kink/definition.k, the package's emitted K, which kink judges, when it is not the \
         package's current emission; with --check, write nothing and say whether it is.",
        kink_flow::Verb::summary,
    );
    let option = |spelling, meaning| kink_flow::cli::VerbOption { spelling, meaning };
    let mut own = vec![option(
        "--corpus DIR",
        "the corpus directory (default: kink/ beside the package's Cargo.toml)",
    )];
    let layout_mutations = "the mutation list (default: the corpus's mutations/, else its \
                            MUTATIONS.toml)";
    match verb {
        "emit" => own.push(option(
            "--check",
            "write nothing, and exit 2 when definition.k is not the package's current emission",
        )),
        "report" => {}
        "coverage" => own.push(option(
            "--locked",
            "refuse a stale kink/definition.k instead of writing it, and leave kink.lock \
             unwritten, exiting 1 when the [coverage] section of a run with the manifest's \
             settings would differ",
        )),
        "run" => own.push(option(
            "--locked",
            "refuse a stale kink/definition.k instead of writing it, and leave kink.lock \
             unwritten, exiting 1 when the run's [run] section would differ",
        )),
        "compare" => own.push(option(
            "--locked",
            "refuse a stale kink/definition.k instead of writing it, and leave kink.lock \
             unwritten, exiting 1 when the run's [compare] section would differ",
        )),
        _ => own.push(option(
            "--locked",
            "refuse a stale kink/definition.k instead of writing it",
        )),
    }
    match flow {
        Some(kink_flow::Verb::Run) => own.push(option("--mutations PATH", layout_mutations)),
        Some(kink_flow::Verb::Query) => own.push(option(
            "--patterns PATH",
            "the pattern list, in place of the patterns FLOW.toml declares (default: those, else \
             the corpus's PATTERNS.toml)",
        )),
        Some(kink_flow::Verb::Fuzz) => own.push(option(
            "--templates PATH",
            "the template list (default: the corpus's TEMPLATES.toml)",
        )),
        Some(kink_flow::Verb::Prune) => own.extend_from_slice(&KINK_PRUNE_LISTS),
        _ => {}
    }
    let mut text = format!(
        "krs kink {verb}: {summary}\n\nusage: {usage}\n\nkrs's options, before or after the verb: \
         the selection options (--manifest-path, --package, --package-id, --definition, \
         --dependency, --cfg, --profile, --message-format, --timings, --counters, and the build \
         tooling's --registration), and\n{}",
        kink_flow::cli::options_text(&own)
    );
    if let Some(flow) = flow {
        let _ = write!(
            text,
            "\nkink-flow's {} options, which krs kink passes on:\n{}",
            flow.as_str(),
            kink_flow::cli::options_text(flow.options())
        );
        if matches!(flow, kink_flow::Verb::Check | kink_flow::Verb::Fuzz) {
            let _ = writeln!(
                text,
                "  (--mutations defaults to the corpus's mutations/, else its MUTATIONS.toml, \
                 when it exists)"
            );
        }
        if flow == kink_flow::Verb::Fuzz {
            let _ = writeln!(
                text,
                "  (--patterns defaults to the patterns FLOW.toml declares, else the corpus's \
                 PATTERNS.toml, when it exists)"
            );
        }
    }
    text.push_str(
        "\n`krs kink --help` explains the corpus layout, the loop and the exit statuses.\n",
    );
    text
}

fn main() {
    let arguments: Vec<OsString> = std::env::args_os().skip(1).collect();
    match parse(arguments.clone()) {
        Ok(ParseResult::Help) => print!("{USAGE}"),
        Ok(ParseResult::Format(request)) => match execute_format(&request) {
            Ok(true) => {}
            Ok(false) => std::process::exit(1),
            Err(error) => {
                eprintln!("krs fmt: {error}");
                std::process::exit(1);
            }
        },
        #[cfg(feature = "kink")]
        Ok(ParseResult::KinkHelp(None)) => print!("{KINK_USAGE}"),
        #[cfg(feature = "kink")]
        Ok(ParseResult::KinkHelp(Some(verb))) => print!("{}", kink_verb_help(&verb)),
        #[cfg(feature = "kink")]
        Ok(ParseResult::Kink(request, measure)) => {
            let status = execute_kink(&request, &measure);
            if status != 0 {
                std::process::exit(status);
            }
        }
        // `krs prove` proves its claims in supervised worker processes, which do the measuring.
        Ok(ParseResult::Run(request, _)) if matches!(&request.command, Command::Prove(prove) if !prove.worker) =>
        {
            let Command::Prove(prove) = &request.command else {
                unreachable!("the guard matched a prove command")
            };
            let status = executing(|| supervise_prove(&arguments, prove));
            if status != 0 {
                std::process::exit(status);
            }
        }
        Ok(ParseResult::Run(request, measure)) => {
            let worker = matches!(&request.command, Command::Prove(prove) if prove.worker);
            if worker {
                krs_cli::watch_supervisor();
            }
            let kind = request.command.kind();
            let run = || {
                let mut measurement =
                    Measurement::new(measure.timings.is_some(), measure.counters.is_some());
                let (result, sources) = execute_command_reported(&request, &mut measurement);
                let measured =
                    write_measurement(&measure, &measurement, kind.as_str(), result.is_ok());
                let status = report_outcome(result, kind, request.message_format, &sources);
                match (kind.executes(), measured) {
                    // An executing command's unwritten measurement is an error beside its answer.
                    (true, false) => exit_status::join(status, kind.failure_status(None)),
                    (false, false) if status == 0 => kind.failure_status(None),
                    _ => status,
                }
            };
            // A worker of a supervising `krs prove` that panics ends with the panic's status,
            // which its supervisor records as a crash.
            let status = if kind.executes() && !worker {
                executing(run)
            } else {
                run()
            };
            if status != 0 {
                std::process::exit(status);
            }
        }
        #[cfg(feature = "kink")]
        Err(UsageError::Kink(message, verb)) => {
            eprintln!("krs kink: {message}\n{}", kink_usage_tail(verb.as_deref()));
            std::process::exit(2);
        }
        Err(UsageError::Value(message)) => {
            eprintln!("krs: {message}");
            std::process::exit(2);
        }
        Err(error) => {
            eprintln!("krs: {error}\n{}", command_usage_tail(error.command()));
            std::process::exit(2);
        }
    }
}

/// Run `body`, an executing command's work in this process, and return its exit status: a panic,
/// which the panic hook has reported, is an error, so the question was not asked
/// ([`exit_status::UNASKED`]). In a debug build, `KRS_TEST_PANIC` set makes the work panic first,
/// for the tests.
fn executing(body: impl FnOnce() -> i32) -> i32 {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        #[cfg(debug_assertions)]
        assert!(
            std::env::var_os("KRS_TEST_PANIC").is_none(),
            "the test hook panics before the command runs"
        );
        body()
    }))
    .unwrap_or(exit_status::UNASKED)
}

/// Run `krs kink`: krs's warnings and refusal on stderr, then the document on stdout, then the
/// command's notes on stderr; returns the exit status.
#[cfg(feature = "kink")]
fn execute_kink(request: &krs_cli::KinkRequest, measure: &MeasureOptions) -> i32 {
    let mut measurement = Measurement::new(measure.timings.is_some(), measure.counters.is_some());
    let outcome = krs_cli::execute_kink(request, &mut measurement);
    let measured = write_measurement(measure, &measurement, "kink", outcome.status == 0);
    report_diagnostics(
        &outcome.warnings.envelopes,
        request.message_format,
        &outcome.sources,
    );
    if let Some(error) = &outcome.error {
        report_error(error, request.message_format, &outcome.sources);
    }
    if let Err(error) = io::stdout().lock().write_all(&outcome.stdout) {
        eprintln!("krs: could not write stdout: {error}");
        return exit_status::UNASKED;
    }
    let _ = io::stdout().lock().flush();
    for note in &outcome.notes {
        eprintln!("{note}");
    }
    if outcome.usage {
        let verb = match &request.verb {
            krs_cli::KinkVerb::Emit { .. } => "emit",
            krs_cli::KinkVerb::Flow { verb, .. } => verb.as_str(),
        };
        eprintln!("{}", kink_usage_tail(Some(verb)));
    }
    let status = i32::from(outcome.status);
    // An unwritten measurement is an error beside the command's answer.
    if measured {
        status
    } else {
        exit_status::join(status, exit_status::UNASKED)
    }
}

/// Measurement output paths requested on the command line.
#[derive(Default)]
struct MeasureOptions {
    timings: Option<PathBuf>,
    counters: Option<PathBuf>,
}

fn write_measurement(
    options: &MeasureOptions,
    measurement: &Measurement,
    command: &str,
    succeeded: bool,
) -> bool {
    let mut ok = true;
    let mut write = |path: &Path, bytes: serde_json::Result<Vec<u8>>| {
        let result = bytes
            .map_err(|error| error.to_string())
            .and_then(|mut bytes| {
                bytes.push(b'\n');
                std::fs::write(path, bytes).map_err(|error| error.to_string())
            });
        if let Err(error) = result {
            eprintln!("krs: could not write `{}`: {error}", path.display());
            ok = false;
        }
    };
    if let Some(path) = &options.timings {
        let document = measurement.timings.document(command, succeeded);
        write(path, serde_json::to_vec_pretty(&document));
    }
    if let Some(path) = &options.counters {
        let document = measurement.counters.document(command, succeeded);
        write(path, serde_json::to_vec_pretty(&document));
    }
    ok
}

/// Print a command outcome of a command of `kind` and return the process exit status.
///
/// A success exits with the outcome's status; a failure, or a failure to write the outcome,
/// exits with the status [`CommandKind::failure_status`] gives.
fn report_outcome(
    result: Result<krs_cli::CommandOutcome, krs_cli::CommandError>,
    kind: CommandKind,
    format: MessageFormat,
    sources: &DiagnosticSources,
) -> i32 {
    match result {
        Ok(outcome) => {
            report_diagnostics(&outcome.warnings().envelopes, format, sources);
            if let Err(error) = io::stdout().lock().write_all(outcome.stdout()) {
                eprintln!("krs: could not write stdout: {error}");
                return kind.failure_status(None);
            }
            let _ = io::stdout().lock().flush();
            if let Err(error) = io::stderr().lock().write_all(outcome.stderr()) {
                eprintln!("krs: could not write stderr: {error}");
                return kind.failure_status(None);
            }
            outcome.exit_code()
        }
        Err(error) => {
            report_error(&error, format, sources);
            kind.failure_status(Some(&error))
        }
    }
}

/// Print a command's refusal: the warnings of the stages that completed first, as on success;
/// the error is the verdict and comes last.
fn report_error(error: &krs_cli::CommandError, format: MessageFormat, sources: &DiagnosticSources) {
    if let Some(warnings) = error.warnings() {
        report_diagnostics(&warnings.envelopes, format, sources);
    }
    if let Some(diagnostics) = error.diagnostics() {
        report_diagnostics(&diagnostics, format, sources);
    } else {
        eprintln!("krs: {error}");
    }
}

fn report_diagnostics(
    envelopes: &[krs_cli::DiagnosticEnvelope],
    format: MessageFormat,
    sources: &DiagnosticSources,
) {
    let color = io::stderr().is_terminal() && std::env::var_os("NO_COLOR").is_none();
    if let Err(error) =
        write_diagnostics(&mut io::stderr().lock(), envelopes, format, sources, color)
    {
        eprintln!("krs: could not render diagnostic: {error}");
    }
}

/// Writes `envelopes`, the located ones first, each group in producer order.
fn write_diagnostics(
    writer: &mut impl Write,
    envelopes: &[krs_cli::DiagnosticEnvelope],
    format: MessageFormat,
    sources: &DiagnosticSources,
    color: bool,
) -> io::Result<()> {
    let (located, unlocated): (Vec<_>, Vec<_>) = envelopes
        .iter()
        .partition(|envelope| envelope.authored_range.is_some());
    for diagnostic in located.into_iter().chain(unlocated) {
        match format {
            MessageFormat::Json => writer.write_all(diagnostic.to_json_line()?.as_bytes())?,
            MessageFormat::Human => {
                writeln!(writer, "{}", sources.render_envelope(diagnostic, color))?;
            }
        }
    }
    Ok(())
}

enum ParseResult {
    Help,
    Format(FormatRequest),
    Run(Box<CommandRequest>, MeasureOptions),
    /// `krs kink --help`, or `krs kink VERB --help` (the verb's help).
    #[cfg(feature = "kink")]
    KinkHelp(Option<String>),
    #[cfg(feature = "kink")]
    Kink(Box<krs_cli::KinkRequest>, MeasureOptions),
}

struct FormatRequest {
    stdin: bool,
    edition: Edition,
    check: bool,
    manifest_path: Option<PathBuf>,
    paths: Vec<PathBuf>,
    trailing_comments: TrailingCommentStyle,
}

/// Options of the run-family commands (`parse`, `run`, `search`, `prove`), with the spelling of each given option.
#[derive(Default)]
struct ExecOptions {
    given: Vec<&'static str>,
    inputs: Vec<OsString>,
    case: Option<PathBuf>,
    /// The case `--case FILE#NAME` names by its id.
    case_id_name: Option<String>,
    case_name: Option<String>,
    typed: Vec<(String, String)>,
    variables: Vec<(String, String)>,
    depth: Option<u64>,
    stop: StopRules,
    stop_count: Option<NonZeroU64>,
    /// `--stop-when`: the cells and the function.
    stop_when: Option<(Vec<String>, String)>,
    /// `--observe`.
    observe: Option<PathBuf>,
    trace: bool,
    coverage: bool,
    mode: Option<SearchMode>,
    max_solutions: Option<usize>,
    claims: Vec<String>,
    /// `--worker-protocol` (hidden): prove for a supervising `krs prove`.
    worker: bool,
    /// `--worker-claim` (hidden): the claims a worker proves, exactly, instead of `--claim`'s.
    worker_claims: Vec<String>,
    /// `--worker-color` (hidden): whether a worker colours, as its supervisor resolved `--color`.
    worker_color: Option<ColorChoice>,
    spec_module: Option<String>,
    sort: Option<String>,
    color: Option<ColorChoice>,
    /// `--smt-resource-limit`.
    smt_resource_limit: Option<std::num::NonZeroU32>,
    /// `--smt-clock-ms`.
    smt_clock_ms: Option<u32>,
    /// `--smt-retries`.
    smt_retries: Option<u32>,
    /// `--claim-timeout`.
    claim_timeout: Option<std::time::Duration>,
    /// `--jobs`.
    jobs: Option<std::num::NonZeroUsize>,
    /// `--name`.
    name: Option<String>,
    /// `--view-budget`.
    view_budget: Option<u64>,
    /// `--expect`.
    expect: Option<String>,
    /// `--compare`, its cells in command-line order.
    compare: Option<Vec<String>>,
    /// `--view`, by cell.
    views: std::collections::BTreeMap<String, String>,
    /// `--observer`.
    observer: Option<String>,
    /// `--pairs`.
    pairs: Option<PathBuf>,
}

impl ExecOptions {
    fn note(&mut self, option: &'static str) {
        if !self.given.contains(&option) {
            self.given.push(option);
        }
    }
}

#[derive(Default)]
struct RunOptions {
    exec: ExecOptions,
    manifest_path: Option<PathBuf>,
    package: Option<String>,
    package_id: Option<String>,
    definition: Option<String>,
    dependencies: Vec<FacetSelector>,
    cfg: Vec<KrsCfg>,
    backend: Option<Backend>,
    output: Option<PathBuf>,
    registration: Option<RegistrationMode>,
    no_reuse: bool,
    message_format: Option<MessageFormat>,
    measure: MeasureOptions,
    partition: bool,
    ir: bool,
    profile: Option<krs_ir::RawKProfile>,
}

#[derive(Debug)]
enum UsageError {
    Argument(lexopt::Error),
    Message(String),
    /// A value that is refused for itself (a `--case` that names no case file), which the usage
    /// would not help to correct: printed without it.
    Value(String),
    /// A usage error of `krs kink`, shown with the usage of the verb it names, if it names one.
    #[cfg(feature = "kink")]
    Kink(String, Option<String>),
    /// A usage error of the command named, shown with that command's usage.
    Command(&'static str, Box<UsageError>),
}

impl UsageError {
    /// This error as one of `command`'s, if the usage helps to correct it.
    fn of(self, command: &'static str) -> Self {
        match self {
            Self::Argument(_) | Self::Message(_) => Self::Command(command, Box::new(self)),
            other => other,
        }
    }

    /// The command whose usage error this is, if the command line named one.
    fn command(&self) -> Option<&'static str> {
        match self {
            Self::Command(command, _) => Some(command),
            _ => None,
        }
    }
}

impl fmt::Display for UsageError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Argument(error) => error.fmt(formatter),
            Self::Message(message) | Self::Value(message) => message.fmt(formatter),
            #[cfg(feature = "kink")]
            Self::Kink(message, _) => message.fmt(formatter),
            Self::Command(_, error) => error.fmt(formatter),
        }
    }
}

impl From<lexopt::Error> for UsageError {
    fn from(error: lexopt::Error) -> Self {
        Self::Argument(error)
    }
}

fn usage(message: impl Into<String>) -> UsageError {
    UsageError::Message(message.into())
}

fn set_once<T>(slot: &mut Option<T>, value: T, option: &str) -> Result<(), UsageError> {
    if slot.replace(value).is_some() {
        return Err(usage(format!("{option} specified more than once")));
    }
    Ok(())
}

fn option_value(parser: &mut lexopt::Parser, role: &str) -> Result<String, UsageError> {
    utf8(parser.value()?, role)
}

fn parse(arguments: Vec<OsString>) -> Result<ParseResult, UsageError> {
    let mut parser = lexopt::Parser::from_args(arguments);
    let command = match parser.next()? {
        Some(Short('h') | Long("help")) => return Ok(ParseResult::Help),
        Some(Value(value)) => utf8(value, "command")?,
        Some(argument) => return Err(argument.unexpected().into()),
        None => return Err(usage("missing command")),
    };
    if command == "fmt" {
        return parse_format(&mut parser).map_err(|error| error.of("fmt"));
    }
    if command == "kink" {
        #[cfg(feature = "kink")]
        return parse_kink(parser.raw_args()?.collect());
        #[cfg(not(feature = "kink"))]
        return Err(usage(
            "this krs was built without the `kink` feature, which `krs kink` needs",
        ));
    }
    let kind = match command.as_str() {
        "check" => CommandKind::Check,
        "expand" => CommandKind::Expand,
        "emit-k" => CommandKind::EmitK,
        "build" => CommandKind::Build,
        "parse" => CommandKind::Parse,
        "run" => CommandKind::Run,
        "search" => CommandKind::Search,
        "prove" => CommandKind::Prove,
        "cases" => CommandKind::Cases,
        "compare" => CommandKind::Compare,
        unknown => return Err(usage(format!("unknown command `{unknown}`"))),
    };
    parse_run(&mut parser, kind).map_err(|error| error.of(kind.as_str()))
}

fn parse_run(parser: &mut lexopt::Parser, kind: CommandKind) -> Result<ParseResult, UsageError> {
    let mut options = RunOptions::default();
    while let Some(argument) = parser.next()? {
        match argument {
            Short('h') | Long("help") => return Ok(ParseResult::Help),
            Long("no-reuse") => options.no_reuse = true,
            Long("partition") if kind == CommandKind::Check => options.partition = true,
            Long("ir") if kind == CommandKind::EmitK => options.ir = true,
            Long("profile") => {
                let value = option_value(parser, "profile")?;
                let selected = krs_ir::RawKProfile::from_metadata(&value).ok_or_else(|| {
                    usage(format!(
                        "unknown profile `{value}`; expected standard or strict"
                    ))
                })?;
                set_once(&mut options.profile, selected, "--profile")?;
            }
            Long("message-format") => {
                let value = option_value(parser, "message format")?;
                let selected = match value.as_str() {
                    "human" => MessageFormat::Human,
                    "json" => MessageFormat::Json,
                    _ => return Err(usage(format!("unknown message format `{value}`"))),
                };
                set_once(&mut options.message_format, selected, "--message-format")?;
            }
            Long("manifest-path") => set_once(
                &mut options.manifest_path,
                PathBuf::from(option_value(parser, "manifest path")?),
                "--manifest-path",
            )?,
            Long("package") => set_once(
                &mut options.package,
                option_value(parser, "package")?,
                "--package",
            )?,
            Long("package-id") => set_once(
                &mut options.package_id,
                option_value(parser, "package ID")?,
                "--package-id",
            )?,
            Long("definition") => set_once(
                &mut options.definition,
                option_value(parser, "definition")?,
                "--definition",
            )?,
            Long("dependency") => options
                .dependencies
                .push(parse_dependency(parser.value()?)?),
            Long("cfg") => options.cfg.push(parse_cfg(parser.value()?)?),
            Long("backend") => {
                let value = option_value(parser, "backend")?;
                let selected = Backend::ALL
                    .into_iter()
                    .find(|backend| backend.as_str() == value)
                    .ok_or_else(|| usage(format!("unknown backend `{value}`")))?;
                set_once(&mut options.backend, selected, "--backend")?;
            }
            Long("output") => set_once(
                &mut options.output,
                PathBuf::from(option_value(parser, "output")?),
                "--output",
            )?,
            Long("timings") => set_once(
                &mut options.measure.timings,
                PathBuf::from(option_value(parser, "timings")?),
                "--timings",
            )?,
            Long("counters") => set_once(
                &mut options.measure.counters,
                PathBuf::from(option_value(parser, "counters")?),
                "--counters",
            )?,
            Long("registration") => {
                let value = option_value(parser, "registration")?;
                let selected = match value.as_str() {
                    "inventory" => RegistrationMode::Inventory,
                    "explicit" => RegistrationMode::Explicit,
                    _ => return Err(usage(format!("unknown registration mode `{value}`"))),
                };
                set_once(&mut options.registration, selected, "--registration")?;
            }
            Short('c') => exec_option(parser, &mut options.exec, "-c")?,
            Long(name) if EXEC_LONG_OPTIONS.contains(&name) => {
                let option = EXEC_LONG_OPTIONS
                    .iter()
                    .find(|option| **option == name)
                    .copied()
                    .expect("guard matched a run option");
                exec_option(parser, &mut options.exec, option)?;
            }
            Value(value) => {
                options.exec.note("FILE");
                options.exec.inputs.push(value);
            }
            _ => return Err(argument.unexpected().into()),
        }
    }
    finish_run(kind, options)
}

/// The options between a supervising `krs prove` and its workers, which the usage does not show.
#[cfg(test)]
const HIDDEN_OPTIONS: [&str; 3] = ["--worker-protocol", "--worker-claim", "--worker-color"];

/// Long options of the run-family commands, without their leading dashes.
const EXEC_LONG_OPTIONS: [&str; 32] = [
    "case",
    "case-name",
    "jobs",
    "name",
    "view-budget",
    "expect",
    "compare",
    "view",
    "observer",
    "pairs",
    "input",
    "depth",
    "stop-before",
    "stop-after",
    "stop-count",
    "stop-when",
    "observe",
    "max-solutions",
    "mode",
    "trace",
    "coverage",
    "claim",
    "spec-module",
    "sort",
    "color",
    "smt-resource-limit",
    "smt-clock-ms",
    "smt-retries",
    "claim-timeout",
    "worker-protocol",
    "worker-claim",
    "worker-color",
];

/// The options of `krs compare` alone, which [`compare_option`] parses.
const COMPARE_OPTIONS: [&str; 5] = ["expect", "compare", "view", "observer", "pairs"];

/// Parse one run-family option (`-c` or a member of [`EXEC_LONG_OPTIONS`]).
fn exec_option(
    parser: &mut lexopt::Parser,
    exec: &mut ExecOptions,
    option: &'static str,
) -> Result<(), UsageError> {
    match option {
        "-c" => {
            exec.note("-c");
            let value = option_value(parser, "configuration variable")?;
            let (name, text) = value
                .split_once('=')
                .ok_or_else(|| usage(format!("-c `{value}` must have the form NAME=TEXT")))?;
            if name.trim_start_matches('$').is_empty() {
                return Err(usage(format!("-c `{value}` has an empty variable name")));
            }
            exec.variables.push((name.to_owned(), text.to_owned()));
        }
        "case" => {
            exec.note("--case");
            let (path, name) = case_path(&option_value(parser, "case file")?)?;
            set_once(&mut exec.case, path, "--case")?;
            exec.case_id_name = name;
        }
        "case-name" => {
            exec.note("--case-name");
            let name = option_value(parser, "case name")?;
            set_once(&mut exec.case_name, name, "--case-name")?;
        }
        "input" => {
            exec.note("--input");
            exec.typed
                .push(typed_input(&option_value(parser, "input")?)?);
        }
        "depth" | "observe" => path_option(parser, exec, option)?,
        option if option.starts_with("stop-") => stop_option(parser, exec, option)?,
        "jobs" | "name" | "view-budget" => cases_option(parser, exec, option)?,
        option if COMPARE_OPTIONS.contains(&option) => compare_option(parser, exec, option)?,
        "max-solutions" => {
            exec.note("--max-solutions");
            let value = option_value(parser, "maximum solution count")?;
            let limit = value.parse::<usize>().map_err(|_| {
                usage(format!(
                    "--max-solutions `{value}` is not a non-negative integer"
                ))
            })?;
            set_once(&mut exec.max_solutions, limit, "--max-solutions")?;
        }
        "mode" => {
            exec.note("--mode");
            let value = option_value(parser, "search mode")?;
            let mode = SearchMode::ALL
                .into_iter()
                .find(|mode| mode.as_str() == value)
                .ok_or_else(|| usage(format!("unknown search mode `{value}`")))?;
            set_once(&mut exec.mode, mode, "--mode")?;
        }
        "trace" => {
            exec.note("--trace");
            exec.trace = true;
        }
        "coverage" => {
            exec.note("--coverage");
            exec.coverage = true;
        }
        "claim" => {
            exec.note("--claim");
            exec.claims.push(option_value(parser, "claim label")?);
        }
        "worker-protocol" | "worker-claim" | "worker-color" => {
            worker_option(parser, exec, option)?;
        }
        "smt-resource-limit" | "smt-clock-ms" | "smt-retries" | "claim-timeout" => {
            solver_option(parser, exec, option)?;
        }
        "spec-module" => {
            exec.note("--spec-module");
            let module = option_value(parser, "spec module")?;
            set_once(&mut exec.spec_module, module, "--spec-module")?;
        }
        "sort" => {
            exec.note("--sort");
            let sort = option_value(parser, "sort")?;
            set_once(&mut exec.sort, sort, "--sort")?;
        }
        "color" => {
            exec.note("--color");
            let value = option_value(parser, "color")?;
            let color = match value.as_str() {
                "auto" => ColorChoice::Auto,
                "always" => ColorChoice::Always,
                "never" => ColorChoice::Never,
                _ => return Err(usage(format!("unknown color choice `{value}`"))),
            };
            set_once(&mut exec.color, color, "--color")?;
        }
        _ => unreachable!("exec_option is called only for run options"),
    }
    Ok(())
}

/// Parse `--jobs`, `--name` or `--view-budget`.
fn cases_option(
    parser: &mut lexopt::Parser,
    exec: &mut ExecOptions,
    option: &'static str,
) -> Result<(), UsageError> {
    match option {
        "jobs" => {
            exec.note("--jobs");
            let value = option_value(parser, "worker count")?;
            let jobs = value
                .parse::<std::num::NonZeroUsize>()
                .map_err(|_| usage(format!("--jobs `{value}` is not a positive integer")))?;
            set_once(&mut exec.jobs, jobs, "--jobs")?;
        }
        "name" => {
            exec.note("--name");
            let pattern = option_value(parser, "name pattern")?;
            if pattern.is_empty() {
                return Err(usage(
                    "--name needs a pattern; a case's name is never empty",
                ));
            }
            set_once(&mut exec.name, pattern, "--name")?;
        }
        "view-budget" => {
            exec.note("--view-budget");
            let value = option_value(parser, "polls")?;
            // A budget of no polls would stop every view at its first poll, which is not the
            // positive bound the option promises.
            let budget = value
                .parse::<std::num::NonZeroU64>()
                .map_err(|_| usage(format!("--view-budget `{value}` is not a positive integer")))?;
            set_once(&mut exec.view_budget, budget.get(), "--view-budget")?;
        }
        _ => unreachable!("cases_option is called only for --jobs, --name and --view-budget"),
    }
    Ok(())
}

/// Parse `--expect`, `--compare`, `--view`, `--observer` or `--pairs`.
fn compare_option(
    parser: &mut lexopt::Parser,
    exec: &mut ExecOptions,
    option: &'static str,
) -> Result<(), UsageError> {
    match option {
        "expect" => {
            exec.note("--expect");
            let case = option_value(parser, "case")?;
            set_once(&mut exec.expect, case, "--expect")?;
        }
        "compare" => {
            exec.note("--compare");
            let value = option_value(parser, "compared cells")?;
            let cells = exec.compare.get_or_insert_with(Vec::new);
            for cell in value.split(',') {
                if cell.is_empty() {
                    return Err(usage(format!(
                        "--compare `{value}` names an empty cell path"
                    )));
                }
                cells.push(cell.to_owned());
            }
        }
        "view" => {
            exec.note("--view");
            let value = option_value(parser, "view")?;
            let Some((cell, function)) = value
                .split_once('=')
                .filter(|(cell, function)| !cell.is_empty() && !function.is_empty())
            else {
                return Err(usage(format!(
                    "--view `{value}` must have the form CELL=FUNCTION"
                )));
            };
            if exec
                .views
                .insert(cell.to_owned(), function.to_owned())
                .is_some()
            {
                return Err(usage(format!(
                    "--view names the cell `{cell}` twice; a cell has one view"
                )));
            }
        }
        "observer" => {
            exec.note("--observer");
            let observer = option_value(parser, "observer")?;
            set_once(&mut exec.observer, observer, "--observer")?;
        }
        "pairs" => {
            exec.note("--pairs");
            let file = option_value(parser, "pairs file")?;
            set_once(&mut exec.pairs, PathBuf::from(file), "--pairs")?;
        }
        _ => unreachable!(
            "compare_option is called only for --expect, --compare, --view, --observer and --pairs"
        ),
    }
    Ok(())
}

/// Parse `--depth`, which bounds the path a run follows, or `--observe`, which declares what the
/// run records along it.
fn path_option(
    parser: &mut lexopt::Parser,
    exec: &mut ExecOptions,
    option: &'static str,
) -> Result<(), UsageError> {
    if option == "observe" {
        exec.note("--observe");
        let path = observe_path(&option_value(parser, "observation file")?)?;
        return set_once(&mut exec.observe, path, "--observe");
    }
    exec.note("--depth");
    let value = option_value(parser, "depth")?;
    let depth = value
        .parse::<u64>()
        .map_err(|_| usage(format!("--depth `{value}` is not a non-negative integer")))?;
    set_once(&mut exec.depth, depth, "--depth")
}

/// Parse one of the stop options of `krs run`.
fn stop_option(
    parser: &mut lexopt::Parser,
    exec: &mut ExecOptions,
    option: &'static str,
) -> Result<(), UsageError> {
    match option {
        "stop-before" => {
            exec.note("--stop-before");
            exec.stop.before.push(stop_name(parser, "--stop-before")?);
        }
        "stop-after" => {
            exec.note("--stop-after");
            exec.stop.after.push(stop_name(parser, "--stop-after")?);
        }
        "stop-count" => {
            exec.note("--stop-count");
            let value = option_value(parser, "stop count")?;
            let count = value
                .parse::<NonZeroU64>()
                .map_err(|_| usage(format!("--stop-count `{value}` is not a positive integer")))?;
            set_once(&mut exec.stop_count, count, "--stop-count")?;
        }
        "stop-when" => {
            exec.note("--stop-when");
            let value = option_value(parser, "stop condition")?;
            let condition = value
                .split_once('=')
                .filter(|(cells, function)| {
                    !function.is_empty() && cells.split(',').all(|cell| !cell.is_empty())
                })
                .map(|(cells, function)| {
                    (
                        cells.split(',').map(str::to_owned).collect::<Vec<_>>(),
                        function.to_owned(),
                    )
                })
                .ok_or_else(|| {
                    usage(format!(
                        "--stop-when `{value}` must have the form CELL,...=FUNCTION"
                    ))
                })?;
            set_once(&mut exec.stop_when, condition, "--stop-when")?;
        }
        _ => unreachable!("stop_option is called only for the stop options"),
    }
    Ok(())
}

/// Parse one of the solver options and `--claim-timeout`.
fn solver_option(
    parser: &mut lexopt::Parser,
    exec: &mut ExecOptions,
    option: &'static str,
) -> Result<(), UsageError> {
    let positive = |value: &str, flag: &str| {
        value
            .parse::<u32>()
            .ok()
            .filter(|value| *value > 0)
            .ok_or_else(|| usage(format!("{flag} `{value}` is not a positive integer")))
    };
    match option {
        "smt-resource-limit" => {
            exec.note("--smt-resource-limit");
            let value = option_value(parser, "resource units")?;
            let units = positive(&value, "--smt-resource-limit")?;
            let units = std::num::NonZeroU32::new(units).expect("a positive integer");
            set_once(&mut exec.smt_resource_limit, units, "--smt-resource-limit")?;
        }
        "smt-clock-ms" => {
            exec.note("--smt-clock-ms");
            let value = option_value(parser, "milliseconds")?;
            let ms = positive(&value, "--smt-clock-ms")?;
            set_once(&mut exec.smt_clock_ms, ms, "--smt-clock-ms")?;
        }
        "smt-retries" => {
            exec.note("--smt-retries");
            let value = option_value(parser, "retries")?;
            let retries = value.parse::<u32>().map_err(|_| {
                usage(format!(
                    "--smt-retries `{value}` is not a non-negative integer"
                ))
            })?;
            set_once(&mut exec.smt_retries, retries, "--smt-retries")?;
        }
        "claim-timeout" => {
            exec.note("--claim-timeout");
            let value = option_value(parser, "seconds")?;
            // A number so small that it rounds to no time at all would cancel every proof
            // before it starts, which is not the positive bound the option promises.
            let timeout = value
                .parse::<f64>()
                .ok()
                .and_then(|seconds| std::time::Duration::try_from_secs_f64(seconds).ok())
                .filter(|timeout| !timeout.is_zero())
                .ok_or_else(|| {
                    usage(format!(
                        "--claim-timeout `{value}` is not a positive number of seconds"
                    ))
                })?;
            set_once(&mut exec.claim_timeout, timeout, "--claim-timeout")?;
        }
        _ => unreachable!("solver_option is called only for the solver options"),
    }
    Ok(())
}

/// The KRS item or K label a stop option names, which must not be empty.
fn stop_name(parser: &mut lexopt::Parser, option: &str) -> Result<String, UsageError> {
    let name = option_value(parser, "stop rule")?;
    if name.is_empty() {
        return Err(usage(format!(
            "{option} needs a KRS item or a K label, not an empty name"
        )));
    }
    Ok(name)
}

/// [`stop_criterion`] of `krs run`'s stop flags in `exec`, beside `--case` when it is given: a count or a
/// condition without a rule is then not refused here but beside the case
/// ([`RunRequest::stop_unpaired`]), since a case whose `run` names stops refuses every stop flag
/// for the reason that only one may say where the run ends, which is the first thing wrong.
fn stop_flags(exec: &mut ExecOptions) -> Result<(StopCriterion, Option<String>), UsageError> {
    let rules = std::mem::take(&mut exec.stop);
    let count = exec.stop_count.take();
    let when = exec.stop_when.take();
    let observer = exec.observer.take();
    let case = exec.case.is_some();
    if case && rules.is_empty() && (count.is_some() || when.is_some()) {
        let refusal = match stop_criterion(rules, count, when, observer) {
            Err(UsageError::Message(message)) => message,
            Err(other) => return Err(other),
            Ok(_) => unreachable!("a count or a condition without a rule is refused"),
        };
        return Ok((StopCriterion::None, Some(refusal)));
    }
    Ok((stop_criterion(rules, count, when, observer)?, None))
}

/// The stop criterion of `--stop-before`, `--stop-after`, `--stop-count` and `--stop-when`
/// with `--observer`: a count or a condition without a rule has no arrival to count or ask at,
/// and an observer without a condition has nothing to evaluate.
fn stop_criterion(
    rules: StopRules,
    count: Option<NonZeroU64>,
    when: Option<(Vec<String>, String)>,
    observer: Option<String>,
) -> Result<StopCriterion, UsageError> {
    if rules.is_empty() && count.is_some() {
        return Err(usage(
            "--stop-count needs --stop-before or --stop-after: it counts arrivals at their rules",
        ));
    }
    if rules.is_empty() && when.is_some() {
        return Err(usage(
            "--stop-when needs --stop-before or --stop-after: it is asked at the arrivals at their rules",
        ));
    }
    if when.is_none() && observer.is_some() {
        return Err(usage(
            "--observer with krs run names the definition --stop-when's function is evaluated in; give --stop-when",
        ));
    }
    if rules.is_empty() {
        return Ok(rules.into());
    }
    Ok(StopCriterion::Rules {
        rules,
        count: count.unwrap_or(NonZeroU64::MIN),
        when: when.map(|(cells, function)| StopWhen {
            function,
            cells,
            observer,
        }),
    })
}

/// The solver options `--smt-resource-limit`, `--smt-clock-ms` and `--smt-retries` give: krs's
/// resource-bounded default ([`krs_exec::BackendOptions::DEFAULT`]) with each given one
/// in place. `--smt-clock-ms` selects the clock mode, so it and `--smt-resource-limit`, which
/// bounds the resource mode, are not given together.
fn solver(exec: &ExecOptions) -> Result<krs_exec::BackendOptions, UsageError> {
    let mut solver = krs_exec::BackendOptions::DEFAULT;
    #[expect(
        clippy::disallowed_methods,
        reason = "krs's `--smt-clock-ms` asks for the clock"
    )]
    let budget = krs_exec::SmtBudget::requested(exec.smt_clock_ms, exec.smt_resource_limit);
    solver.smt_budget = budget.map_err(|_| {
        usage("--smt-resource-limit and --smt-clock-ms select different solver modes; give one")
    })?;
    if let Some(retries) = exec.smt_retries {
        solver.smt_retry_limit = retries;
    }
    // Each retry doubles the previous attempt's bound, a 32-bit count of units or milliseconds
    // that the backend saturates: a retry past the largest bound would repeat it instead of
    // doubling it, which is not the ladder these options state, so the last attempt's bound must
    // fit.
    let (first, unit, flag) = match solver.smt_budget {
        krs_exec::SmtBudget::Units(units) => (units.get(), "units", "--smt-resource-limit"),
        krs_exec::SmtBudget::Clock(clock) => (clock.timeout_ms(), "ms", "--smt-clock-ms"),
    };
    let retries = solver.smt_retry_limit;
    if retries > 32 || u64::from(first) << retries > u64::from(u32::MAX) {
        return Err(usage(format!(
            "{retries} retries double the first Z3 attempt's {first} {unit} past {}, the largest \
             bound of one attempt; give fewer --smt-retries or a smaller {flag}",
            u32::MAX
        )));
    }
    Ok(solver)
}

/// Parse one of the hidden options between a supervising `krs prove` and its workers.
fn worker_option(
    parser: &mut lexopt::Parser,
    exec: &mut ExecOptions,
    option: &'static str,
) -> Result<(), UsageError> {
    match option {
        "worker-protocol" => {
            exec.note("--worker-protocol");
            exec.worker = true;
        }
        "worker-claim" => {
            exec.note("--worker-claim");
            exec.worker_claims
                .push(option_value(parser, "claim label")?);
        }
        "worker-color" => {
            exec.note("--worker-color");
            // The supervisor resolves `auto`: a worker's stdout is never the terminal.
            let value = option_value(parser, "color")?;
            let color = match value.as_str() {
                "always" => ColorChoice::Always,
                "never" => ColorChoice::Never,
                _ => return Err(usage(format!("unknown worker color `{value}`"))),
            };
            set_once(&mut exec.worker_color, color, "--worker-color")?;
        }
        _ => unreachable!("worker_option is called only for the worker options"),
    }
    Ok(())
}

/// The case `--case` names: `FILE`, or `FILE#NAME`, the case NAME of a document of named cases,
/// as `krs cases` prints the case's id and `krs compare` reads a side ([`SideFile::parse`]); FILE
/// must be `.toml` or `.json`, its extension selecting how it is read. A refusal is about the
/// value alone, so it is not followed by the usage ([`UsageError::Value`]).
/// Refuses `--output observations` where nothing may declare observations (`declarable` false):
/// no `--observe`, and no `--case`, whose document may declare them.
fn observations_declared(declarable: bool, output: TermOutput) -> Result<(), UsageError> {
    if output == TermOutput::Observations && !declarable {
        return Err(usage(
            "--output observations prints the observations the run declares; declare them with --observe FILE or give a case whose document has `observe`",
        ));
    }
    Ok(())
}

/// The file `--observe FILE` names, a `.toml` or `.json` document read by its extension.
fn observe_path(value: &str) -> Result<PathBuf, UsageError> {
    let path = PathBuf::from(value);
    match path.extension().and_then(|extension| extension.to_str()) {
        Some("toml" | "json") => Ok(path),
        Some(extension) => Err(UsageError::Value(format!(
            "--observe `{value}` has the extension `.{extension}`; an observation file is `.toml` or `.json`"
        ))),
        None => Err(UsageError::Value(format!(
            "--observe `{value}` has no extension; an observation file is `.toml` or `.json`"
        ))),
    }
}

fn case_path(value: &str) -> Result<(PathBuf, Option<String>), UsageError> {
    if let Ok(side) = SideFile::parse(value) {
        return Ok((side.path, side.name));
    }
    let refused = |message: String| Err(UsageError::Value(message));
    // The file a `#` would end: `FILE#NAME` names a case only of a `.toml` or `.json` FILE.
    let Some((file, name)) = value.split_once('#') else {
        return match Path::new(value)
            .extension()
            .and_then(|extension| extension.to_str())
        {
            Some(extension) => refused(format!(
                "--case `{value}` has the extension `.{extension}`; a case file is `.toml` or `.json`"
            )),
            None => refused(format!(
                "--case `{value}` has no extension; a case file is `.toml` or `.json`"
            )),
        };
    };
    let id = "; `--case FILE#NAME` names the case NAME of a `.toml` or `.json` FILE, as `krs cases` \
              prints a case's id (or give `--case FILE --case-name NAME`)";
    let extension = |path: &str| {
        Path::new(path)
            .extension()
            .and_then(|extension| extension.to_str())
            .map(str::to_owned)
    };
    // `value` reads as FILE#NAME or as a file whose name holds `#`; the refusal names the file
    // an extension marks: the FILE before `#` when it has one, else `value` whole when it has
    // one (`a#b.yaml`), else the FILE.
    match (extension(file), extension(value)) {
        (Some(extension), _)
            if matches!(extension.as_str(), "toml" | "json") && name.is_empty() =>
        {
            refused(format!(
                "--case `{value}`: no case name follows `#`; give `--case {file}#NAME`, or \
                 `--case {file}` for a document of one case"
            ))
        }
        (Some(extension), _) => refused(format!(
            "--case `{value}` names the file `{file}`, which has the extension `.{extension}`; a \
             case file is `.toml` or `.json`{id}"
        )),
        (None, Some(extension)) => refused(format!(
            "--case `{value}` has the extension `.{extension}`; a case file is `.toml` or \
             `.json`{id}"
        )),
        (None, None) => refused(format!(
            "--case `{value}` names the file `{file}`, which has no extension; a case file is \
             `.toml` or `.json`{id}"
        )),
    }
}

/// The case of the `--case` document that run and search select: the one `--case-name` names,
/// or the one `--case FILE#NAME` names by its id, given at most once.
fn selected_case_name(exec: &mut ExecOptions) -> Result<Option<String>, UsageError> {
    if exec.case_name.is_some() && exec.case.is_none() {
        return Err(usage(
            "--case-name selects a case of the document --case names; pass --case FILE",
        ));
    }
    if let (Some(named), Some(name)) = (&exec.case_id_name, &exec.case_name) {
        // Two options that each name the case: the usage line `--case FILE [--case-name NAME]`
        // is what this is corrected against, so it is a usage error, not a refused value.
        return Err(usage(format!(
            "--case names the case `{named}` by its id (FILE#NAME) and --case-name names `{name}`; \
             give the case once"
        )));
    }
    Ok(exec.case_name.take().or_else(|| exec.case_id_name.take()))
}

/// The case documents of `krs cases`, each `.toml` or `.json` (its extension selects how it is
/// read), at least one.
fn case_documents(values: Vec<OsString>) -> Result<Vec<PathBuf>, UsageError> {
    if values.is_empty() {
        return Err(usage(
            "krs cases needs at least one case document (.toml or .json)",
        ));
    }
    values
        .into_iter()
        .map(|value| {
            let path = PathBuf::from(value);
            match path.extension().and_then(|extension| extension.to_str()) {
                Some("toml" | "json") => Ok(path),
                _ => Err(usage(format!(
                    "the case document `{}` is not a `.toml` or `.json` file, which its extension says",
                    path.display()
                ))),
            }
        })
        .collect()
}

/// `krs cases` with its options, which [`exec_command`] checked it accepts.
fn cases_command(
    exec: ExecOptions,
    output: Option<&Path>,
    solver: krs_exec::BackendOptions,
) -> Result<Command, UsageError> {
    Ok(Command::Cases(CasesRequest {
        documents: case_documents(exec.inputs)?,
        jobs: exec.jobs,
        name: exec.name,
        output: cases_output(output)?,
        solver,
        view_budget: exec.view_budget.unwrap_or(DEFAULT_VIEW_BUDGET),
    }))
}

/// The `--output` of `krs cases`: `human` (the default) or `json`.
fn cases_output(output: Option<&Path>) -> Result<CasesOutput, UsageError> {
    match output.map(Path::to_string_lossy) {
        None => Ok(CasesOutput::Human),
        Some(value) if value == "human" => Ok(CasesOutput::Human),
        Some(value) if value == "json" => Ok(CasesOutput::Json),
        Some(value) => Err(usage(format!(
            "unknown --output format `{value}` for krs cases; it prints human or json"
        ))),
    }
}

/// `krs compare` with its options, which [`exec_command`] checked it accepts: `LEFT RIGHT`, or
/// `--expect CASE` and `ACTUAL`.
fn compare_command(
    exec: ExecOptions,
    output: Option<&Path>,
    solver: krs_exec::BackendOptions,
) -> Result<Command, UsageError> {
    let output = compare_output(output)?;
    let view_budget = exec.view_budget.unwrap_or(DEFAULT_VIEW_BUDGET);
    if let Some(file) = exec.pairs {
        // Each pair states its own sides and comparison; options of one comparison would give
        // every pair the same, which a pair's own keys already say.
        if let Some(option) = exec.given.iter().find(|option| {
            ["FILE", "--expect", "--compare", "--view", "--observer"].contains(option)
        }) {
            let option = if *option == "FILE" {
                "LEFT RIGHT"
            } else {
                option
            };
            return Err(usage(format!(
                "{option} does not apply with --pairs: each pair of the file states its sides and its `compare`, `views` and `observer`"
            )));
        }
        let document = file
            .extension()
            .is_some_and(|extension| extension == "toml" || extension == "json");
        if !document {
            return Err(usage(format!(
                "--pairs `{}` is not a `.toml` or `.json` file, which its extension says",
                file.display()
            )));
        }
        return Ok(Command::Compare(CompareRequest {
            sides: CompareSides::Pairs {
                file,
                jobs: exec.jobs,
            },
            compare: None,
            views: std::collections::BTreeMap::new(),
            observer: None,
            output,
            solver,
            view_budget,
        }));
    }
    if exec.jobs.is_some() {
        return Err(usage(
            "--jobs applies to krs compare with --pairs, whose pairs the workers share",
        ));
    }
    let mut files = exec
        .inputs
        .into_iter()
        .map(|value| SideFile::parse(&utf8(value, "side")?).map_err(usage))
        .collect::<Result<Vec<_>, _>>()?;
    let sides = match (exec.expect, files.len()) {
        (Some(case), 1) => {
            if exec.compare.is_some() || !exec.views.is_empty() || exec.observer.is_some() {
                return Err(usage(
                    "--compare, --view and --observer do not apply with --expect: the case's `expect` table states the compared cells, the views and the observer",
                ));
            }
            CompareSides::Expectation {
                case: SideFile::parse(&case).map_err(usage)?,
                actual: files.remove(0),
            }
        }
        (Some(_), given) => {
            return Err(usage(format!(
                "krs compare --expect CASE checks one side, ACTUAL, against the case's expectation; {given} given"
            )));
        }
        (None, 2) => {
            let right = files.remove(1);
            CompareSides::Ends {
                left: files.remove(0),
                right,
            }
        }
        (None, given) => {
            return Err(usage(format!(
                "krs compare takes two sides, LEFT and RIGHT, or --expect CASE and one side, ACTUAL; {given} given"
            )));
        }
    };
    if exec.observer.is_some() && exec.views.is_empty() {
        return Err(usage(
            "--observer names the definition the views are evaluated in, and no --view names a view",
        ));
    }
    Ok(Command::Compare(CompareRequest {
        sides,
        compare: exec.compare,
        views: exec.views,
        observer: exec.observer,
        output,
        solver,
        view_budget,
    }))
}

/// The `--output` format of `krs compare`.
fn compare_output(output: Option<&Path>) -> Result<CompareOutput, UsageError> {
    match output.map(Path::to_string_lossy) {
        None => Ok(CompareOutput::Human),
        Some(value) if value == "human" => Ok(CompareOutput::Human),
        Some(value) if value == "json" => Ok(CompareOutput::Json),
        Some(value) => Err(usage(format!(
            "unknown --output format `{value}` for krs compare; it prints human or json"
        ))),
    }
}

/// The input name and the JSON document of `--input NAME=JSON`.
fn typed_input(value: &str) -> Result<(String, String), UsageError> {
    let (name, document) = value
        .split_once('=')
        .ok_or_else(|| usage(format!("--input `{value}` must have the form NAME=JSON")))?;
    if name.trim_start_matches('$').is_empty() {
        return Err(usage(format!("--input `{value}` has an empty input name")));
    }
    Ok((name.to_owned(), document.to_owned()))
}

/// The options each run-family command accepts beyond the shared selection options.
fn exec_options(kind: CommandKind) -> &'static [&'static str] {
    match kind {
        CommandKind::Parse => &["FILE", "--sort"],
        CommandKind::Run => &[
            "FILE",
            "--case",
            "--case-name",
            "--input",
            "-c",
            "--depth",
            "--stop-before",
            "--stop-after",
            "--stop-count",
            "--stop-when",
            "--observer",
            "--observe",
            "--trace",
            "--coverage",
            "--color",
            "--smt-resource-limit",
            "--smt-clock-ms",
            "--smt-retries",
            "--view-budget",
        ],
        CommandKind::Search => &[
            "FILE",
            "--case",
            "--case-name",
            "--input",
            "-c",
            "--mode",
            "--depth",
            "--max-solutions",
            "--trace",
            "--color",
            "--smt-resource-limit",
            "--smt-clock-ms",
            "--smt-retries",
            "--view-budget",
        ],
        CommandKind::Cases => &[
            "FILE",
            "--jobs",
            "--name",
            "--view-budget",
            "--smt-resource-limit",
            "--smt-clock-ms",
            "--smt-retries",
        ],
        CommandKind::Compare => &[
            "FILE",
            "--expect",
            "--compare",
            "--view",
            "--observer",
            "--pairs",
            "--jobs",
            "--view-budget",
            "--smt-resource-limit",
            "--smt-clock-ms",
            "--smt-retries",
        ],
        CommandKind::Prove => &[
            "--spec-module",
            "--claim",
            "--depth",
            "--color",
            "--smt-resource-limit",
            "--smt-clock-ms",
            "--smt-retries",
            "--claim-timeout",
            "--worker-protocol",
            "--worker-claim",
            "--worker-color",
        ],
        CommandKind::Check | CommandKind::Expand | CommandKind::EmitK | CommandKind::Build => &[],
    }
}

fn term_output(kind: CommandKind, output: Option<PathBuf>) -> Result<TermOutput, UsageError> {
    let Some(output) = output else {
        return Ok(if kind == CommandKind::Parse {
            TermOutput::Kast
        } else {
            TermOutput::Pretty
        });
    };
    let value = output.to_string_lossy();
    match (value.as_ref(), kind) {
        ("kast", _) => Ok(TermOutput::Kast),
        ("json", _) => Ok(TermOutput::Json),
        ("kore", _) => Ok(TermOutput::Kore),
        ("none", CommandKind::Run) => Ok(TermOutput::None),
        ("end", CommandKind::Run) => Ok(TermOutput::End),
        ("observations", CommandKind::Run) => Ok(TermOutput::Observations),
        ("jsonl", CommandKind::Prove) => Ok(TermOutput::JsonLines),
        ("program", CommandKind::Parse) => Ok(TermOutput::Program),
        ("pretty", CommandKind::Run | CommandKind::Search | CommandKind::Prove) => {
            Ok(TermOutput::Pretty)
        }
        ("program", _) => Err(usage("--output program applies only to krs parse")),
        _ => Err(usage(format!(
            "unknown --output format `{value}` for krs {}",
            kind.as_str()
        ))),
    }
}

fn exec_command(
    kind: CommandKind,
    mut exec: ExecOptions,
    output: Option<PathBuf>,
) -> Result<Command, UsageError> {
    let accepted = exec_options(kind);
    if let Some(option) = exec.given.iter().find(|option| !accepted.contains(option)) {
        return Err(usage(if *option == "FILE" {
            format!("krs {} takes no FILE argument", kind.as_str())
        } else {
            format!("{option} does not apply to krs {}", kind.as_str())
        }));
    }
    let solver = solver(&exec)?;
    let view_budget = exec.view_budget.unwrap_or(DEFAULT_VIEW_BUDGET);
    if kind == CommandKind::Cases {
        return cases_command(exec, output.as_deref(), solver);
    }
    if kind == CommandKind::Compare {
        return compare_command(exec, output.as_deref(), solver);
    }
    if exec.inputs.len() > 1 {
        return Err(usage("more than one FILE given"));
    }
    let case_name = selected_case_name(&mut exec)?;
    let (stop, stop_unpaired) = stop_flags(&mut exec)?;
    let input = exec.inputs.into_iter().next().map(|input| {
        if input == "-" {
            ProgramSource::Stdin
        } else {
            ProgramSource::File(PathBuf::from(input))
        }
    });
    let output = term_output(kind, output)?;
    observations_declared(exec.observe.is_some() || exec.case.is_some(), output)?;
    let color = exec.color.unwrap_or_default();
    Ok(match kind {
        CommandKind::Parse => Command::Parse(ParseRequest {
            sort: exec.sort,
            input: input.unwrap_or(ProgramSource::Stdin),
            output,
        }),
        CommandKind::Run => Command::Run(RunRequest {
            input,
            case: exec.case,
            case_name,
            inputs: exec.typed,
            variables: exec.variables,
            depth: exec.depth,
            stop,
            stop_unpaired,
            observe: exec.observe,
            trace: exec.trace,
            coverage: exec.coverage,
            output,
            color,
            solver,
            view_budget,
        }),
        CommandKind::Search => Command::Search(SearchRequest {
            input,
            case: exec.case,
            case_name,
            inputs: exec.typed,
            variables: exec.variables,
            mode: exec.mode.unwrap_or_default(),
            depth: exec.depth,
            max_solutions: exec.max_solutions,
            trace: exec.trace,
            output,
            color,
            solver,
            view_budget,
        }),
        CommandKind::Prove => {
            if !exec.worker && !exec.worker_claims.is_empty() {
                return Err(usage("--worker-claim applies only with --worker-protocol"));
            }
            if !exec.worker && exec.worker_color.is_some() {
                return Err(usage("--worker-color applies only with --worker-protocol"));
            }
            Command::Prove(ProveRequest {
                spec_module: exec.spec_module,
                claims: if exec.worker_claims.is_empty() {
                    exec.claims
                } else {
                    exec.worker_claims
                },
                depth: exec.depth,
                output,
                color: exec.worker_color.unwrap_or(color),
                worker: exec.worker,
                solver,
                claim_timeout: exec.claim_timeout,
            })
        }
        CommandKind::Check
        | CommandKind::Expand
        | CommandKind::EmitK
        | CommandKind::Build
        | CommandKind::Cases
        | CommandKind::Compare => {
            unreachable!("only run-family commands take run options")
        }
    })
}

fn finish_run(kind: CommandKind, options: RunOptions) -> Result<ParseResult, UsageError> {
    let RunOptions {
        exec,
        manifest_path,
        package,
        package_id,
        definition,
        dependencies,
        cfg,
        backend,
        output,
        registration,
        no_reuse,
        message_format,
        measure,
        partition,
        ir,
        profile,
    } = options;
    if package.is_some() && package_id.is_some() {
        return Err(usage("--package and --package-id cannot be combined"));
    }
    let root = FacetSelector {
        package: match (package, package_id) {
            (Some(name), None) => PackageSelector::Name(name),
            (None, Some(id)) => PackageSelector::Id(id),
            _ => return Err(usage("missing --package or --package-id")),
        },
        definition: definition.ok_or_else(|| usage("missing --definition"))?,
    };
    if let Some(option) = exec.given.first()
        && exec_options(kind).is_empty()
    {
        return Err(usage(if *option == "FILE" {
            format!("krs {} takes no FILE argument", kind.as_str())
        } else {
            format!("{option} does not apply to krs {}", kind.as_str())
        }));
    }
    let command = match kind {
        CommandKind::Parse
        | CommandKind::Run
        | CommandKind::Search
        | CommandKind::Prove
        | CommandKind::Cases
        | CommandKind::Compare => {
            if backend.is_some() {
                return Err(usage(format!(
                    "--backend does not apply to krs {}; it always uses the in-process k-rust backend",
                    kind.as_str()
                )));
            }
            exec_command(kind, exec, output)?
        }
        CommandKind::Check if output.is_some() => {
            return Err(usage("--output does not apply to check"));
        }
        CommandKind::Check => Command::Check { backend, partition },
        CommandKind::Expand => Command::Expand { output },
        CommandKind::EmitK => Command::EmitK {
            output: output.ok_or_else(|| usage("missing --output"))?,
            ir,
        },
        CommandKind::Build => Command::Build {
            backend: backend.unwrap_or(Backend::Llvm),
            output: output.ok_or_else(|| usage("missing --output"))?,
        },
    };
    Ok(ParseResult::Run(
        Box::new(CommandRequest {
            command,
            manifest_path: manifest_path.unwrap_or_else(|| PathBuf::from("Cargo.toml")),
            root,
            dependencies,
            cfg,
            registration: registration.unwrap_or(RegistrationMode::Inventory),
            no_reuse,
            message_format: message_format.unwrap_or_default(),
            profile,
        }),
        measure,
    ))
}

/// The options of `krs kink` that are krs's own and take a value, as `--name`.
#[cfg(feature = "kink")]
const KINK_VALUE_OPTIONS: [&str; 12] = [
    "--manifest-path",
    "--package",
    "--package-id",
    "--definition",
    "--dependency",
    "--cfg",
    "--profile",
    "--message-format",
    "--registration",
    "--corpus",
    "--timings",
    "--counters",
];

/// Parse `krs kink`'s arguments: krs's selection options and `--corpus`, `--locked`, before or
/// after the verb; the verb (`emit`, or one of kink-flow's); and, for a kink-flow verb, every
/// other argument in order, which kink-flow's parser reads. Before the verb only krs's options
/// may appear, so the verb is the first argument that is neither one of them nor a value of one.
#[cfg(feature = "kink")]
fn parse_kink(arguments: Vec<OsString>) -> Result<ParseResult, UsageError> {
    let mut verb = None;
    parse_kink_verb(arguments, &mut verb).map_err(|message| UsageError::Kink(message, verb))
}

/// [`parse_kink`], recording in `verb` the verb as soon as it is read, so that a usage error
/// after it is shown with the verb's usage.
#[cfg(feature = "kink")]
fn parse_kink_verb(
    arguments: Vec<OsString>,
    verb: &mut Option<String>,
) -> Result<ParseResult, String> {
    let kink = |message: String| message;
    let arguments = arguments
        .into_iter()
        .map(|argument| {
            argument
                .into_string()
                .map_err(|_| kink("an argument is not valid UTF-8".into()))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut options = RunOptions::default();
    let mut corpus = None;
    let mut locked = false;
    let mut check = false;
    let mut rest = Vec::new();
    let mut arguments = arguments.into_iter();
    while let Some(argument) = arguments.next() {
        // Help after a verb is the verb's: its usage and its options, kink-flow's included.
        if matches!(argument.as_str(), "-h" | "--help") {
            return Ok(ParseResult::KinkHelp(verb.clone()));
        }
        let (name, inline) = match argument.split_once('=') {
            Some((name, value)) if name.starts_with("--") => {
                (name.to_owned(), Some(value.to_owned()))
            }
            _ => (argument.clone(), None),
        };
        if KINK_VALUE_OPTIONS.contains(&name.as_str()) {
            let value = match inline {
                Some(value) => value,
                None => arguments
                    .next()
                    .ok_or_else(|| kink(format!("{name} needs a value")))?,
            };
            kink_selection(&mut options, &mut corpus, &name, value)
                .map_err(|error| kink(error.to_string()))?;
            continue;
        }
        match name.as_str() {
            "--no-reuse" => {
                return Err(kink(
                    "--no-reuse does not apply to krs kink: every command that builds the \
                     package builds it in process, and reuses no earlier build"
                        .into(),
                ));
            }
            "--locked" if inline.is_none() => locked = true,
            "--check" if inline.is_none() && verb.as_deref() == Some("emit") => check = true,
            _ if verb.is_none() => {
                if argument.starts_with('-') {
                    return Err(kink(format!(
                        "{argument} before the verb: give the verb first (emit, {})",
                        kink_verbs()
                    )));
                }
                if argument != "emit" && kink_flow::Verb::parse(&argument).is_none() {
                    return Err(kink(kink_flow::Verb::retired(&argument).unwrap_or_else(
                        || format!("unknown verb `{argument}`; expected emit, {}", kink_verbs()),
                    )));
                }
                *verb = Some(argument);
            }
            _ => rest.push(argument),
        }
    }
    let verb = verb
        .clone()
        .ok_or_else(|| kink(format!("missing verb: emit, {}", kink_verbs())))?;
    kink_request(options, corpus, locked, check, &verb, rest)
}

/// The first argument of `args`, the arguments of `krs kink VERB` that are not krs's own, that
/// begins with `-` and is no option `verb` takes: kink-flow's options of the verb, and the flags by
/// which krs names the lists the verb takes as operands (`run --mutations`, `query --patterns`,
/// `fuzz --templates`, `prune --mutations` and `--patterns`). The value of an option that takes
/// one is skipped.
#[cfg(feature = "kink")]
fn unlisted_option(verb: kink_flow::Verb, args: &[String]) -> Option<&str> {
    let operands: &[&str] = match verb {
        kink_flow::Verb::Run => &["--mutations"],
        kink_flow::Verb::Query => &["--patterns"],
        kink_flow::Verb::Fuzz => &["--templates"],
        kink_flow::Verb::Prune => &["--mutations", "--patterns"],
        kink_flow::Verb::Check
        | kink_flow::Verb::Coverage
        | kink_flow::Verb::Report
        | kink_flow::Verb::Compare => &[],
    };
    let mut args = args.iter();
    while let Some(argument) = args.next() {
        if !argument.starts_with('-') {
            continue;
        }
        if operands.contains(&argument.as_str()) {
            args.next();
            continue;
        }
        match verb
            .options()
            .iter()
            .find(|option| option.flag() == argument)
        {
            Some(option) => {
                if option.spelling.contains(' ') {
                    args.next();
                }
            }
            None => return Some(argument),
        }
    }
    None
}

/// The request of `krs kink VERB` with the options `parse_kink` read, and `rest`, the
/// arguments that are not krs's.
#[cfg(feature = "kink")]
fn kink_request(
    options: RunOptions,
    corpus: Option<PathBuf>,
    locked: bool,
    check: bool,
    verb: &str,
    rest: Vec<String>,
) -> Result<ParseResult, String> {
    let kink = |message: String| message;
    let verb = if verb == "emit" {
        if let Some(argument) = rest.first() {
            return Err(kink(format!("krs kink emit takes no {argument}")));
        }
        if locked {
            return Err(kink(
                "--locked does not apply to emit; emit --check writes nothing and fails on a \
                 stale definition.k"
                    .into(),
            ));
        }
        krs_cli::KinkVerb::Emit { check }
    } else {
        let verb = kink_flow::Verb::parse(verb).expect("the verb was checked");
        if locked && verb == kink_flow::Verb::Report {
            return Err(kink(
                "--locked does not apply to report, which builds nothing and only prints the \
                 stored run; emit --check fails on a stale definition.k"
                    .into(),
            ));
        }
        // An option the verb does not take is the first thing wrong with the command line, before
        // a missing selection: kink-flow's parser would refuse it only after the package is
        // read.
        if let Some(argument) = unlisted_option(verb, &rest) {
            return Err(kink(kink_flow::cli::unexpected_argument(argument)));
        }
        krs_cli::KinkVerb::Flow {
            verb,
            options: rest,
        }
    };
    if options.package.is_some() && options.package_id.is_some() {
        return Err(kink("--package and --package-id cannot be combined".into()));
    }
    // A flow names the definition it is for, so a command given `--corpus DIR` takes from the
    // flow's `[spec] krs` whichever of the package and the facet it does not name; one it does
    // name is compared with the flow's once the package is planned, and another's is refused.
    let named = options.package.is_some() || options.package_id.is_some();
    let flow = if named && options.definition.is_some() {
        None
    } else {
        Some(corpus.as_deref().map_or_else(
            || Err("no --corpus DIR names a flow that states it".to_owned()),
            krs_cli::kink::flow_definition,
        ))
    };
    let from_flow = |missing: &str| match &flow {
        Some(Ok(definition)) => Ok(definition.clone()),
        Some(Err(why)) => Err(kink(format!("missing {missing}: {why}"))),
        None => unreachable!("the flow is read when a selection is missing"),
    };
    let root = FacetSelector {
        package: match (options.package, options.package_id) {
            (Some(name), None) => PackageSelector::Name(name),
            (None, Some(id)) => PackageSelector::Id(id),
            _ => PackageSelector::Name(from_flow("--package or --package-id")?.0),
        },
        definition: match options.definition {
            Some(definition) => definition,
            None => from_flow("--definition")?.1,
        },
    };
    Ok(ParseResult::Kink(
        Box::new(krs_cli::KinkRequest {
            manifest_path: options
                .manifest_path
                .unwrap_or_else(|| PathBuf::from("Cargo.toml")),
            root,
            dependencies: options.dependencies,
            cfg: options.cfg,
            registration: options.registration.unwrap_or(RegistrationMode::Inventory),
            profile: options.profile,
            message_format: options.message_format.unwrap_or_default(),
            corpus,
            locked,
            verb,
        }),
        options.measure,
    ))
}

/// kink-flow's verbs, as a usage message lists them.
#[cfg(feature = "kink")]
fn kink_verbs() -> String {
    kink_flow::Verb::ALL
        .iter()
        .map(|verb| verb.as_str())
        .collect::<Vec<_>>()
        .join(", ")
}

/// One of `krs kink`'s value options ([`KINK_VALUE_OPTIONS`]), read as the other commands read
/// it.
#[cfg(feature = "kink")]
fn kink_selection(
    options: &mut RunOptions,
    corpus: &mut Option<PathBuf>,
    name: &str,
    value: String,
) -> Result<(), UsageError> {
    match name {
        "--manifest-path" => set_once(&mut options.manifest_path, PathBuf::from(value), name),
        "--package" => set_once(&mut options.package, value, name),
        "--package-id" => set_once(&mut options.package_id, value, name),
        "--definition" => set_once(&mut options.definition, value, name),
        "--dependency" => {
            options.dependencies.push(parse_dependency(value.into())?);
            Ok(())
        }
        "--cfg" => {
            options.cfg.push(parse_cfg(value.into())?);
            Ok(())
        }
        "--profile" => {
            let selected = krs_ir::RawKProfile::from_metadata(&value).ok_or_else(|| {
                usage(format!(
                    "unknown profile `{value}`; expected standard or strict"
                ))
            })?;
            set_once(&mut options.profile, selected, name)
        }
        "--message-format" => {
            let selected = match value.as_str() {
                "human" => MessageFormat::Human,
                "json" => MessageFormat::Json,
                _ => return Err(usage(format!("unknown message format `{value}`"))),
            };
            set_once(&mut options.message_format, selected, name)
        }
        "--registration" => {
            let selected = match value.as_str() {
                "inventory" => RegistrationMode::Inventory,
                "explicit" => RegistrationMode::Explicit,
                _ => return Err(usage(format!("unknown registration mode `{value}`"))),
            };
            set_once(&mut options.registration, selected, name)
        }
        "--corpus" => set_once(corpus, PathBuf::from(value), name),
        "--timings" => set_once(&mut options.measure.timings, PathBuf::from(value), name),
        "--counters" => set_once(&mut options.measure.counters, PathBuf::from(value), name),
        _ => unreachable!("kink_selection is called only for KINK_VALUE_OPTIONS"),
    }
}

fn parse_format(parser: &mut lexopt::Parser) -> Result<ParseResult, UsageError> {
    let mut stdin = false;
    let mut edition = None;
    let mut check = false;
    let mut manifest_path = None;
    let mut paths = Vec::new();
    let mut trailing_comments = None;
    while let Some(argument) = parser.next()? {
        match argument {
            Short('h') | Long("help") => return Ok(ParseResult::Help),
            Long("stdin") => stdin = true,
            Long("edition") => {
                let value = option_value(parser, "Rust edition")?;
                set_once(
                    &mut edition,
                    value.parse::<Edition>().map_err(usage)?,
                    "--edition",
                )?;
            }
            Long("check") => check = true,
            Long("manifest-path") => set_once(
                &mut manifest_path,
                PathBuf::from(option_value(parser, "manifest path")?),
                "--manifest-path",
            )?,
            Long("trailing-comments") => {
                let value = option_value(parser, "trailing comment style")?;
                let selected = match value.as_str() {
                    "aligned" => TrailingCommentStyle::AlignedColumn,
                    "gutter" => TrailingCommentStyle::FixedGutter,
                    _ => return Err(usage(format!("unknown trailing comment style `{value}`"))),
                };
                set_once(&mut trailing_comments, selected, "--trailing-comments")?;
            }
            Value(path) => paths.push(PathBuf::from(path)),
            _ => return Err(argument.unexpected().into()),
        }
    }
    if stdin && (!paths.is_empty() || manifest_path.is_some()) {
        return Err(usage(
            "--stdin cannot be combined with paths or --manifest-path",
        ));
    }
    if edition.is_some() && !stdin {
        return Err(usage("--edition requires --stdin"));
    }
    Ok(ParseResult::Format(FormatRequest {
        stdin,
        edition: edition.unwrap_or_default(),
        check,
        manifest_path,
        paths,
        trailing_comments: trailing_comments.unwrap_or(TrailingCommentStyle::AlignedColumn),
    }))
}

fn execute_format(request: &FormatRequest) -> Result<bool, String> {
    let options = FormatOptions {
        trailing_comments: request.trailing_comments,
        edition: request.edition,
        ..FormatOptions::default()
    };
    if request.stdin {
        let mut source = String::new();
        io::stdin()
            .read_to_string(&mut source)
            .map_err(|error| format!("cannot read stdin: {error}"))?;
        let output =
            krs_fmt::format_source(&source, &options).map_err(|error| error.to_string())?;
        if request.check {
            if output != source {
                eprint!(
                    "{}",
                    krs_fmt::unified_diff(Path::new("<stdin>"), &source, &output)
                );
                return Ok(false);
            }
        } else {
            io::stdout()
                .lock()
                .write_all(output.as_bytes())
                .map_err(|error| format!("cannot write stdout: {error}"))?;
        }
        return Ok(true);
    }

    let files = krs_cli::discover_format_inputs(request.manifest_path.as_deref(), &request.paths)?;
    let mut formatted = Vec::with_capacity(files.len());
    let mut failed = false;
    for input in &files {
        match krs_fmt::format_file(
            &input.path,
            &FormatOptions {
                edition: input.edition,
                facade_aliases: input.facade_aliases.clone(),
                ..options
            },
        ) {
            Ok(file) => formatted.push(file),
            Err(error) => {
                eprintln!("{}: {error}", input.path.display());
                failed = true;
            }
        }
    }
    if failed {
        return Ok(false);
    }
    if request.check {
        let mut changed = false;
        for file in formatted.iter().filter(|file| file.changed) {
            let before = std::fs::read_to_string(&file.path)
                .map_err(|error| format!("cannot reread `{}`: {error}", file.path.display()))?;
            eprint!(
                "{}",
                krs_fmt::unified_diff(&file.path, &before, &file.output)
            );
            changed = true;
        }
        return Ok(!changed);
    }
    for file in formatted.into_iter().filter(|file| file.changed) {
        std::fs::write(&file.path, file.output)
            .map_err(|error| format!("cannot write `{}`: {error}", file.path.display()))?;
    }
    Ok(true)
}

fn parse_dependency(value: OsString) -> Result<FacetSelector, UsageError> {
    let value = utf8(value, "dependency")?;
    if !value.contains(':') {
        return Err(usage(format!(
            "dependency `{value}` must have the form CargoPackage:definition"
        )));
    }
    FacetSelector::parse(&value).ok_or_else(|| {
        usage(format!(
            "dependency `{value}` must have non-empty package and definition names"
        ))
    })
}

fn parse_cfg(value: OsString) -> Result<KrsCfg, UsageError> {
    let value = utf8(value, "cfg")?;
    KrsCfg::parse(&value).ok_or_else(|| {
        let key = value.split_once('=').map_or(value.as_str(), |(key, _)| key);
        usage(format!("invalid cfg key `{key}`"))
    })
}

fn utf8(value: OsString, role: &str) -> Result<String, UsageError> {
    value
        .into_string()
        .map_err(|_| usage(format!("{role} is not valid UTF-8")))
}

#[cfg(test)]
mod tests {
    use super::*;
    use krs_diagnostic::codes::CodeKind;

    #[test]
    fn reports_located_then_unlocated_errors_and_warnings_as_envelopes() {
        let package = krs_ir::PackageId::new("diag", "diag", "0.1.0", "workspace").unwrap();
        let file = krs_ir::SourceFileId::new(
            package,
            "src/lib.rs",
            krs_ir::Sha256Digest::new("11".repeat(32)).unwrap(),
        )
        .unwrap();
        let unused = krs_diagnostic::Code::foreign("UnusedVariable", CodeKind::Author);
        let mut envelope = krs_cli::DiagnosticEnvelope::error(
            krs_cli::DiagnosticStage::Native,
            unused.clone(),
            "unused variable",
            krs_ir::SourceRange::new(file, 7, 16).unwrap(),
        );
        envelope.severity = krs_cli::DiagnosticSeverity::Warning;
        // An undefined label in a `raw_k!` text: the author's.
        let error = krs_cli::DiagnosticEnvelope::unlocated(
            krs_cli::DiagnosticStage::Native,
            krs_diagnostic::Code::foreign("UndefinedKLabel", CodeKind::Author),
            "undefined label",
        );
        let mut warning = krs_cli::DiagnosticEnvelope::unlocated(
            krs_cli::DiagnosticStage::Native,
            unused,
            "unused variable",
        );
        warning.severity = krs_cli::DiagnosticSeverity::Warning;
        let mut output = Vec::new();
        write_diagnostics(
            &mut output,
            &[error.clone(), envelope.clone(), warning.clone()],
            MessageFormat::Json,
            &DiagnosticSources::default(),
            false,
        )
        .unwrap();
        let output = String::from_utf8(output).unwrap();
        assert_eq!(
            output,
            format!(
                "{}{}{}",
                envelope.to_json_line().unwrap(),
                error.to_json_line().unwrap(),
                warning.to_json_line().unwrap(),
            )
        );
        assert!(output.contains("\"authored_range\":null"));
        let mut human = Vec::new();
        write_diagnostics(
            &mut human,
            &[error],
            MessageFormat::Human,
            &DiagnosticSources::default(),
            false,
        )
        .unwrap();
        assert_eq!(
            String::from_utf8(human).unwrap(),
            "error[UndefinedKLabel]: undefined label\n"
        );
    }

    fn parse_args(args: &[&str]) -> Result<ParseResult, UsageError> {
        parse(args.iter().map(OsString::from).collect())
    }

    fn error(args: &[&str]) -> String {
        match parse_args(args) {
            Err(error) => error.to_string(),
            Ok(_) => panic!("expected error for {args:?}"),
        }
    }

    #[cfg(feature = "kink")]
    fn kink(args: &[&str]) -> krs_cli::KinkRequest {
        match parse_args(args).unwrap() {
            ParseResult::Kink(request, _) => *request,
            _ => panic!("expected a kink command for {args:?}"),
        }
    }

    /// A flow names the definition it is for, so `krs kink --corpus DIR` takes from the flow
    /// whichever of the package and the facet the command line does not name; a selection the
    /// command line gives is kept, to be compared with the flow's once the package is planned;
    /// and a corpus whose flow names none leaves the selection missing, saying why.
    #[cfg(feature = "kink")]
    #[test]
    fn kink_takes_a_missing_selection_from_the_corpus_flow() {
        let directory = tempfile::tempdir().unwrap();
        let corpus = directory.path().join("corpus");
        std::fs::create_dir_all(&corpus).unwrap();
        std::fs::write(
            corpus.join("FLOW.toml"),
            "[spec]\nkrs = { package = \"plus\", definition = \"main\" }\n",
        )
        .unwrap();
        let corpus = corpus.to_str().unwrap();
        let selected = |extra: &[&str]| {
            let request = kink(&[&["kink", "coverage", "--corpus", corpus][..], extra].concat());
            (request.root.package, request.root.definition)
        };
        let name = |name: &str| PackageSelector::Name(name.to_owned());
        assert_eq!(selected(&[]), (name("plus"), "main".to_owned()));
        assert_eq!(
            selected(&["--package", "other"]),
            (name("other"), "main".to_owned())
        );
        assert_eq!(
            selected(&["--definition", "lite"]),
            (name("plus"), "lite".to_owned())
        );
        assert_eq!(
            selected(&["--package-id", "id", "--definition", "lite"]),
            (PackageSelector::Id("id".to_owned()), "lite".to_owned())
        );
        // No flow states the selection: no `--corpus`, a directory without a manifest, a K flow.
        let missing = error(&["kink", "coverage", "--package", "p"]);
        assert!(
            missing.contains("missing --definition: no --corpus DIR names a flow"),
            "{missing}"
        );
        let empty = directory.path().join("empty");
        let missing = error(&["kink", "coverage", "--corpus", empty.to_str().unwrap()]);
        assert!(
            missing.contains("missing --package or --package-id:")
                && missing.contains("FLOW.toml is not a file"),
            "{missing}"
        );
        std::fs::create_dir_all(&empty).unwrap();
        std::fs::write(
            empty.join("FLOW.toml"),
            "[spec]\nentry = \"a.k\"\nmain_module = \"A\"\n",
        )
        .unwrap();
        let missing = error(&["kink", "coverage", "--corpus", empty.to_str().unwrap()]);
        assert!(missing.contains("is a K flow"), "{missing}");
    }

    /// `krs kink` takes krs's selection before or after the verb and hands every other option
    /// to kink-flow's parser in order; `emit` takes `--check` and nothing of kink-flow's.
    #[cfg(feature = "kink")]
    #[test]
    fn kink_separates_krs_options_from_the_verbs() {
        let request = kink(&[
            "kink",
            "--package",
            "p",
            "run",
            "--only",
            "a",
            "--definition=main",
            "--full",
            "--locked",
            "--corpus",
            "c",
            "--output",
            "verdicts",
        ]);
        assert_eq!(request.root.definition, "main");
        assert_eq!(request.corpus, Some(PathBuf::from("c")));
        assert!(request.locked);
        assert_eq!(
            request.verb,
            krs_cli::KinkVerb::Flow {
                verb: kink_flow::Verb::Run,
                options: ["--only", "a", "--full", "--output", "verdicts"]
                    .map(String::from)
                    .to_vec(),
            }
        );
        let emit = kink(&[
            "kink",
            "emit",
            "--check",
            "--package",
            "p",
            "--definition",
            "d",
        ]);
        assert_eq!(emit.verb, krs_cli::KinkVerb::Emit { check: true });
    }

    /// `krs kink results` is a usage error that names `coverage`, the verb that replaced it.
    #[cfg(feature = "kink")]
    #[test]
    fn kink_refuses_the_retired_results_verb() {
        let error = error(&["kink", "results", "--package", "p"]);
        assert!(
            error.contains("`results` is no longer a verb: `coverage` replaced it"),
            "{error}"
        );
    }

    /// `krs kink` refuses an option before the verb or on a verb it does not apply to, an
    /// unknown verb, and a missing package or verb; `krs kink --help` is kink's own help.
    #[cfg(feature = "kink")]
    #[test]
    fn kink_refuses_misplaced_options_and_a_missing_selection() {
        for (args, message) in [
            (&["kink", "--full", "run"][..], "--full before the verb"),
            (
                &["kink", "walk", "--package", "p"][..],
                "unknown verb `walk`",
            ),
            (
                &[
                    "kink",
                    "emit",
                    "--full",
                    "--package",
                    "p",
                    "--definition",
                    "d",
                ][..],
                "takes no --full",
            ),
            (
                &[
                    "kink",
                    "emit",
                    "--locked",
                    "--package",
                    "p",
                    "--definition",
                    "d",
                ][..],
                "--locked does not apply",
            ),
            (
                &[
                    "kink",
                    "report",
                    "--locked",
                    "--package",
                    "p",
                    "--definition",
                    "d",
                ][..],
                "--locked does not apply to report",
            ),
            (
                &[
                    "kink",
                    "report",
                    "--no-reuse",
                    "--package",
                    "p",
                    "--definition",
                    "d",
                ][..],
                "every command that builds the package",
            ),
            (
                &["kink", "run", "--definition", "d"][..],
                "missing --package",
            ),
            // An option the verb does not take comes first, in krs's wording, before a missing
            // selection; a value of a listed option and krs's operand flag are no option.
            (&["kink", "run", "--bogus"][..], "invalid option '--bogus'"),
            (
                &[
                    "kink",
                    "fuzz",
                    "--seed",
                    "-3",
                    "--templates",
                    "t.toml",
                    "--bogus",
                ][..],
                "invalid option '--bogus'",
            ),
            (
                &["kink", "--package", "p", "--definition", "d"][..],
                "missing verb",
            ),
        ] {
            let error = error(args);
            assert!(error.contains(message), "{args:?}: {error}");
        }
        assert!(matches!(
            parse_args(&["kink", "--help"]),
            Ok(ParseResult::KinkHelp(None))
        ));
        assert!(
            error(&["kink", "run", "--only", "x", "--mutations", "m.toml"])
                .contains("missing --package")
        );
        // After a verb it is the verb's help.
        assert!(matches!(
            parse_args(&["kink", "--package", "p", "fuzz", "--template", "t", "-h"]),
            Ok(ParseResult::KinkHelp(Some(verb))) if verb == "fuzz"
        ));
        // A usage error names the verb, once read, whose usage it shows.
        assert!(matches!(
            parse_args(&["kink", "emit", "--full"]),
            Err(UsageError::Kink(_, Some(verb))) if verb == "emit"
        ));
        assert!(matches!(
            parse_args(&["kink", "--full", "run"]),
            Err(UsageError::Kink(_, None))
        ));
    }

    /// `krs kink VERB --help` lists the verb's usage line, krs's options and every option of
    /// kink-flow's verb, which no other help krs prints lists; each verb's usage line is the one
    /// `krs kink --help` lists; a usage error shows the verb's usage line and where its options
    /// are, not the whole help.
    #[cfg(feature = "kink")]
    #[test]
    fn kink_verb_help_lists_the_verbs_options() {
        let words = |text: &str| text.split_whitespace().collect::<Vec<_>>().join(" ");
        for (verb, usage) in KINK_VERB_USAGE {
            assert!(words(KINK_USAGE).contains(usage), "{verb}: {usage}");
            let help = kink_verb_help(verb);
            assert!(help.starts_with(&format!("krs kink {verb}: ")), "{help}");
            assert!(help.contains(&format!("\nusage: {usage}\n")), "{help}");
            if let Some(flow) = kink_flow::Verb::parse(verb) {
                assert!(
                    help.contains(&kink_flow::cli::options_text(flow.options())),
                    "{help}"
                );
                // A usage line that spells kink-flow's options out spells every one; fuzz's
                // names them as a group.
                if flow != kink_flow::Verb::Fuzz {
                    for option in flow.options() {
                        assert!(
                            usage.contains(&format!("[{}", option.flag())),
                            "{verb}: {usage} lacks {}",
                            option.flag()
                        );
                    }
                }
            }
            let tail = kink_usage_tail(Some(verb));
            assert_eq!(tail.lines().count(), 2, "{tail}");
            assert!(tail.starts_with(&format!("usage: {usage}\n")), "{tail}");
        }
        let fuzz = kink_verb_help("fuzz");
        for option in ["--cases N", "--work W", "--templates PATH", "--locked"] {
            assert!(fuzz.contains(&format!("  {option} ")), "{fuzz}");
        }
        assert!(
            fuzz.contains(
                "--patterns defaults to the patterns FLOW.toml declares, else the corpus's \
                 PATTERNS.toml"
            ),
            "{fuzz}"
        );
        assert!(!kink_verb_help("emit").contains("--locked"));
        assert!(kink_usage_tail(None).contains("VERB one of emit, check, coverage"));
    }

    fn run(args: &[&str]) -> (CommandRequest, MeasureOptions) {
        match parse_args(args).unwrap() {
            ParseResult::Run(request, measure) => (*request, measure),
            _ => panic!("expected run command"),
        }
    }

    #[test]
    fn parses_message_format() {
        for command in ["check", "expand", "emit-k", "build"] {
            let mut args = vec![command, "--package", "imp", "--definition", "main"];
            if matches!(command, "emit-k" | "build") {
                args.extend(["--output", "out"]);
            }
            assert_eq!(run(&args).0.message_format, MessageFormat::Human);
            for spelling in [
                vec!["--message-format", "json"],
                vec!["--message-format=json"],
                vec!["--message-format=human"],
            ] {
                let mut selected = args.clone();
                selected.extend(&spelling);
                let expected = if spelling.last() == Some(&"--message-format=human") {
                    MessageFormat::Human
                } else {
                    MessageFormat::Json
                };
                assert_eq!(run(&selected).0.message_format, expected);
            }
        }
        assert_eq!(
            error(&["check", "--message-format=xml"]),
            "unknown message format `xml`"
        );
    }

    #[test]
    fn parses_value_options_with_equals() {
        let (request, measure) = run(&[
            "build",
            "--manifest-path=Cargo.toml",
            "--package=imp",
            "--definition=main",
            "--dependency=base:core",
            "--cfg=feature=enabled",
            "--backend=haskell",
            "--output=out",
            "--timings=timings.json",
            "--counters=counters.json",
            "--registration=explicit",
        ]);
        assert_eq!(
            request.command,
            Command::Build {
                backend: Backend::Haskell,
                output: PathBuf::from("out")
            }
        );
        assert_eq!(request.dependencies.len(), 1);
        assert_eq!(request.cfg[0].value.as_deref(), Some("enabled"));
        assert_eq!(request.registration, RegistrationMode::Explicit);
        assert_eq!(measure.timings, Some(PathBuf::from("timings.json")));
        assert_eq!(measure.counters, Some(PathBuf::from("counters.json")));
    }

    #[test]
    fn parses_command_variants_and_repeatable_values() {
        let (request, _) = run(&[
            "emit-k",
            "--package",
            "imp",
            "--definition",
            "main",
            "--backend",
            "haskell",
            "--output",
            "out",
            "--dependency",
            "a:b",
            "--dependency",
            "c:d",
            "--cfg",
            "flag",
            "--cfg",
            "mode=fast",
            "--no-reuse",
            "--no-reuse",
        ]);
        assert_eq!(
            request.command,
            Command::EmitK {
                output: "out".into(),
                ir: false,
            }
        );
        assert_eq!(request.dependencies.len(), 2);
        assert_eq!(request.cfg.len(), 2);
        assert_eq!(request.cfg[0].value, None);
        assert!(request.no_reuse);
        let (request, _) = run(&[
            "emit-k",
            "--package",
            "imp",
            "--definition",
            "main",
            "--output",
            "out",
            "--ir",
        ]);
        assert_eq!(
            request.command,
            Command::EmitK {
                output: "out".into(),
                ir: true,
            }
        );
        for command in ["check", "build"] {
            let mut args = vec![command, "--package", "imp", "--definition", "main", "--ir"];
            if command == "build" {
                args.extend(["--output", "out"]);
            }
            assert!(parse_args(&args).is_err(), "{command} accepted --ir");
        }

        let (request, _) = run(&[
            "check",
            "--package-id",
            "exact-id",
            "--definition",
            "main",
            "--backend",
            "haskell",
        ]);
        assert_eq!(
            request.command,
            Command::Check {
                backend: Some(Backend::Haskell),
                partition: false,
            }
        );
        assert_eq!(request.root.package, PackageSelector::Id("exact-id".into()));

        let (request, _) = run(&["expand", "--package", "imp", "--definition", "main"]);
        assert_eq!(request.command, Command::Expand { output: None });
        let (request, _) = run(&[
            "expand",
            "--package",
            "imp",
            "--definition",
            "main",
            "--output",
            "printed",
        ]);
        assert_eq!(
            request.command,
            Command::Expand {
                output: Some(PathBuf::from("printed"))
            }
        );
    }

    #[test]
    fn rejects_repeated_singular_options() {
        let required = [
            "build",
            "--package-id",
            "id",
            "--definition",
            "main",
            "--output",
            "out",
        ];
        for (option, value) in [
            ("--manifest-path", "Cargo.toml"),
            ("--package", "imp"),
            ("--package-id", "id"),
            ("--definition", "main"),
            ("--backend", "llvm"),
            ("--output", "out"),
            ("--timings", "timings.json"),
            ("--counters", "counters.json"),
            ("--registration", "inventory"),
            ("--message-format", "json"),
        ] {
            let mut args = required.to_vec();
            if !args.contains(&option) {
                args.extend([option, value]);
            }
            args.extend([option, value]);
            assert_eq!(
                error(&args),
                format!("{option} specified more than once"),
                "{args:?}"
            );
        }
        for (option, value) in [
            ("--manifest-path", "Cargo.toml"),
            ("--trailing-comments", "gutter"),
        ] {
            assert_eq!(
                error(&["fmt", option, value, option, value]),
                format!("{option} specified more than once")
            );
        }
    }

    #[test]
    fn rejects_invalid_combinations_and_spellings() {
        let base = ["--package", "imp", "--definition", "main"];
        assert!(
            error(&[
                "check",
                "--package",
                "imp",
                "--package-id",
                "id",
                "--definition",
                "main"
            ])
            .contains("--package and --package-id")
        );
        for key in ["1abc", "a-b", "fn", ""] {
            assert!(
                error(&[
                    "check",
                    "--package",
                    "imp",
                    "--definition",
                    "main",
                    "--cfg",
                    key
                ])
                .contains("invalid cfg key")
            );
        }
        assert!(
            error(&[
                "check", base[0], base[1], base[2], base[3], "--output", "out"
            ])
            .contains("--output does not apply to check")
        );
        for command in ["emit-k", "build"] {
            assert!(
                error(&[command, base[0], base[1], base[2], base[3]]).contains("missing --output")
            );
        }
        assert!(error(&["check", "--package", "imp"]).contains("missing --definition"));
        assert!(!error(&["check", "--wat"]).is_empty());
        assert!(error(&["wat"]).contains("unknown command"));
        assert!(error(&["check", "--backend", "unknown"]).contains("unknown backend"));
        for dependency in ["base", ":core", "base:"] {
            assert!(error(&["check", "--dependency", dependency]).contains("dependency"));
        }
    }

    #[test]
    fn parses_fmt_editor_mode() {
        let ParseResult::Format(request) = parse_args(&[
            "fmt",
            "--stdin",
            "--edition",
            "2021",
            "--trailing-comments",
            "gutter",
        ])
        .unwrap() else {
            panic!("expected fmt command")
        };
        assert!(request.stdin);
        assert_eq!(request.edition, Edition::E2021);
        assert_eq!(request.trailing_comments, TrailingCommentStyle::FixedGutter);
    }

    #[test]
    fn parses_fmt_modes() {
        let ParseResult::Format(request) = parse_args(&[
            "fmt",
            "--stdin",
            "--stdin",
            "--check",
            "--check",
            "--trailing-comments=gutter",
        ])
        .unwrap() else {
            panic!("expected fmt command")
        };
        assert!(request.stdin);
        assert!(request.check);
        assert_eq!(request.trailing_comments, TrailingCommentStyle::FixedGutter);
        let ParseResult::Format(request) =
            parse_args(&["fmt", "--", "--check", "--help", "src/lib.rs"]).unwrap()
        else {
            panic!("expected fmt command")
        };
        assert_eq!(
            request.paths,
            [
                PathBuf::from("--check"),
                PathBuf::from("--help"),
                PathBuf::from("src/lib.rs")
            ]
        );
        assert!(!request.check);
        let ParseResult::Format(request) =
            parse_args(&["fmt", "--manifest-path=Cargo.toml"]).unwrap()
        else {
            panic!("expected fmt command")
        };
        assert_eq!(request.manifest_path, Some(PathBuf::from("Cargo.toml")));
    }

    #[test]
    fn rejects_unknown_or_file_mode_edition() {
        assert!(error(&["fmt", "--stdin", "--edition", "2030"]).contains("unknown Rust edition"));
        assert!(error(&["fmt", "--edition", "2021", "src"]).contains("--edition requires --stdin"));
        assert!(
            error(&["fmt", "--stdin", "--edition", "2021", "--edition=2024"])
                .contains("--edition specified more than once")
        );
    }

    #[test]
    fn rejects_fmt_stdin_conflicts() {
        assert!(error(&["fmt", "--stdin", "src"]).contains("--stdin cannot"));
        assert!(
            error(&["fmt", "--stdin", "--manifest-path", "Cargo.toml"]).contains("--stdin cannot")
        );
    }

    /// The exit paragraph states both exceptions to a run's exit cell status: an expectation's
    /// verdict, and `--output end`'s refusal of an end with no end document.
    #[test]
    fn usage_states_what_replaces_the_exit_cell_status() {
        let paragraph = USAGE
            .split_once("Exit status of run")
            .unwrap()
            .1
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ");
        for stated in [
            "A run with an expectation (--case) exits by its verdict instead, 0 met, 1 unmet and 3 inconclusive",
            "with --output end, a run whose end has no end document exits 2, whatever its own status",
        ] {
            assert!(paragraph.contains(stated), "{paragraph}");
        }
    }

    /// A usage error of a krs command prints, after its message, every shape of the command's
    /// command line that the help lists, aligned as there, and where the options are explained,
    /// not the whole help; a command line that names no command is shown every command's name.
    /// A value refused for itself is shown without the usage.
    #[test]
    fn a_usage_error_shows_the_commands_usage_lines() {
        let tail = |args: &[&str]| match parse_args(args) {
            Err(error) => command_usage_tail(error.command()),
            Ok(_) => panic!("expected a usage error for {args:?}"),
        };
        expect_test::expect![[r"
            usage: krs compare --package P --definition D LEFT RIGHT [--compare CELL,...]...
                              [--view CELL=FUNCTION]... [--observer PACKAGE:DEFINITION]
                              [--output human|json] [--view-budget POLLS]
                              [--smt-resource-limit UNITS | --smt-clock-ms MS] [--smt-retries N]
                   krs compare --package P --definition D --expect CASE ACTUAL [--output human|json]
                              [--view-budget POLLS]
                              [--smt-resource-limit UNITS | --smt-clock-ms MS] [--smt-retries N]
                   krs compare --package P --definition D --pairs FILE [--jobs N] [--output human|json]
                              [--view-budget POLLS]
                              [--smt-resource-limit UNITS | --smt-clock-ms MS] [--smt-retries N]
            `krs --help` lists every command's options and what each means"]]
        .assert_eq(&tail(&["compare", "--trace"]));
        assert_eq!(
            tail(&["emit-k", "--bogus"]),
            "usage: krs <check|expand|emit-k|build> --package PACKAGE --definition NAME [OPTIONS]\n\
             `krs --help` lists every command's options and what each means"
        );
        assert!(tail(&["fmt", "--edition"]).starts_with("usage: krs fmt [--check]"));
        // Every command, and every command name the help lists, has its own usage lines; the
        // list names `kink` only where this krs can run it.
        let general = command_usage_tail(None);
        for command in [
            "check", "expand", "emit-k", "build", "parse", "run", "search", "prove", "cases",
            "compare", "kink", "fmt",
        ] {
            let listed = general.contains(&format!(" {command},"))
                || general.contains(&format!(" {command}\n"));
            assert_eq!(
                listed,
                command != "kink" || cfg!(feature = "kink"),
                "{command}: {general}"
            );
            assert_ne!(command_usage_tail(Some(command)), general, "{command}");
        }
        assert_eq!(tail(&["frobnicate"]), general);
        assert_eq!(tail(&[]), general);
        let kink = if cfg!(feature = "kink") { "kink, " } else { "" };
        assert_eq!(
            general,
            format!(
                "usage: krs COMMAND [OPTIONS], COMMAND one of check, expand, emit-k, build, parse, \
                 run, search, cases, compare, prove, {kink}fmt\n`krs --help` lists every command \
                 and its options"
            )
        );
        #[cfg(not(feature = "kink"))]
        assert_eq!(tail(&["kink", "emit"]), general);
        // Two options that each name the case are corrected against run's usage line.
        assert_eq!(
            parse_args(&[
                "run",
                "--package",
                "p",
                "--definition",
                "d",
                "--case",
                "a.toml#x",
                "--case-name",
                "y"
            ])
            .err()
            .and_then(|error| error.command()),
            Some("run")
        );
        // A value refused for itself is not a misuse of the command line's shape.
        assert!(
            parse_args(&[
                "run",
                "--package",
                "p",
                "--definition",
                "d",
                "--case",
                "a.yaml"
            ])
            .err()
            .is_some_and(|error| matches!(error, UsageError::Value(_)) && error.command().is_none())
        );
    }

    #[test]
    fn help_and_missing_values() {
        for args in [vec!["--help"], vec!["check", "--help"], vec!["fmt", "-h"]] {
            assert!(matches!(parse_args(&args), Ok(ParseResult::Help)));
        }
        assert!(
            error(&["check", "--definition"])
                .contains("missing argument for option '--definition'")
        );
        assert!(
            error(&["fmt", "--trailing-comments"])
                .contains("missing argument for option '--trailing-comments'")
        );
    }

    #[test]
    #[expect(
        clippy::too_many_lines,
        reason = "One table of every run-family command keeps their parses side by side."
    )]
    fn parses_run_family_commands() {
        let base = ["--package", "imp", "--definition", "main"];
        let with = |verb: &str, extra: &[&str]| {
            let mut args = vec![verb];
            args.extend(base);
            args.extend(extra);
            run(&args).0.command
        };
        assert_eq!(
            with(
                "run",
                &[
                    "prog.imp",
                    "--case",
                    "cases/sum.toml",
                    "--case-name",
                    "sum",
                    "--input",
                    "regs={\"A\": 1}",
                    "--input=$PC=0x100",
                    "-c",
                    "env=.Map",
                    "-c$STORE=1",
                    "--depth",
                    "3",
                    "--trace",
                    "--coverage",
                    "--output",
                    "json"
                ]
            ),
            Command::Run(RunRequest {
                input: Some(ProgramSource::File(PathBuf::from("prog.imp"))),
                case: Some(PathBuf::from("cases/sum.toml")),
                case_name: Some("sum".to_owned()),
                inputs: vec![
                    ("regs".to_owned(), "{\"A\": 1}".to_owned()),
                    ("$PC".to_owned(), "0x100".to_owned()),
                ],
                variables: vec![
                    ("env".to_owned(), ".Map".to_owned()),
                    ("$STORE".to_owned(), "1".to_owned()),
                ],
                depth: Some(3),
                stop: StopCriterion::None,
                stop_unpaired: None,
                observe: None,
                trace: true,
                coverage: true,
                output: TermOutput::Json,
                color: ColorChoice::Auto,
                solver: krs_exec::BackendOptions::DEFAULT,
                view_budget: DEFAULT_VIEW_BUDGET,
            })
        );
        assert_eq!(
            with(
                "search",
                &[
                    "-",
                    "--case=case.json",
                    "--mode",
                    "one-step",
                    "--max-solutions",
                    "2",
                    "--color",
                    "never"
                ]
            ),
            Command::Search(SearchRequest {
                input: Some(ProgramSource::Stdin),
                case: Some(PathBuf::from("case.json")),
                case_name: None,
                inputs: Vec::new(),
                variables: Vec::new(),
                mode: SearchMode::OneStep,
                depth: None,
                max_solutions: Some(2),
                trace: false,
                output: TermOutput::Pretty,
                color: ColorChoice::Never,
                solver: krs_exec::BackendOptions::DEFAULT,
                view_budget: DEFAULT_VIEW_BUDGET,
            })
        );
        assert_eq!(
            with(
                "prove",
                &[
                    "--claim",
                    "branching",
                    "--claim",
                    "MAIN-SPEC.sum",
                    "--output=kore"
                ]
            ),
            Command::Prove(ProveRequest {
                spec_module: None,
                claims: vec!["branching".to_owned(), "MAIN-SPEC.sum".to_owned()],
                depth: None,
                output: TermOutput::Kore,
                color: ColorChoice::Auto,
                worker: false,
                solver: krs_exec::BackendOptions::DEFAULT,
                claim_timeout: None,
            })
        );
        assert_eq!(
            with("prove", &["--spec-module", "IMP-SUM-SPEC"]),
            Command::Prove(ProveRequest {
                spec_module: Some("IMP-SUM-SPEC".to_owned()),
                claims: Vec::new(),
                depth: None,
                output: TermOutput::Pretty,
                color: ColorChoice::Auto,
                worker: false,
                solver: krs_exec::BackendOptions::DEFAULT,
                claim_timeout: None,
            })
        );
        assert_eq!(
            with("parse", &["--sort", "Stmt"]),
            Command::Parse(ParseRequest {
                sort: Some("Stmt".to_owned()),
                input: ProgramSource::Stdin,
                output: TermOutput::Kast,
            })
        );
        assert_eq!(
            with("parse", &["--output", "program"]),
            Command::Parse(ParseRequest {
                sort: None,
                input: ProgramSource::Stdin,
                output: TermOutput::Program,
            })
        );
        let Command::Run(run) = with("run", &["prog.imp", "--output", "pretty"]) else {
            panic!("krs run parses as a run command");
        };
        assert_eq!(run.output, TermOutput::Pretty);
        let Command::Run(run) = with("run", &["prog.imp", "--output", "end"]) else {
            panic!("krs run parses as a run command");
        };
        assert_eq!(run.output, TermOutput::End);
        let Command::Prove(prove) = with("prove", &[]) else {
            panic!("krs prove parses as a prove command");
        };
        assert_eq!(prove.output, TermOutput::Pretty);
        assert!(!prove.worker);
        // A worker proves exactly the claims its supervisor gives it, whatever `--claim` says.
        let Command::Prove(worker) = with(
            "prove",
            &[
                "--claim",
                "sum",
                "--output",
                "jsonl",
                "--worker-protocol",
                "--worker-claim",
                "MAIN-SPEC.branching",
                "--color",
                "auto",
                "--worker-color",
                "always",
            ],
        ) else {
            panic!("krs prove parses as a prove command");
        };
        assert!(worker.worker);
        assert_eq!(worker.claims, ["MAIN-SPEC.branching"]);
        assert_eq!(worker.output, TermOutput::JsonLines);
        // A worker colours as its supervisor resolved `--color` against the supervisor's stdout.
        assert_eq!(worker.color, ColorChoice::Always);
    }

    /// `--stop-before` and `--stop-after` name stop rules by KRS item or K label, each
    /// repeatable, and `--stop-count` counts arrivals at them; a count without a stop is refused.
    #[test]
    fn parses_stop_options_and_refuses_a_count_without_a_stop() {
        let base = ["--package", "imp", "--definition", "main"];
        let with = |verb: &str, extra: &[&str]| {
            let mut args = vec![verb];
            args.extend(base);
            args.extend(extra);
            run(&args).0.command
        };
        let failure = |verb: &str, extra: &[&str]| {
            let mut args = vec![verb];
            args.extend(base);
            args.extend(extra);
            error(&args)
        };
        let stop = |extra: &[&str]| match with("run", extra) {
            Command::Run(request) => request.stop,
            other => panic!("{other:?}"),
        };
        let rules = StopRules {
            before: vec!["ppu::frame_end".to_owned()],
            after: vec!["boundary-fetch".to_owned(), "crate::tick".to_owned()],
        };
        assert_eq!(
            stop(&[
                "--stop-before",
                "ppu::frame_end",
                "--stop-after=boundary-fetch",
                "--stop-after",
                "crate::tick",
                "--stop-count",
                "60"
            ]),
            StopCriterion::Rules {
                rules,
                count: NonZeroU64::new(60).unwrap(),
                when: None,
            }
        );
        // Without --stop-count the run ends at its first stop.
        assert_eq!(
            stop(&["--stop-after", "boundary-fetch"]),
            StopCriterion::Rules {
                rules: StopRules {
                    after: vec!["boundary-fetch".to_owned()],
                    ..StopRules::default()
                },
                count: NonZeroU64::MIN,
                when: None,
            }
        );
        assert_eq!(stop(&[]), StopCriterion::None);
        assert_eq!(
            failure("run", &["--stop-count", "2"]),
            "--stop-count needs --stop-before or --stop-after: it counts arrivals at their rules"
        );
        assert_eq!(
            failure("run", &["--stop-after", "tick", "--stop-count", "0"]),
            "--stop-count `0` is not a positive integer"
        );
        assert_eq!(
            failure(
                "run",
                &[
                    "--stop-after",
                    "tick",
                    "--stop-count",
                    "2",
                    "--stop-count",
                    "3"
                ]
            ),
            "--stop-count specified more than once"
        );
        assert_eq!(
            failure("run", &["--stop-before", ""]),
            "--stop-before needs a KRS item or a K label, not an empty name"
        );
        assert_eq!(
            failure("search", &["--stop-after", "tick"]),
            "--stop-after does not apply to krs search"
        );
    }

    /// `--stop-when CELL,...=FUNCTION` with the observer `--observer` names, which needs a stop
    /// rule; `--observer` with `krs run` needs a condition.
    #[test]
    fn parses_stop_when_and_its_observer() {
        let base = ["--package", "imp", "--definition", "main"];
        let with = |verb: &str, extra: &[&str]| {
            let mut args = vec![verb];
            args.extend(base);
            args.extend(extra);
            run(&args).0.command
        };
        let failure = |verb: &str, extra: &[&str]| {
            let mut args = vec![verb];
            args.extend(base);
            args.extend(extra);
            error(&args)
        };
        let stop = |extra: &[&str]| match with("run", extra) {
            Command::Run(request) => request.stop,
            other => panic!("{other:?}"),
        };
        // --stop-when: CELL,...=FUNCTION, with the observer --observer names.
        assert_eq!(
            stop(&[
                "--stop-before",
                "crate::interrupt::boundary_fetch",
                "--stop-when",
                "pc,rom_end,rom=MooneyeBreakpoint",
                "--observer",
                "views:views"
            ]),
            StopCriterion::Rules {
                rules: StopRules {
                    before: vec!["crate::interrupt::boundary_fetch".to_owned()],
                    ..StopRules::default()
                },
                count: NonZeroU64::MIN,
                when: Some(StopWhen {
                    function: "MooneyeBreakpoint".to_owned(),
                    cells: vec!["pc".to_owned(), "rom_end".to_owned(), "rom".to_owned()],
                    observer: Some("views:views".to_owned()),
                }),
            }
        );
        assert_eq!(
            failure("run", &["--stop-when", "n=Even"]),
            "--stop-when needs --stop-before or --stop-after: it is asked at the arrivals at their rules"
        );
        for malformed in ["n", "n=", "=Even", "n,,m=Even", ",=Even"] {
            assert_eq!(
                failure("run", &["--stop-after", "tick", "--stop-when", malformed]),
                format!("--stop-when `{malformed}` must have the form CELL,...=FUNCTION"),
                "{malformed}"
            );
        }
        assert_eq!(
            failure(
                "run",
                &["--stop-after", "tick", "--observer", "views:views"]
            ),
            "--observer with krs run names the definition --stop-when's function is evaluated in; give --stop-when"
        );
        assert_eq!(
            failure("search", &["--stop-when", "n=Even"]),
            "--stop-when does not apply to krs search"
        );
    }

    /// The solver options: krs's resource-bounded default, a resource limit or a clock in its
    /// place (never both), and the retries of either; `--claim-timeout` is prove's, positive.
    #[test]
    fn solver_options_select_one_mode_and_claim_timeout_is_prove_only() {
        use krs_exec::BackendOptions;
        let base = ["--package", "imp", "--definition", "main"];
        let parsed = |verb: &str, extra: &[&str]| {
            let mut args = vec![verb];
            args.extend(base);
            args.extend(extra);
            run(&args).0.command
        };
        assert_eq!(parsed("run", &[]).solver(), BackendOptions::DEFAULT);
        assert_eq!(
            parsed(
                "search",
                &["--smt-resource-limit", "5000", "--smt-retries", "0"]
            )
            .solver(),
            BackendOptions {
                smt_budget: krs_exec::SmtBudget::Units(std::num::NonZeroU32::new(5000).unwrap()),
                smt_retry_limit: 0,
            }
        );
        let Command::Prove(prove) = parsed(
            "prove",
            &["--smt-clock-ms", "250", "--claim-timeout", "1.5"],
        ) else {
            panic!("krs prove parses as a prove command");
        };
        #[expect(
            clippy::disallowed_methods,
            reason = "`--smt-clock-ms 250` asks for the clock"
        )]
        let clocked = BackendOptions {
            smt_budget: krs_exec::SmtBudget::clock(250),
            smt_retry_limit: 3,
        };
        assert_eq!(prove.solver, clocked);
        assert_eq!(
            prove.claim_timeout,
            Some(std::time::Duration::from_millis(1500))
        );
        let failure = |verb: &str, extra: &[&str]| {
            let mut args = vec![verb];
            args.extend(base);
            args.extend(extra);
            error(&args)
        };
        assert_eq!(
            failure("run", &["--smt-resource-limit", "1", "--smt-clock-ms", "1"]),
            "--smt-resource-limit and --smt-clock-ms select different solver modes; give one"
        );
        assert_eq!(
            failure("prove", &["--smt-resource-limit", "0"]),
            "--smt-resource-limit `0` is not a positive integer"
        );
        assert_eq!(
            failure("prove", &["--smt-clock-ms", "-5"]),
            "--smt-clock-ms `-5` is not a positive integer"
        );
        assert_eq!(
            failure("prove", &["--smt-retries", "x"]),
            "--smt-retries `x` is not a non-negative integer"
        );
        assert_eq!(
            failure("prove", &["--smt-retries", "14"]),
            "14 retries double the first Z3 attempt's 370000 units past 4294967295, the largest \
             bound of one attempt; give fewer --smt-retries or a smaller --smt-resource-limit"
        );
        assert_eq!(
            parsed("prove", &["--smt-retries", "13"])
                .solver()
                .smt_retry_limit,
            13
        );
        assert_eq!(
            failure(
                "run",
                &["--smt-clock-ms", "1", "--smt-retries", "4294967295"]
            ),
            "4294967295 retries double the first Z3 attempt's 1 ms past 4294967295, the largest \
             bound of one attempt; give fewer --smt-retries or a smaller --smt-clock-ms"
        );
        for seconds in ["0", "-1", "NaN", "inf", "soon", "1e-12"] {
            assert_eq!(
                failure("prove", &["--claim-timeout", seconds]),
                format!("--claim-timeout `{seconds}` is not a positive number of seconds")
            );
        }
        assert_eq!(
            failure("run", &["--claim-timeout", "1"]),
            "--claim-timeout does not apply to krs run"
        );
        assert_eq!(
            failure("parse", &["--smt-retries", "1"]),
            "--smt-retries does not apply to krs parse"
        );
    }

    #[test]
    fn worker_options_need_the_worker_protocol_and_jsonl_is_prove_only() {
        let failure = |verb: &str, extra: &[&str]| {
            let mut args = vec![verb, "--package", "imp", "--definition", "main"];
            args.extend(extra);
            error(&args)
        };
        assert_eq!(
            failure("prove", &["--worker-claim", "sum"]),
            "--worker-claim applies only with --worker-protocol"
        );
        assert_eq!(
            failure("prove", &["--worker-color", "never"]),
            "--worker-color applies only with --worker-protocol"
        );
        assert_eq!(
            failure("run", &["--output", "jsonl"]),
            "unknown --output format `jsonl` for krs run"
        );
    }

    /// `--case-name` selects a case of the `--case` document, once, and only for run and search.
    #[test]
    fn case_name_needs_a_case_and_is_given_once() {
        let failure = |verb: &str, extra: &[&str]| {
            let mut args = vec![verb, "--package", "imp", "--definition", "main"];
            args.extend(extra);
            error(&args)
        };
        assert_eq!(
            failure("run", &["--case-name", "boot"]),
            "--case-name selects a case of the document --case names; pass --case FILE"
        );
        assert_eq!(
            failure(
                "search",
                &["--case", "a.toml", "--case-name", "x", "--case-name=y"]
            ),
            "--case-name specified more than once"
        );
        assert_eq!(
            failure("prove", &["--case-name", "x"]),
            "--case-name does not apply to krs prove"
        );
    }

    /// `--case FILE#NAME` names a case by the id `krs cases` prints, in run and search, as
    /// `--case FILE --case-name NAME` does; the name follows the first `#` after a `.toml` or
    /// `.json` file, so it may hold `#`. A `#` that no name follows and a file of another
    /// extension are refused for the value alone, without the usage; a case named both ways is a
    /// usage error of the command.
    #[test]
    fn a_case_id_names_a_case() {
        let base = ["--package", "imp", "--definition", "main"];
        let case = |verb: &str, value: &str| {
            let mut args = vec![verb];
            args.extend(base);
            args.extend(["--case", value]);
            match run(&args).0.command {
                Command::Run(run) => (run.case, run.case_name),
                Command::Search(search) => (search.case, search.case_name),
                _ => panic!("expected run or search"),
            }
        };
        assert_eq!(
            case("run", "krs/mooneye/mooneye.toml#ei_sequence"),
            (
                Some(PathBuf::from("krs/mooneye/mooneye.toml")),
                Some("ei_sequence".to_owned())
            )
        );
        assert_eq!(
            case("search", "cases/a.json#x#y"),
            (Some(PathBuf::from("cases/a.json")), Some("x#y".to_owned()))
        );
        assert_eq!(
            case("run", "cases/a#b.toml"),
            (Some(PathBuf::from("cases/a#b.toml")), None)
        );
        let refused = |extra: &[&str]| {
            let mut args = vec!["run"];
            args.extend(base);
            args.extend(extra);
            match parse_args(&args) {
                Err(UsageError::Value(message)) => message,
                Err(other) => panic!("expected a refusal of the value, got {other}"),
                Ok(_) => panic!("expected an error for {args:?}"),
            }
        };
        let mut both = vec!["run"];
        both.extend(base);
        both.extend(["--case", "a.toml#x", "--case-name", "y"]);
        assert_eq!(
            error(&both),
            "--case names the case `x` by its id (FILE#NAME) and --case-name names `y`; give the \
             case once"
        );
        assert_eq!(
            refused(&["--case", "a.toml#"]),
            "--case `a.toml#`: no case name follows `#`; give `--case a.toml#NAME`, or `--case \
             a.toml` for a document of one case"
        );
        assert_eq!(
            refused(&["--case", "cases.yaml#boot"]),
            "--case `cases.yaml#boot` names the file `cases.yaml`, which has the extension `.yaml`; \
             a case file is `.toml` or `.json`; `--case FILE#NAME` names the case NAME of a \
             `.toml` or `.json` FILE, as `krs cases` prints a case's id (or give `--case FILE \
             --case-name NAME`)"
        );
        // A `#` before which no file has an extension is part of the file's name.
        assert_eq!(
            refused(&["--case", "a#b.yaml"]),
            "--case `a#b.yaml` has the extension `.yaml`; a case file is `.toml` or `.json`; \
             `--case FILE#NAME` names the case NAME of a `.toml` or `.json` FILE, as `krs cases` \
             prints a case's id (or give `--case FILE --case-name NAME`)"
        );
    }

    /// `krs cases` takes case documents, `--jobs`, `--name`, `--output human|json`,
    /// `--view-budget` and the solver options; it refuses the options of one run.
    #[test]
    fn parses_cases_options() {
        let base = ["--package", "imp", "--definition", "main"];
        let with = |extra: &[&str]| {
            let mut args = vec!["cases"];
            args.extend(base);
            args.extend(extra);
            match run(&args).0.command {
                Command::Cases(request) => request,
                other => panic!("{other:?}"),
            }
        };
        let failure = |extra: &[&str]| {
            let mut args = vec!["cases"];
            args.extend(base);
            args.extend(extra);
            error(&args)
        };
        assert_eq!(
            with(&["a.toml", "b.json"]),
            CasesRequest {
                documents: vec![PathBuf::from("a.toml"), PathBuf::from("b.json")],
                jobs: None,
                name: None,
                output: CasesOutput::Human,
                solver: krs_exec::BackendOptions::DEFAULT,
                view_budget: DEFAULT_VIEW_BUDGET,
            }
        );
        let request = with(&[
            "a.toml",
            "--jobs",
            "2",
            "--name",
            "ld-*",
            "--output",
            "json",
            "--view-budget",
            "1500",
            "--smt-retries",
            "0",
        ]);
        assert_eq!(request.jobs, std::num::NonZeroUsize::new(2));
        assert_eq!(request.name.as_deref(), Some("ld-*"));
        assert_eq!(request.output, CasesOutput::Json);
        assert_eq!(request.view_budget, 1500);
        assert_eq!(request.solver.smt_retry_limit, 0);
        assert_eq!(
            failure(&[]),
            "krs cases needs at least one case document (.toml or .json)"
        );
        assert!(failure(&["a.txt"]).contains("not a `.toml` or `.json` file"));
        assert_eq!(
            failure(&["a.toml", "--jobs", "0"]),
            "--jobs `0` is not a positive integer"
        );
        assert_eq!(
            failure(&["a.toml", "--view-budget", "0"]),
            "--view-budget `0` is not a positive integer"
        );
        assert_eq!(
            failure(&["a.toml", "--output", "pretty"]),
            "unknown --output format `pretty` for krs cases; it prints human or json"
        );
        for option in [&["--case", "a.toml"][..], &["--depth", "1"], &["-c", "x=1"]] {
            let mut extra = vec!["a.toml"];
            extra.extend(option);
            assert_eq!(
                failure(&extra),
                format!("{} does not apply to krs cases", option[0])
            );
        }
        let mut args = vec!["run"];
        args.extend(base);
        args.extend(["--jobs", "2"]);
        assert_eq!(error(&args), "--jobs does not apply to krs run");
        let mut args = vec!["run"];
        args.extend(base);
        args.extend(["--view-budget", "2"]);
        match run(&args).0.command {
            Command::Run(request) => {
                assert_eq!(request.view_budget, 2);
            }
            other => panic!("{other:?}"),
        }
    }

    /// An end document states one run's end: neither a search's states nor a proof's, nor a
    /// parse.
    #[test]
    fn only_run_prints_an_end_document() {
        for verb in ["search", "prove", "parse"] {
            assert_eq!(
                error(&[
                    verb,
                    "--package",
                    "imp",
                    "--definition",
                    "main",
                    "--output",
                    "end"
                ]),
                format!("unknown --output format `end` for krs {verb}")
            );
        }
    }

    #[test]
    fn rejects_run_family_options_on_the_wrong_verb() {
        let base = ["--package", "imp", "--definition", "main"];
        let failure = |verb: &str, extra: &[&str]| {
            let mut args = vec![verb];
            args.extend(base);
            args.extend(extra);
            error(&args)
        };
        assert_eq!(
            failure("run", &["--max-solutions", "1"]),
            "--max-solutions does not apply to krs run"
        );
        assert_eq!(
            failure("run", &["--mode", "all"]),
            "--mode does not apply to krs run"
        );
        assert_eq!(
            failure("parse", &["--trace"]),
            "--trace does not apply to krs parse"
        );
        assert_eq!(
            failure("prove", &["--trace"]),
            "--trace does not apply to krs prove"
        );
        assert_eq!(
            failure("run", &["--claim", "x"]),
            "--claim does not apply to krs run"
        );
        assert_eq!(
            failure("check", &["--claim", "x"]),
            "--claim does not apply to krs check"
        );
        assert_eq!(
            failure("run", &["--spec-module", "IMP-SUM-SPEC"]),
            "--spec-module does not apply to krs run"
        );
        assert_eq!(
            failure("prove", &["--spec-module", "A", "--spec-module", "B"]),
            "--spec-module specified more than once"
        );
        assert_eq!(
            failure("prove", &["prog.imp"]),
            "krs prove takes no FILE argument"
        );
        assert_eq!(
            failure("check", &["prog.imp"]),
            "krs check takes no FILE argument"
        );
        assert_eq!(failure("run", &["a", "b"]), "more than one FILE given");
        assert_eq!(
            failure("run", &["--output", "program"]),
            "--output program applies only to krs parse"
        );
        assert_eq!(
            failure("search", &["--output", "none"]),
            "unknown --output format `none` for krs search"
        );
        assert_eq!(
            failure("run", &["-c", "ENV"]),
            "-c `ENV` must have the form NAME=TEXT"
        );
        assert_eq!(
            failure("run", &["--input", "pc"]),
            "--input `pc` must have the form NAME=JSON"
        );
        assert_eq!(
            failure("run", &["--input", "$=1"]),
            "--input `$=1` has an empty input name"
        );
        assert_eq!(
            failure("run", &["--case", "case.yaml"]),
            "--case `case.yaml` has the extension `.yaml`; a case file is `.toml` or `.json`"
        );
        assert_eq!(
            failure("search", &["--case", "case"]),
            "--case `case` has no extension; a case file is `.toml` or `.json`"
        );
        assert_eq!(
            failure("run", &["--case", "a.toml", "--case", "b.toml"]),
            "--case specified more than once"
        );
        assert_eq!(
            failure("prove", &["--input", "pc=1"]),
            "--input does not apply to krs prove"
        );
        assert_eq!(
            failure("parse", &["--case", "a.toml"]),
            "--case does not apply to krs parse"
        );
        assert_eq!(
            failure("run", &["--depth", "-1"]),
            "--depth `-1` is not a non-negative integer"
        );
        assert_eq!(
            failure("search", &["--mode", "=>!"]),
            "unknown search mode `=>!`"
        );
        assert!(
            failure("run", &["--backend", "llvm"])
                .starts_with("--backend does not apply to krs run")
        );
    }

    #[cfg(unix)]
    #[test]
    fn rejects_non_utf8_option_values() {
        use std::os::unix::ffi::OsStringExt;
        let args = vec![
            OsString::from("check"),
            OsString::from("--definition"),
            OsString::from_vec(vec![0xff]),
        ];
        assert!(
            matches!(parse(args), Err(UsageError::Command("check", error))
                if matches!(error.as_ref(), UsageError::Message(message) if message.contains("UTF-8")))
        );
    }

    /// The synopsis of `krs cases` lists every option it accepts and the `--output` formats.
    #[test]
    fn cases_usage_synopsis_matches_the_parser() {
        let lines: Vec<&str> = USAGE.lines().collect();
        let start = lines
            .iter()
            .position(|line| line.starts_with("  krs cases  "))
            .expect("a synopsis for krs cases");
        let synopsis = std::iter::once(lines[start])
            .chain(
                lines[start + 1..]
                    .iter()
                    .copied()
                    .take_while(|line| line.starts_with("             ")),
            )
            .collect::<Vec<_>>()
            .join(" ");
        assert!(synopsis.contains("[--output human|json]"));
        for format in ["human", "json"] {
            assert!(cases_output(Some(Path::new(format))).is_ok());
        }
        for option in exec_options(CommandKind::Cases) {
            let option = if *option == "FILE" {
                "CASES..."
            } else {
                option
            };
            assert!(
                synopsis.contains(option),
                "krs cases synopsis omits {option}"
            );
        }
    }

    /// The package and definition every `krs compare` test below names.
    const COMPARE_BASE: [&str; 4] = ["--package", "imp", "--definition", "main"];

    /// `krs compare` with `extra` after the package and definition.
    fn compare_arguments<'a>(extra: &[&'a str]) -> Vec<&'a str> {
        let mut args = vec!["compare"];
        args.extend(COMPARE_BASE);
        args.extend(extra);
        args
    }

    /// The side `path`, naming the case `name` of its document when given.
    fn side(path: &str, name: Option<&str>) -> SideFile {
        SideFile {
            path: PathBuf::from(path),
            name: name.map(str::to_owned),
        }
    }

    /// `krs compare` takes two sides, or `--expect CASE` and one; `--compare` (comma-separated,
    /// repeatable), `--view CELL=FUNCTION`, `--observer`, `--output human|json`, `--view-budget`
    /// and the solver options; the expectation states its own cells and views.
    #[test]
    fn parses_compare_options() {
        let with = |extra: &[&str]| match run(&compare_arguments(extra)).0.command {
            Command::Compare(request) => request,
            other => panic!("{other:?}"),
        };
        assert_eq!(
            with(&["a.json", "cases.toml#ld-a"]),
            CompareRequest {
                sides: CompareSides::Ends {
                    left: side("a.json", None),
                    right: side("cases.toml", Some("ld-a")),
                },
                compare: None,
                views: std::collections::BTreeMap::new(),
                observer: None,
                output: CompareOutput::Human,
                solver: krs_exec::BackendOptions::DEFAULT,
                view_budget: DEFAULT_VIEW_BUDGET,
            }
        );
        let request = with(&[
            "a.json",
            "b.toml",
            "--compare",
            "pc,bus",
            "--compare",
            "f",
            "--view",
            "bus=WritesView",
            "--observer",
            "observe:main",
            "--output",
            "json",
            "--view-budget",
            "50",
        ]);
        assert_eq!(
            request.compare,
            Some(vec!["pc".to_owned(), "bus".to_owned(), "f".to_owned()])
        );
        assert_eq!(
            request.views,
            [("bus".to_owned(), "WritesView".to_owned())].into()
        );
        assert_eq!(request.observer.as_deref(), Some("observe:main"));
        assert_eq!(request.output, CompareOutput::Json);
        assert_eq!(request.view_budget, 50);
        assert_eq!(
            with(&["--expect", "cases.toml#ld-a", "end.json"]).sides,
            CompareSides::Expectation {
                case: side("cases.toml", Some("ld-a")),
                actual: side("end.json", None),
            }
        );
        // A batch of pairs, on workers.
        let pairs = with(&["--pairs", "pairs.toml", "--jobs", "3", "--output", "json"]);
        assert_eq!(
            pairs.sides,
            CompareSides::Pairs {
                file: PathBuf::from("pairs.toml"),
                jobs: std::num::NonZeroUsize::new(3),
            }
        );
        assert_eq!(pairs.output, CompareOutput::Json);
        assert_eq!(pairs.compare, None);
        assert!(pairs.views.is_empty() && pairs.observer.is_none());
    }

    /// `krs compare` refuses a wrong number of sides, the comparison options beside
    /// `--expect`, a malformed `--view` or `--compare`, a side that is no document, and the
    /// options of other verbs; `--view` belongs to `krs compare` alone.
    #[test]
    fn refuses_compare_misuse() {
        let failure = |extra: &[&str]| error(&compare_arguments(extra));
        assert_eq!(
            failure(&["a.json"]),
            "krs compare takes two sides, LEFT and RIGHT, or --expect CASE and one side, ACTUAL; 1 given"
        );
        assert_eq!(
            failure(&["--expect", "c.toml", "a.json", "b.json"]),
            "krs compare --expect CASE checks one side, ACTUAL, against the case's expectation; 2 given"
        );
        assert!(
            failure(&["--expect", "c.toml", "a.json", "--view", "bus=V"])
                .starts_with("--compare, --view and --observer do not apply with --expect")
        );
        assert_eq!(
            failure(&["a.json", "b.json", "--observer", "o:main"]),
            "--observer names the definition the views are evaluated in, and no --view names a view"
        );
        assert_eq!(
            failure(&["a.json", "b.json", "--view", "bus"]),
            "--view `bus` must have the form CELL=FUNCTION"
        );
        assert_eq!(
            failure(&["a.json", "b.json", "--view", "bus=A", "--view", "bus=B"]),
            "--view names the cell `bus` twice; a cell has one view"
        );
        assert_eq!(
            failure(&["a.json", "b.json", "--compare", "pc,"]),
            "--compare `pc,` names an empty cell path"
        );
        assert_eq!(
            failure(&["a.json", "b.txt"]),
            "the document `b.txt` is not a `.toml` or `.json` file, which its extension says"
        );
        assert_eq!(
            failure(&["a.json", "b.json", "--output", "pretty"]),
            "unknown --output format `pretty` for krs compare; it prints human or json"
        );
        for option in [&["--case", "a.toml"][..], &["--depth", "1"]] {
            let mut extra = vec!["a.json", "b.json"];
            extra.extend(option);
            assert_eq!(
                failure(&extra),
                format!("{} does not apply to krs compare", option[0])
            );
        }
        // Workers share the pairs of a batch; a pair states its own sides and comparison.
        assert_eq!(
            failure(&["a.json", "b.json", "--jobs", "2"]),
            "--jobs applies to krs compare with --pairs, whose pairs the workers share"
        );
        for (extra, option) in [
            (&["a.json", "b.json"][..], "LEFT RIGHT"),
            (&["--expect", "a.toml"], "--expect"),
            (&["--compare", "pc"], "--compare"),
            (&["--view", "bus=V"], "--view"),
            (&["--observer", "o:main"], "--observer"),
        ] {
            let mut arguments = vec!["--pairs", "pairs.toml"];
            arguments.extend(extra);
            assert_eq!(
                failure(&arguments),
                format!(
                    "{option} does not apply with --pairs: each pair of the file states its sides and its `compare`, `views` and `observer`"
                )
            );
        }
        assert_eq!(
            failure(&["--pairs", "pairs.txt"]),
            "--pairs `pairs.txt` is not a `.toml` or `.json` file, which its extension says"
        );
        let mut args = vec!["run"];
        args.extend(COMPARE_BASE);
        args.extend(["--view", "bus=V"]);
        assert_eq!(error(&args), "--view does not apply to krs run");
    }

    /// The three synopses of `krs compare` list every option it accepts and the `--output` formats.
    #[test]
    fn compare_usage_synopsis_matches_the_parser() {
        let lines: Vec<&str> = USAGE.lines().collect();
        let mut synopsis = String::new();
        let mut index = 0;
        while index < lines.len() {
            if lines[index].starts_with("  krs compare ") {
                synopsis.push_str(lines[index]);
                index += 1;
                while index < lines.len() && lines[index].starts_with("             ") {
                    synopsis.push(' ');
                    synopsis.push_str(lines[index]);
                    index += 1;
                }
            } else {
                index += 1;
            }
        }
        assert!(synopsis.contains("--expect CASE ACTUAL"), "{synopsis}");
        assert!(synopsis.contains("[--output human|json]"), "{synopsis}");
        for option in exec_options(CommandKind::Compare) {
            let option = if *option == "FILE" {
                "LEFT RIGHT"
            } else {
                option
            };
            assert!(
                synopsis.contains(option),
                "krs compare synopsis omits {option}"
            );
        }
    }

    /// The synopsis of each run-family command lists exactly the `--output`
    /// formats the parser accepts for it and every option it accepts.
    #[test]
    fn usage_synopsis_matches_the_parser() {
        let lines: Vec<&str> = USAGE.lines().collect();
        for kind in [
            CommandKind::Parse,
            CommandKind::Run,
            CommandKind::Search,
            CommandKind::Prove,
        ] {
            let head = format!("  krs {:<6} ", kind.as_str());
            let start = lines
                .iter()
                .position(|line| line.starts_with(&head))
                .unwrap_or_else(|| panic!("no synopsis for krs {}", kind.as_str()));
            let synopsis = std::iter::once(lines[start])
                .chain(
                    lines[start + 1..]
                        .iter()
                        .copied()
                        .take_while(|line| line.starts_with("             ")),
                )
                .collect::<Vec<_>>()
                .join(" ");
            let listed: Vec<&str> = synopsis
                .split("[--output ")
                .nth(1)
                .and_then(|rest| rest.split(']').next())
                .unwrap_or_else(|| panic!("no --output in the krs {} synopsis", kind.as_str()))
                .split('|')
                .collect();
            for format in ["pretty", "program", "kast", "json", "jsonl", "kore", "none"] {
                assert_eq!(
                    term_output(kind, Some(PathBuf::from(format))).is_ok(),
                    listed.contains(&format),
                    "krs {} synopsis and parser disagree on --output {format}",
                    kind.as_str()
                );
            }
            for option in exec_options(kind) {
                if HIDDEN_OPTIONS.contains(option) {
                    assert!(
                        !USAGE.contains(option),
                        "the usage shows the hidden {option}"
                    );
                    continue;
                }
                let option = if *option == "FILE" { "FILE|-" } else { option };
                assert!(
                    synopsis.contains(option),
                    "krs {} synopsis omits {option}",
                    kind.as_str()
                );
            }
        }
    }
}
