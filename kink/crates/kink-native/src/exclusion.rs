//! Exclusions: the conditions under which a run is no evidence for any comparison, whatever its
//! leaves say (re-pin R0b, `draft/tasks/repin-501f18b9`). Each makes the whole side of a test
//! Unknown, every oracle slot at once, so no other slot of the same test can still distinguish and
//! no outcome record is written for it. kink-campaign applies them when it judges a run
//! (`Runtime::judge`), on the baseline and on every mutant side, on a live run and on a stored
//! baseline run a `BaselineSession` reuses alike, before any evidence leaves the runner.
//!
//! - [`Exclusion::StackStop`]: the run counted a stop for lack of native stack (`stackStops`,
//!   finding A-06, k-rust KINK-06/5). A dismissed stop leaves no leaf trace: the leaf can be less
//!   simplified, or a step decided without a refinement, and whether a stop happens depends on the
//!   thread's stack and on other threads.
//! - [`Exclusion::LoadStackStop`]: the load of the side's definition counted a stop for lack of
//!   stack in its discharge of rewrite-rule definedness (`discharge_counts().stack_stops`) or in
//!   its critical-pair check (`value_claims().counts().condition_stack_stops`), read through
//!   `select_definition` on the backend that runs (finding A-08, KINK-06/4): the loaded rewrite
//!   theory and its value claims are then not a function of the definition. Budget stops are a
//!   function of the definition and only withdraw claims, so they exclude nothing.
//! - [`Exclusion::ContradictedClaim`]: a leaf is an undefined step that falsifies a trusted claim
//!   (re-pin decision 2, finding A-13): k-rust names a contradicted `total` claim
//!   (`contradictedTotal`), or a `Trivial` leaf's rule carries `preserves-definedness`. The
//!   definition is inconsistent there, and any verdict follows from an inconsistent theory. In both
//!   modalities the `Trivial` leaf of an undefined step is the configuration the step was taken
//!   from, naming the step's rule; a state set never merges it, and keeps one per distinct
//!   configuration and depth, which every converging path takes alike, so a leaf contradiction on a
//!   state set is one on the path set of the same request (fz26 KINK-PATHSET-FALLBACK). The one
//!   leaf that names another rule is a remainder its own normalization refutes: it names the rule
//!   that produced its parent, which, when that parent is the merged state itself, is under a state
//!   set the witness path's only (k-rust `docs/backend-port.md`), so the `preserves-definedness`
//!   reading below can differ between the modalities there. It never reads a contradiction of that
//!   rule's claim (D40): a remainder takes no step, and its leaf is `Trivial` only when one of its
//!   own `\ceil` or `Defined` constraints is refuted, which comes from its parent's constraints or
//!   its own negated condition; a `preserves-definedness` step adds no definedness obligation, and
//!   its `requires` and `ensures` are outside its claim, so what the remainder refutes either
//!   restricted the producer's instances before its step or is not the producer's result. Since
//!   re-pin adoption A-1 also any record on the run's `contradictedClaims` list, observed by the
//!   run or by the load of its definition (`observedIn: load`, decision D-6), ground or not
//!   ([`RunFacts::contradicted_claims`]): the list holds what no leaf carries, a candidate a
//!   defined sibling covered and a state a state-set merge absorbed (`docs/compatibility.md` at
//!   0068938b1, 1659), so a comparison of complete sets needs it empty; a load record is on every
//!   run's list, so it excludes every test of its definition. On a ground run any record excludes,
//!   so `ground` is not read: a non-ground record there arises only from a mark, a refusal, an
//!   unsupported hook or a non-ground record, each excluded on its own (compat 1661-1668). An empty
//!   list says nothing about a symbolic run (compat 1661), whose tests stay on the trusted-baseline
//!   premise, and the leaf rule does not close that gap: a `preserves-definedness` claim false at a
//!   symbolic instance that only a later step narrows to leaves neither a record nor a leaf naming
//!   the rule, in either modality, so such a run is not excluded (KINK-PD-SYMBOLIC-INSTANCE, a
//!   known gap pinned by `tests/exclusion.rs`
//!   `known_gap_a_pd_claim_false_at_a_narrowed_symbolic_instance_is_not_excluded`). Only a leaf's
//!   contradiction ([`DefinitionExclusions::contradiction_on_a_leaf`]) is the per-test case for
//!   which admission keeps a baseline (kink-campaign `admit`); a record on the list alone refuses a
//!   baseline as any other exclusion does, so no refusal relaxes.
//! - [`Exclusion::ImplementationChosenValue`] (re-pin adoption A-1): the run read a value the
//!   definition leaves open, on k-rust's `implementationChosenValues` list
//!   ([`RunFacts::implementation_chosen_values`]): every class value k-rust's evaluator takes in
//!   `Execution` mode is noted there, the initial state's normalization and work that ended on no
//!   leaf included (compat 1778-1801). Decision 1's census still stands beside it; the list adds a
//!   run that read an open value through an equation the census does not see (a prelude one).
//! - [`Exclusion::ImplementationChosenHook`]: the definition references a hook for which k-rust
//!   chooses a value the definition leaves open (re-pin decision 1, findings D-10, E-10, E-11):
//!   kills are relative to the definition, not to k-rust's model of it. The hooks are k-rust's
//!   own list, those whose value k-rust's builtin files (`domains.md`, `substitution.md`,
//!   `json.md`, `timer.md`, `ffi.md`, `unification.k`) leave to the backend, the implementation
//!   or the environment, and those k-rust evaluates that no builtin file documents
//!   ([`IMPLEMENTATION_CHOSEN_HOOKS`], [`DOMAINS_OPEN_HOOKS`], [`BUILTIN_OPEN_HOOKS`],
//!   [`UNDOCUMENTED_EVALUATED_HOOKS`]). The census reads the definition's own sentences and every
//!   rewrite rule whatever its source: kompile copies the prelude's stream rules into a definition
//!   with stream cells, keeping their prelude source. Since KINK-CENSUS-RUNLIST (fz26) it reads
//!   only the open hooks k-rust evaluates without a run-level record ([`census_hook`]): an open
//!   hook an execute request cannot evaluate (a console operation, or one k-rust has no
//!   evaluator for, [`RUN_LIST_HOOKS`]) takes no value in a run, and an application of one whose
//!   value the run needs is on the run's `unsupportedHooks` wherever it sits, which excludes that
//!   run ([`Exclusion::UnsupportedHook`]). So the prelude's stream rules (`#getc`, `#write`,
//!   `Float2String`) no longer exclude a definition with stream cells; a run that reaches one
//!   with constructor-like arguments is excluded by its list.
//! - [`Exclusion::ShortCircuitReading`]: the run's result can depend on whether `andBool`,
//!   `orBool`, `impliesBool`, `#if`, `andThenBool` or `orElseBool` skip an operand that may be
//!   undefined
//!   (re-pin decision 1 applied to domains.md lines 1115-1117 and 2314-2317; R0c review 1 minor):
//!   k-rust evaluates every operand (an application is strict in all its arguments, k-rust
//!   `deferred.rs`), so such a step is undefined where a short-circuiting backend gives a value.
//!   A `Trivial` leaf of a rewrite rule whose right-hand side applies one makes the run
//!   excluded; a rule whose condition depends on one, or whose right-hand side applies a
//!   function whose condition does, gives no leaf signal (the rule is just not applied), so the
//!   definition is excluded ([`DefinitionExclusions::short_circuit_conditions`]). Since re-pin
//!   R0c-fix-2 a rule whose right-hand side applies one over an operand that may be undefined
//!   excludes the definition too ([`DefinitionExclusions::short_circuit_results`]): its
//!   undefined candidate beside a defined same-priority sibling leaves no leaf. "May be
//!   undefined" is read on the definition the side runs, a mutant's after the claims its edit
//!   leaves unbacked are removed (a function whose `total` was removed is partial there). Since
//!   KINK-SC-DEFINED (fz26) a skippable operand counts only where one of its possibly undefined
//!   applications (of a partial or reading-dependent function) is evaluated by no operand that
//!   runs whenever it is skipped: where it is, both readings are undefined together (the
//!   must/may rule of `ShortCircuitAnalysis::direct`, which reads no guard's truth; a recursive
//!   function's own calls are read under premise A1, termination). It clears the prelude's
//!   `findChar` and so the stdin stream rules over it.
//! - [`Exclusion::AllowanceRefusal`]: a leaf reports a hook left unevaluated whose refusal reads
//!   the process's memory allowance (Execute promise exclusion, findings A-07, B-02, B-07): the
//!   result is a function of the host, not of the inputs a key names. Since re-pin adoption A-1
//!   also any entry of the run's `allowanceRefusals` list ([`RunFacts::allowance_refusals`]): a
//!   refusal inside an attempt that was undone or an equation passed over can steer a result and
//!   leave no diagnostic (compat 92), and a result whose list is empty is the result under every
//!   allowance of at least as many bytes (compat 853).
//! - [`Exclusion::UnsupportedHook`] (re-pin adoption A-1): the run or its load left an application
//!   unevaluated as an unsupported hook (`unsupportedHooks`, [`RunFacts::unsupported_hooks`]),
//!   whatever became of the work that met it (compat 92).
//! - [`Exclusion::EqualsCondition`]: a rewrite rule or equation of the definition has a condition
//!   that equates two terms (K `{ A #Equals B }`), which k-rust 501f18b9 names as a gap of its own
//!   answers when the terms may be undefined ("Two gaps remain", `docs/compatibility.md`): such
//!   a definition is excluded (re-pin R0c-fix-3, R0c-fix-2 review minor 3). Since re-pin
//!   R0c-fix-4 every axiom's antecedents and `ensures` are read, whatever its left-hand side, and
//!   since re-pin R0-tail a rewrite rule's `ensures` under the `\exists` kompile emits for an
//!   existential variable of its right-hand side too (every `\equals` of a rewrite rule's
//!   right-hand side is read). The algorithm is named by [`DEFINITION_EXCLUSION_VERSION`] in the
//!   campaign manifest.
//!
//! Every exclusion is read per test: it makes that test's comparison unknown, and a kill by
//! another test, whose runs it does not touch, stands (decision 2's scope, Sebastien,
//! 2026-10-17: where a claim is false only at inputs the killing test never reaches, weakening
//! it there gives a definition with models in which the killing test behaves the same).
//!
//! A definition that holds an axiom rooted at a collection role symbol is not excluded as a whole,
//! but none of its collection terms is a terminal value (finding C-10,
//! [`DefinitionExclusions::collections_trusted`]).

use std::collections::BTreeSet;

use k_rust::backend::BackendDiagnosticOutput;
use k_rust::kore::{
    ast::{Attributes, Definition, Pattern, Sentence},
    walk,
};
use k_rust::names::KoreAttribute;
use k_rust_backend::{
    confluence::ViolationKind,
    definition::BackendDefinition,
    rule::TermIndex,
    term::{CollectionMetadata, FunctionType, SymbolType},
};

use crate::execution::{AdaptedExecution, AdaptedLeaf, HaltClass, RunFacts};

/// The version of the definition exclusions ([`DefinitionExclusions`], with the hook lists and
/// the scans it reads): whether a comparison is made at all depends on it, so kink's semantics
/// identity names it (kink-campaign `identity`), and every store keys on that identity: the
/// campaign manifest's `kink` member, kink-flow's result key and its tier-1 context (packet
/// CACHE-ID). Bump it whenever this module changes what it excludes. v1 (re-pin R0-tail, R0c-fix-4 review minor 4): the first
/// named version, with the `ensures` of a rewrite rule read under the `\exists` of its existential
/// variables. v2 (re-pin adoption A-1): a run is also excluded by k-rust's run-level lists, any
/// entry of `contradictedClaims` (`contradicted-claim`), `implementationChosenValues`
/// (`implementation-chosen-value`), `allowanceRefusals` (`allowance-refusal`) or
/// `unsupportedHooks` (`unsupported-hook`). v3 (fz26 KS-PIN-SCDEF and KINK-CENSUS-RUNLIST): a
/// short-circuit operator is flagged only when a term its skipped operand may leave undefined is
/// not one another operand must evaluate (the must/may rule), and the definition-level census
/// reads only the open hooks k-rust evaluates without a record ([`census_hook`]); the others
/// ([`RUN_LIST_HOOKS`]) are judged per run through `unsupportedHooks`. Both only narrow what is
/// excluded.
pub const DEFINITION_EXCLUSION_VERSION: &str = "kink-native/definition-exclusion/v3";

/// The hooks for which k-rust 8f8ad57c5 says it may compute a value the definition leaves open,
/// exactly the hooks for which its classifier `chosen_value` (`k-rust-backend/src/builtin.rs`;
/// KINK-17/2) can return `Some`: the match arms (`MAP.keys_list`, `MAP.values`, `SET.set2list`,
/// `MAP.choice`, `SET.choice`, `STRING.base2string`, `SUBSTITUTION.substOne`, `IO.read`), the six
/// Float operations `float::mixed_destination` reads (`BinaryOperation::of`), `FLOAT.sign`
/// (`float::nan_sign`) and `FLOAT.min`/`FLOAT.max` (`float::signed_zeros`, already among the six).
/// Pinned against the k-rust source, and the source text of those functions by digest, by the
/// kink-native test `implementation_chosen_hooks_are_k_rusts`.
///
/// Re-pin L-1 (`draft/tasks/repin-58720d2e`): at 501f18b9 the classifier was
/// `implementation_chosen_in`, with the first five arms and the Float helpers. KINK-17/2 (k-rust
/// 1691bf61c, review 25fa4ccc9, merge 978d30070) added `STRING.base2string` (letter case),
/// `SUBSTITUTION.substOne` (fresh names) and `IO.read` (read count). The census held all three
/// already, as kink-side hooks ([`DOMAINS_OPEN_HOOKS`], [`BUILTIN_OPEN_HOOKS`]); they moved here,
/// so [`IMPLEMENTATION_CHOSEN_HOOKS`] is the same set in another order.
pub const K_RUST_IMPLEMENTATION_CHOSEN_HOOKS: &[&str] = &[
    "MAP.keys_list",
    "MAP.values",
    "SET.set2list",
    "MAP.choice",
    "SET.choice",
    "STRING.base2string",
    "SUBSTITUTION.substOne",
    "IO.read",
    "FLOAT.add",
    "FLOAT.sub",
    "FLOAT.mul",
    "FLOAT.div",
    "FLOAT.min",
    "FLOAT.max",
    "FLOAT.sign",
];

/// The hooks whose value k-rust's prelude text (`k-rust/builtin/domains.md` at 501f18b9) leaves
/// to the backend, the implementation or the environment, beyond k-rust's own list: kink-side
/// additions to decision 1's census (`BYTES.string2bytes` since re-pin R0b, finding E-11; the
/// rest from re-pin R0c's sweep of domains.md, R0b review 1 major 2). Each is given with the
/// domains.md lines and a phrase of them that says so; the kink-native test
/// `domains_md_leaves_these_hook_values_open` checks every phrase against the file and pins the
/// file's digest, so a re-pin sweeps it again.
///
/// - The pair `String2Bytes`/`Bytes2String` names no encoding (domains.md names one only for
///   `encodeBytes`/`decodeBytes`, which take it as an argument, line 2012); k-rust reads each
///   byte as the code point of the same number, "its chosen reading" (`bytes.rs:64-73`).
/// - `Float2String`'s string is "determined by the backend"; with a format it is what
///   `mpfr_printf` gives.
/// - `RangeMap`'s `choice` is "arbitrarily chosen", and its `keys_list` and `values` state no
///   order, as `Map`'s, which k-rust names.
/// - `randInt`/`srandInt` are pseudorandom on concrete backends and uninterpreted on symbolic
///   ones; the deprecated String hooks and the `K-REFLECTION` hooks that read the process or
///   the environment are "largely unsupported"; and every I/O hook returns what "the underlying
///   system call" gives.
///
/// `Base2String`'s letter case ("determined by the backend", domains.md 1829-1831) and the count
/// a `#read` returns ("fewer characters than requested", 2548-2549) were kink-side hooks until
/// re-pin L-1; k-rust's classifier names both since KINK-17/2, so they are on
/// [`K_RUST_IMPLEMENTATION_CHOSEN_HOOKS`] (each hook is on one list).
///
/// Not added, because domains.md fixes the value: `encodeBytes`/`decodeBytes` (a named
/// encoding), the logging hooks (`IO.log`, `IO.logString`, `IO.traceTerm`, which return `.K`),
/// `#sort` and `getsymbol` (read off the term), `Float2Int`, `replace` with a negative count and
/// `memsetBytes` out of range (undefined there, which is no value; k-rust leaves them
/// unevaluated), and the Float and `MInt` operations (IEEE 754 and two's-complement results).
pub const DOMAINS_OPEN_HOOKS: &[(&str, &str, &str)] = &[
    (
        "BYTES.string2bytes",
        "2089-2095",
        "You can convert between a `Bytes` and a `String`",
    ),
    (
        "BYTES.bytes2string",
        "2089-2095",
        "You can convert between a `Bytes` and a `String`",
    ),
    (
        "STRING.float2string",
        "1801-1804",
        "by `Float2String` is determined by the backend",
    ),
    (
        "STRING.floatFormat",
        "1806-1810",
        "is one which results directly from passing that `format` to `mpfr_printf`",
    ),
    (
        "STRING.category",
        "1877-1878",
        "String hooks which are deprecated and only are supported",
    ),
    (
        "STRING.directionality",
        "1877-1878",
        "String hooks which are deprecated and only are supported",
    ),
    (
        "STRING.uuid",
        "1877-1878",
        "String hooks which are deprecated and only are supported",
    ),
    (
        "INT.rand",
        "1347-1349",
        "on concrete backends, compute a pseudorandom integer",
    ),
    (
        "INT.srand",
        "1347-1349",
        "on concrete backends, compute a pseudorandom integer",
    ),
    (
        "RANGEMAP.choice",
        "676-679",
        "You can get an arbitrarily chosen key of a `RangeMap`",
    ),
    (
        "RANGEMAP.keys_list",
        "628-631",
        "You can get a `List` of all the ranges in a `RangeMap`",
    ),
    (
        "RANGEMAP.values",
        "646-649",
        "You can get a `List` of all values in a `RangeMap`",
    ),
    (
        "KREFLECTION.configuration",
        "2366-2368",
        "unsupported in modern K",
    ),
    ("KREFLECTION.fresh", "2366-2368", "unsupported in modern K"),
    ("KREFLECTION.getenv", "2366-2368", "unsupported in modern K"),
    (
        "KREFLECTION.kompiledDir",
        "2366-2368",
        "unsupported in modern K",
    ),
    (
        "KREFLECTION.argv",
        "2389-2390",
        "meaningful only for the purposes of compilation to a binary",
    ),
    (
        "KREFLECTION.printKORE",
        "2366-2368",
        "unsupported in modern K",
    ),
    (
        "IO.open",
        "2413-2414",
        "corresponding to the `errno` returned by the underlying system call",
    ),
    (
        "IO.tell",
        "2413-2414",
        "corresponding to the `errno` returned by the underlying system call",
    ),
    (
        "IO.seek",
        "2413-2414",
        "corresponding to the `errno` returned by the underlying system call",
    ),
    (
        "IO.seekEnd",
        "2413-2414",
        "corresponding to the `errno` returned by the underlying system call",
    ),
    (
        "IO.getc",
        "2413-2414",
        "corresponding to the `errno` returned by the underlying system call",
    ),
    (
        "IO.putc",
        "2413-2414",
        "corresponding to the `errno` returned by the underlying system call",
    ),
    (
        "IO.write",
        "2413-2414",
        "corresponding to the `errno` returned by the underlying system call",
    ),
    (
        "IO.close",
        "2413-2414",
        "corresponding to the `errno` returned by the underlying system call",
    ),
    (
        "IO.lock",
        "2413-2414",
        "corresponding to the `errno` returned by the underlying system call",
    ),
    (
        "IO.unlock",
        "2413-2414",
        "corresponding to the `errno` returned by the underlying system call",
    ),
    (
        "IO.accept",
        "2413-2414",
        "corresponding to the `errno` returned by the underlying system call",
    ),
    (
        "IO.shutdownWrite",
        "2413-2414",
        "corresponding to the `errno` returned by the underlying system call",
    ),
    (
        "IO.time",
        "2604-2605",
        "You can get the current time in seconds",
    ),
    (
        "IO.system",
        "2413-2414",
        "corresponding to the `errno` returned by the underlying system call",
    ),
    (
        "IO.mkstemp",
        "2413-2414",
        "corresponding to the `errno` returned by the underlying system call",
    ),
    (
        "IO.remove",
        "2413-2414",
        "corresponding to the `errno` returned by the underlying system call",
    ),
];

/// The hooks whose value k-rust's builtin files other than `domains.md`
/// (`k-rust/builtin/*.md` and `unification.k` at 501f18b9) leave to the backend, the
/// implementation or the environment: kink-side additions to decision 1's census from re-pin
/// R0c-fix-1's sweep of every builtin file (R0c review 1 major 3). Each is given as its file, the
/// lines and a phrase of them; the kink-native test `builtin_files_leave_these_hook_values_open`
/// checks every phrase, pins every builtin file's digest, and checks that every hook those files
/// declare `impure` is on the list or named below with the reason it is not.
///
/// - `substitution.md`: capture-avoiding substitution renames bound variables, and "the rewriter
///   will automatically assign unique names" with "a unique integer suffix", which "might be
///   different" depending on when rewriting halts; k-rust mints `{base}{n}` with its own counter
///   (`FreshNames::mint`), so an alpha-equivalent result can differ in k-rust's suffix alone.
///   `substMany` is listed here; `substOne` is on [`K_RUST_IMPLEMENTATION_CHOSEN_HOOKS`] since
///   re-pin L-1, as k-rust's classifier names it (`fresh-name`, KINK-17/2).
/// - `unification.k`: seven hooks declared `impure` with no stated value (renaming, variable
///   sets, freezing, unifiability); the file leaves every value to the implementation.
/// - `json.md`: `JSON2String` names no layout of the JSON text it gives, and `String2JSON` no
///   reading of a JSON number as an `Int` or a `Float`.
/// - `timer.md`: `timerStart`/`timerStop` state no value; a timer reads the host's clock.
/// - `ffi.md`: native calls, symbol and buffer addresses (`#address` is "unspecified" outside
///   `#alloc`), allocated memory and native reads and writes are the host's.
///
/// Not added, because the file fixes the value: `FFI.free` ("returns `.K`"), the `RAT` hooks
/// (rational arithmetic in a stated canonical form), `FLOAT.rat2float` (IEEE 754 rounding, as
/// the other Float hooks), and the sort hooks of `kast.md` (`K.K`, `K.KItem`, no value). Fresh
/// constants (`!X`, `kast.md` 172-176, and `freshKVar`) are not a hook: the definition's
/// compiled `<generatedCounter>` cell and its `freshGenerator` rules fix them, so they are a
/// premise about the compiled definition, not a value the backend chooses.
pub const BUILTIN_OPEN_HOOKS: &[(&str, &str, &str, &str)] = &[
    (
        "substitution.md",
        "SUBSTITUTION.substMany",
        "83-88",
        "the rewriter will automatically assign unique names",
    ),
    (
        "unification.k",
        "UNIFICATION.renameVariables",
        "6-6",
        "hook(UNIFICATION.renameVariables), impure",
    ),
    (
        "unification.k",
        "UNIFICATION.variables",
        "8-8",
        "hook(UNIFICATION.variables), impure",
    ),
    (
        "unification.k",
        "UNIFICATION.metaVariables",
        "10-10",
        "hook(UNIFICATION.metaVariables), impure",
    ),
    (
        "unification.k",
        "UNIFICATION.variablesMap",
        "12-12",
        "hook(UNIFICATION.variablesMap), impure",
    ),
    (
        "unification.k",
        "UNIFICATION.rename",
        "14-14",
        "hook(UNIFICATION.rename), impure",
    ),
    (
        "unification.k",
        "UNIFICATION.freezeVariables",
        "16-16",
        "hook(UNIFICATION.freezeVariables), impure",
    ),
    (
        "unification.k",
        "UNIFICATION.unifiable",
        "18-18",
        "hook(UNIFICATION.unifiable), impure",
    ),
    (
        "json.md",
        "JSON.json2string",
        "34-37",
        "can also be converted to a `String` using the `JSON2String` function",
    ),
    (
        "json.md",
        "JSON.string2json",
        "8-12",
        "utilizing K's syntax for strings,",
    ),
    (
        "timer.md",
        "TIMER.timerStart",
        "7-7",
        "[function, hook(TIMER.timerStart)]",
    ),
    (
        "timer.md",
        "TIMER.timerStop",
        "9-9",
        "[function, hook(TIMER.timerStop)]",
    ),
    (
        "ffi.md",
        "FFI.call",
        "77-82",
        "returns the return value of the function as a `Bytes`.",
    ),
    (
        "ffi.md",
        "FFI.call_variadic",
        "90-97",
        "type of the function, and returns the return value of the function as a",
    ),
    (
        "ffi.md",
        "FFI.address",
        "125-126",
        "a mechanism to look up any function symbol and return",
    ),
    (
        "ffi.md",
        "FFI.alloc",
        "148-150",
        "will allocate `Size` bytes with an alignment",
    ),
    (
        "ffi.md",
        "FFI.bytes_address",
        "161-165",
        "the return value is unspecified",
    ),
    (
        "ffi.md",
        "FFI.read",
        "186-189",
        "will read native memory at address `Addr` into `Mem`",
    ),
    (
        "ffi.md",
        "FFI.write",
        "197-203",
        "will write the contents of `Mem` to native memory at",
    ),
];

/// The hooks k-rust 501f18b9's builtin dispatch evaluates that no builtin file it ships declares
/// (re-pin R0c-fix-2, R0c-fix-1 review minor): the user declares them, and no text of the
/// definition specifies their value, so a kill through one is relative to k-rust's evaluator,
/// not to the definition (decision 1). The kink-native test
/// `evaluated_hooks_no_builtin_file_documents_are_open` derives this list from the dispatch
/// source (every hook literal of a match arm in k-rust-backend `builtin.rs` and `builtin/`) and
/// the builtin files, and pins both lists: a re-pin that adds an evaluated hook fails it.
pub const UNDOCUMENTED_EVALUATED_HOOKS: &[&str] = &[
    "HASH.keccak256",
    "HASH.ripemd160",
    "HASH.sha256",
    "HASH.sha3_256",
    "KRYPTO.bn128add",
    "KRYPTO.bn128ate",
    "KRYPTO.bn128g2valid",
    "KRYPTO.bn128mul",
    "KRYPTO.bn128valid",
    "KRYPTO.ecdsaPubKey",
    "KRYPTO.ecdsaRecover",
    "KRYPTO.keccak256",
    "KRYPTO.keccak256raw",
    "KRYPTO.ripemd160",
    "KRYPTO.ripemd160raw",
    "KRYPTO.sha256",
    "KRYPTO.sha256raw",
    "KRYPTO.sha3256",
    "KRYPTO.sha512_256raw",
    "SECP256K1.ecdsaRecover",
];

/// Decision 1's census hooks: [`K_RUST_IMPLEMENTATION_CHOSEN_HOOKS`], the hooks of
/// [`DOMAINS_OPEN_HOOKS`], those of [`BUILTIN_OPEN_HOOKS`] and [`UNDOCUMENTED_EVALUATED_HOOKS`], in
/// that order (the kink-native test `implementation_chosen_hooks_are_k_rusts` checks that it is
/// exactly their union).
pub const IMPLEMENTATION_CHOSEN_HOOKS: &[&str] = &[
    "MAP.keys_list",
    "MAP.values",
    "SET.set2list",
    "MAP.choice",
    "SET.choice",
    "STRING.base2string",
    "SUBSTITUTION.substOne",
    "IO.read",
    "FLOAT.add",
    "FLOAT.sub",
    "FLOAT.mul",
    "FLOAT.div",
    "FLOAT.min",
    "FLOAT.max",
    "FLOAT.sign",
    "BYTES.string2bytes",
    "BYTES.bytes2string",
    "STRING.float2string",
    "STRING.floatFormat",
    "STRING.category",
    "STRING.directionality",
    "STRING.uuid",
    "INT.rand",
    "INT.srand",
    "RANGEMAP.choice",
    "RANGEMAP.keys_list",
    "RANGEMAP.values",
    "KREFLECTION.configuration",
    "KREFLECTION.fresh",
    "KREFLECTION.getenv",
    "KREFLECTION.kompiledDir",
    "KREFLECTION.argv",
    "KREFLECTION.printKORE",
    "IO.open",
    "IO.tell",
    "IO.seek",
    "IO.seekEnd",
    "IO.getc",
    "IO.putc",
    "IO.write",
    "IO.close",
    "IO.lock",
    "IO.unlock",
    "IO.accept",
    "IO.shutdownWrite",
    "IO.time",
    "IO.system",
    "IO.mkstemp",
    "IO.remove",
    "SUBSTITUTION.substMany",
    "UNIFICATION.renameVariables",
    "UNIFICATION.variables",
    "UNIFICATION.metaVariables",
    "UNIFICATION.variablesMap",
    "UNIFICATION.rename",
    "UNIFICATION.freezeVariables",
    "UNIFICATION.unifiable",
    "JSON.json2string",
    "JSON.string2json",
    "TIMER.timerStart",
    "TIMER.timerStop",
    "FFI.call",
    "FFI.call_variadic",
    "FFI.address",
    "FFI.alloc",
    "FFI.bytes_address",
    "FFI.read",
    "FFI.write",
    "HASH.keccak256",
    "HASH.ripemd160",
    "HASH.sha256",
    "HASH.sha3_256",
    "KRYPTO.bn128add",
    "KRYPTO.bn128ate",
    "KRYPTO.bn128g2valid",
    "KRYPTO.bn128mul",
    "KRYPTO.bn128valid",
    "KRYPTO.ecdsaPubKey",
    "KRYPTO.ecdsaRecover",
    "KRYPTO.keccak256",
    "KRYPTO.keccak256raw",
    "KRYPTO.ripemd160",
    "KRYPTO.ripemd160raw",
    "KRYPTO.sha256",
    "KRYPTO.sha256raw",
    "KRYPTO.sha3256",
    "KRYPTO.sha512_256raw",
    "SECP256K1.ecdsaRecover",
];

/// The open hooks ([`IMPLEMENTATION_CHOSEN_HOOKS`]) that the definition-level census leaves to
/// the run's `unsupportedHooks` list (KINK-CENSUS-RUNLIST, fz26): those an execute request cannot
/// evaluate, because it supplies no console (the console operations, k-rust's inventory class
/// `execution_only`) or because k-rust has no evaluator for them (its inventory class
/// `unsupported`, its `NOT_EVALUATED` list, or a namespace it does not evaluate), less those with
/// a k-rust `chosen_value` class ([`K_RUST_IMPLEMENTATION_CHOSEN_HOOKS`]: `IO.read`, a console
/// operation of class `read-count`, stays in the census).
///
/// Why the census need not read them: such a hook takes no value in a run kink requests. An
/// application of one on constructor-like arguments whose value the run needs is on the run's
/// `unsupportedHooks`, wherever it sits (a right-hand side, a condition, a left-hand-side match
/// that fails, an equation passed over, an undone attempt, the load) and whatever became of the
/// work that met it ([`Exclusion::UnsupportedHook`]); on symbolic arguments it stays unevaluated,
/// so it denotes some value of its sort, an end that holds it is no terminal value, and a branch
/// on it is a branch the definition has; a comparison that sorts or heads alone decide reads no
/// value of it. So no value of one can steer a compared run without the run's list naming it,
/// and a census entry only duplicated that list. The census keeps the hooks k-rust evaluates
/// without a record: the `String2Bytes`/`Bytes2String` pair, the hooks no builtin file documents
/// ([`UNDOCUMENTED_EVALUATED_HOOKS`]), and those of its `chosen_value` classes (moving these
/// needs every class shown withheld outside execution, which is not verified).
///
/// The premise is k-rust's contract, `docs/compatibility.md` line 117 ("Backend scope", the
/// console paragraph), which the kink-native test
/// `the_console_passage_the_run_list_rests_on_is_pinned` pins by digest; k-rust's test
/// `unsupported_hook_positions.rs` checks it in the four positions for every hook of its `CASES`,
/// which hold every hook here (`the_run_list_hooks_are_k_rusts_unevaluated_open_hooks`, which
/// also derives this list from k-rust's inventory, its `NOT_EVALUATED` list and its hook
/// namespaces). A test's initial state is still read against every open hook
/// ([`state_references_implementation_chosen`]): the contract names the positions of a rule or
/// equation, not the initial state.
pub const RUN_LIST_HOOKS: &[&str] = &[
    "STRING.float2string",
    "STRING.floatFormat",
    "STRING.category",
    "STRING.directionality",
    "STRING.uuid",
    "INT.rand",
    "INT.srand",
    "RANGEMAP.choice",
    "RANGEMAP.keys_list",
    "RANGEMAP.values",
    "KREFLECTION.configuration",
    "KREFLECTION.fresh",
    "KREFLECTION.getenv",
    "KREFLECTION.kompiledDir",
    "KREFLECTION.argv",
    "KREFLECTION.printKORE",
    "IO.open",
    "IO.tell",
    "IO.seek",
    "IO.seekEnd",
    "IO.getc",
    "IO.putc",
    "IO.write",
    "IO.close",
    "IO.lock",
    "IO.unlock",
    "IO.accept",
    "IO.shutdownWrite",
    "IO.time",
    "IO.system",
    "IO.mkstemp",
    "IO.remove",
    "SUBSTITUTION.substMany",
    "UNIFICATION.renameVariables",
    "UNIFICATION.variables",
    "UNIFICATION.metaVariables",
    "UNIFICATION.variablesMap",
    "UNIFICATION.rename",
    "UNIFICATION.freezeVariables",
    "UNIFICATION.unifiable",
    "JSON.json2string",
    "JSON.string2json",
    "TIMER.timerStart",
    "TIMER.timerStop",
    "FFI.call",
    "FFI.call_variadic",
    "FFI.address",
    "FFI.alloc",
    "FFI.bytes_address",
    "FFI.read",
    "FFI.write",
];

/// Whether the definition-level census reads `hook`: it is open ([`IMPLEMENTATION_CHOSEN_HOOKS`])
/// and k-rust evaluates it without a run-level record (it is not on [`RUN_LIST_HOOKS`]).
#[must_use]
pub fn census_hook(hook: &str) -> bool {
    IMPLEMENTATION_CHOSEN_HOOKS.contains(&hook) && !RUN_LIST_HOOKS.contains(&hook)
}

/// The hooks of the operators whose operands a backend may or may not skip (domains.md
/// 1115-1117: `andBool` and `orBool` "may be short-circuited in concrete backends", and
/// `impliesBool` is `notBool P orBool Q`, 1110-1111; 2314-2317: `#if` "does not short-circuit
/// on symbolic backends"; 1115 calls `andThenBool` and `orElseBool` short-circuiting, but k-rust
/// reads their skipped operand's definedness too, so a step through one over an undefined
/// operand is undefined in k-rust where the text gives a value): re-pin decision 1 applied to the
/// short-circuit reading ([`Exclusion::ShortCircuitReading`]). Each with the argument positions a
/// backend may skip: both operands of a Boolean operator (a `[simplification]` such as
/// `_ andBool false => false` skips the left one), the branches of `#if`. The short-circuit
/// analysis needs every operator here to evaluate at least one of its skippable positions, and
/// every other position whenever it skips one (KINK-SC-DEFINED; the kink-native test
/// `every_short_circuit_operator_evaluates_a_skippable_operand_and_every_other_one` checks it
/// from each operator's meaning and fails on an operator it has none for).
pub const SHORT_CIRCUIT_HOOKS: &[(&str, &[usize])] = &[
    ("BOOL.and", &[0, 1]),
    ("BOOL.or", &[0, 1]),
    ("BOOL.implies", &[0, 1]),
    ("BOOL.andThen", &[0, 1]),
    ("BOOL.orElse", &[0, 1]),
    ("KEQUAL.ite", &[1, 2]),
];

/// The conjunctions whose operands, at the top of a rule's condition, may be undefined without
/// making the rule's applicability depend on the reading: a skipped operand makes the condition
/// `false` where k-rust's reading makes it undefined, and the rule applies in neither.
const CONJUNCTION_HOOKS: [&str; 2] = ["BOOL.and", "BOOL.andThen"];

/// The hooks whose result size the process's memory allowance caps (k-rust `bytes.rs`, the only
/// readers of `Allowance::of_process`): a refusal of one depends on the host.
pub const ALLOWANCE_HOOKS: [&str; 3] = ["BYTES.padRight", "BYTES.padLeft", "BYTES.int2bytes"];

/// Why a run is no evidence for any comparison (see the module documentation).
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Exclusion {
    StackStop,
    LoadStackStop,
    ContradictedClaim,
    ImplementationChosenHook,
    ShortCircuitReading,
    AllowanceRefusal,
    EqualsCondition,
    /// The run read a value the definition leaves open (k-rust's `implementationChosenValues`;
    /// re-pin adoption A-1).
    ImplementationChosenValue,
    /// The run or its load left an application unevaluated as an unsupported hook (k-rust's
    /// `unsupportedHooks`; re-pin adoption A-1).
    UnsupportedHook,
}

impl Exclusion {
    /// The report name, which is also the reason a run document gives.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::StackStop => "stack-stop",
            Self::LoadStackStop => "load-stack-stop",
            Self::ContradictedClaim => "contradicted-claim",
            Self::ImplementationChosenHook => "implementation-chosen-hook",
            Self::ShortCircuitReading => "short-circuit-reading",
            Self::AllowanceRefusal => "allowance-refusal",
            Self::EqualsCondition => "equals-condition",
            Self::ImplementationChosenValue => "implementation-chosen-value",
            Self::UnsupportedHook => "unsupported-hook",
        }
    }
}

/// A sentence of a definition (its own, or a rewrite rule whatever its source) that references a
/// symbol with a hook the census reads ([`census_hook`]).
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct HookReference {
    /// The KORE module of the sentence.
    pub module: String,
    /// The sentence's `UNIQUE_ID`, label or source position, as far as it has one.
    pub sentence: String,
    pub symbol: String,
    pub hook: String,
}

/// What a loaded definition contributes to the exclusions of every run on it. Built once per
/// backend, from the compiled KORE the backend loaded and that backend's selected definition.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct DefinitionExclusions {
    /// `discharge_counts().stack_stops + value_claims().counts().condition_stack_stops` of the
    /// default module's load (the only module kink's requests name).
    pub load_stack_stops: usize,
    /// The sentences that reference a hook the census reads ([`census_hook`]): the definition's
    /// own, and every rewrite rule whatever its source.
    pub implementation_chosen: Vec<HookReference>,
    /// The axioms rooted at a collection role symbol: the executable equations the load reports
    /// as `IndexedAt(Map | List | Set)` and the `simplification` or `symbolic` axioms it does not
    /// report (k-rust `collection_leaf_contract.rs`), each as its id, label or position.
    pub role_rooted_axioms: Vec<String>,
    /// The `UNIQUE_ID`s of the axioms written with `preserves-definedness`.
    pub preserves_definedness: BTreeSet<String>,
    /// The rewrite rules (each as its id, label or position) whose applicability or result
    /// depends on the short-circuit reading with no leaf to show it: a condition that, below its
    /// top-level conjunction, applies a short-circuit operator over an operand that may be
    /// undefined, or that applies a function whose value depends on the reading; or a right-hand
    /// side that applies a function whose own condition does ([`Exclusion::ShortCircuitReading`]).
    pub short_circuit_conditions: Vec<String>,
    /// The `UNIQUE_ID`s of the rewrite rules whose right-hand side applies a short-circuit
    /// operator over an operand that may be undefined, directly or through a function whose
    /// equation does: a `Trivial` leaf of one is no evidence ([`Exclusion::ShortCircuitReading`]).
    pub short_circuit_rules: BTreeSet<String>,
    /// The same rewrite rules, each as its id, label or position: any one excludes the whole
    /// definition (re-pin R0c-fix-2, R0c-fix-1 review major). An undefined candidate beside a
    /// defined same-priority sibling leaves no leaf (k-rust drops it and keeps the sibling's
    /// successor), so the leaf check alone cannot see every step that depends on the reading.
    pub short_circuit_results: Vec<String>,
    /// The function symbols whose value depends on the short-circuit reading (an equation's
    /// condition or right-hand side does, directly or through another such symbol): a test's
    /// initial state that applies one is no evidence.
    pub short_circuit_symbols: BTreeSet<String>,
    /// The rewrite rules and equations (each as its id, label or position) whose condition holds
    /// an `\equals` between two terms, a K `{ A #Equals B }`, other than the Bool reading
    /// `\equals(C, true)` of a K condition ([`Exclusion::EqualsCondition`]).
    pub equals_conditions: Vec<String>,
}

/// A compiled side loaded for one module on this thread, with the exclusions read from it
/// ([`DefinitionExclusions::load_validated`]).
pub struct ValidatedLoad {
    /// The side's exclusions, as [`DefinitionExclusions::of_validated`] gives them.
    pub exclusions: DefinitionExclusions,
    /// The backend loaded from the side's compiled KORE for the module (`Backend::from_definition`
    /// with default options), whose selected definition the exclusions were read from.
    pub backend: k_rust::backend::Backend,
    /// The side's compiled KORE, parsed.
    pub kore: Definition,
}

impl DefinitionExclusions {
    /// The exclusions of `kore`, loaded as `definition` (the definition the backend selected for
    /// the default module, after the load). Only the definition's own sentences count for the
    /// implementation-chosen census (see `authored`): not the prelude's, whose `Source` starts
    /// with one of `builtin_prefixes` (k-rust `CompileOptions::builtin_source_prefixes`), and not
    /// kompile's derived axioms. Every axiom counts for the role-rooted scan.
    #[must_use]
    pub fn of(
        kore: &Definition,
        definition: &BackendDefinition,
        builtin_prefixes: &[String],
    ) -> Self {
        let counts = definition.value_claims().counts();
        let load_stack_stops =
            definition.discharge_counts().stack_stops + counts.condition_stack_stops;
        let hooked = definition
            .symbols()
            .values()
            .filter_map(|symbol| {
                let hook = symbol.attributes.hook.as_deref()?;
                census_hook(hook).then(|| (symbol.name.to_string(), hook.to_owned()))
            })
            .collect::<std::collections::BTreeMap<_, _>>();
        let roles = definition
            .symbols()
            .values()
            .filter_map(|symbol| symbol.attributes.collection.as_ref())
            .flat_map(|metadata| {
                let symbols = match metadata {
                    CollectionMetadata::Map(map) => &map.symbols,
                    CollectionMetadata::List(list) | CollectionMetadata::Set(list) => &list.symbols,
                };
                [
                    symbols.unit.to_string(),
                    symbols.element.to_string(),
                    symbols.concat.to_string(),
                ]
            })
            .collect::<BTreeSet<_>>();
        let mut implementation_chosen = BTreeSet::new();
        let mut role_rooted_axioms = BTreeSet::new();
        let mut preserves_definedness = BTreeSet::new();
        for module in &kore.modules {
            for sentence in &module.sentences {
                let (attributes, patterns, declared) = match sentence {
                    Sentence::Axiom {
                        pattern,
                        attributes,
                        ..
                    }
                    | Sentence::Claim {
                        pattern,
                        attributes,
                        ..
                    } => (attributes, vec![&**pattern], None),
                    Sentence::AliasDeclaration {
                        left,
                        right,
                        attributes,
                        ..
                    } => (attributes, vec![&**left, &**right], None),
                    Sentence::SymbolDeclaration {
                        symbol, attributes, ..
                    } => (attributes, Vec::new(), Some(symbol.name.as_str())),
                    Sentence::Import { .. } | Sentence::SortDeclaration { .. } => continue,
                };
                if let Sentence::Axiom {
                    pattern,
                    attributes,
                    ..
                } = sentence
                {
                    if attributes.has(KoreAttribute::PreservesDefinedness)
                        && let Some(id) = string_attribute(attributes, KoreAttribute::UniqueId)
                    {
                        preserves_definedness.insert(id.to_owned());
                    }
                    if (attributes.has(KoreAttribute::Simplification)
                        || attributes.has(KoreAttribute::Symbolic))
                        && axiom_head(pattern).is_some_and(|head| roles.contains(head))
                    {
                        role_rooted_axioms.insert(sentence_name(attributes));
                    }
                }
                // A rewrite rule counts whatever its source says: the prelude's stream rules are
                // copied into a definition with stream cells and keep their prelude source (their
                // hooks, `#getc`, `#write` and `Float2String`, are on the run list, so they no
                // longer count; a census hook in such a rule would).
                if !authored(attributes, builtin_prefixes) && !is_rewrite_axiom(sentence) {
                    continue;
                }
                let mut referenced = BTreeSet::new();
                if let Some(name) = declared {
                    referenced.insert(name.to_owned());
                }
                for pattern in patterns {
                    walk::for_each_post_order(pattern, |node| {
                        if let Pattern::Application { symbol, .. } = node
                            && hooked.contains_key(symbol.name.as_str())
                        {
                            referenced.insert(symbol.name.clone());
                        }
                    });
                }
                for symbol in referenced {
                    if let Some(hook) = hooked.get(&symbol) {
                        implementation_chosen.insert(HookReference {
                            module: module.name.clone(),
                            sentence: sentence_name(attributes),
                            symbol,
                            hook: hook.clone(),
                        });
                    }
                }
            }
        }
        for violation in definition.value_claims().violations() {
            if let ViolationKind::IndexedAt(TermIndex::Map | TermIndex::List | TermIndex::Set) =
                &violation.kind
            {
                role_rooted_axioms.insert(violation.rule.as_ref().map_or_else(
                    || "an unnamed equation".to_owned(),
                    |rule| rule.attributes.unique_id.clone(),
                ));
            }
        }
        let mut short_circuit = ShortCircuitAnalysis::of(definition);
        short_circuit.close_over(kore);
        let mut short_circuit_conditions = BTreeSet::new();
        let mut short_circuit_rules = BTreeSet::new();
        let mut short_circuit_results = BTreeSet::new();
        let mut equals_conditions = BTreeSet::new();
        for module in &kore.modules {
            for sentence in &module.sentences {
                let Sentence::Axiom {
                    pattern,
                    attributes,
                    ..
                } = sentence
                else {
                    continue;
                };
                if holds_condition_equality(pattern) {
                    equals_conditions.insert(sentence_name(attributes));
                }
                let Some((conditions, left, right)) = rewrite_sides(pattern) else {
                    continue;
                };
                if conditions
                    .iter()
                    .chain([&left])
                    .any(|side| short_circuit.condition_side(side))
                    || short_circuit.applies(right, &short_circuit.valued)
                {
                    short_circuit_conditions.insert(sentence_name(attributes));
                }
                if short_circuit.result(right) {
                    short_circuit_results.insert(sentence_name(attributes));
                    if let Some(id) = string_attribute(attributes, KoreAttribute::UniqueId) {
                        short_circuit_rules.insert(id.to_owned());
                    }
                }
            }
        }
        Self {
            load_stack_stops,
            implementation_chosen: implementation_chosen.into_iter().collect(),
            role_rooted_axioms: role_rooted_axioms.into_iter().collect(),
            preserves_definedness,
            short_circuit_conditions: short_circuit_conditions.into_iter().collect(),
            short_circuit_rules,
            short_circuit_results: short_circuit_results.into_iter().collect(),
            short_circuit_symbols: short_circuit
                .undefined
                .union(&short_circuit.valued)
                .cloned()
                .collect(),
            equals_conditions: equals_conditions.into_iter().collect(),
        }
    }

    /// The exclusions of a compiled side loaded for `module` (its encoded KORE name) on this
    /// thread, as kink-campaign's runner computes them for a side it prepares.
    pub fn of_validated(side: &crate::ValidatedDefinition, module: &str) -> Result<Self, String> {
        Self::load_validated(side, module).map(|load| load.exclusions)
    }

    /// [`Self::of_validated`], keeping the backend and the parsed KORE the exclusions were read
    /// from ([`ValidatedLoad`]), for a client that judges further runs of the side on that load
    /// (kink-flow's in-campaign witness filter, fz26 FZ-COMPARABLE-B). The exclusions are those
    /// [`Self::of_validated`] gives.
    pub fn load_validated(
        side: &crate::ValidatedDefinition,
        module: &str,
    ) -> Result<ValidatedLoad, String> {
        let kore = k_rust::kore::parser::parse_definition(&side.artifacts().definition_kore)
            .map_err(|error| error.to_string())?;
        let mut backend = k_rust::backend::Backend::from_definition(
            kore.clone(),
            module,
            k_rust::backend::BackendOptions::default(),
        )
        .map_err(|error| error.to_string())?;
        let selected = backend
            .select_definition(None)
            .map_err(|error| error.to_string())?;
        let exclusions = Self::of(
            &kore,
            &selected,
            &side.compile_options().builtin_source_prefixes,
        );
        Ok(ValidatedLoad {
            exclusions,
            backend,
            kore,
        })
    }

    /// The facts of two loads of one definition taken together, each exclusion holding when it
    /// holds on either load (re-pin R0c): the load stack stops are added, and the census
    /// references, the role-rooted axioms, the `preserves-definedness` ids and the short-circuit
    /// rules, conditions and symbols are united. A run
    /// produced on one load and judged on another is judged under this (a baseline run a
    /// session reuses, kink-campaign `BaselineSession`).
    #[must_use]
    pub fn combined(&self, other: &Self) -> Self {
        fn union<T: Clone + Ord>(left: &[T], right: &[T]) -> Vec<T> {
            left.iter()
                .chain(right)
                .cloned()
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect()
        }
        Self {
            load_stack_stops: self.load_stack_stops.saturating_add(other.load_stack_stops),
            implementation_chosen: union(&self.implementation_chosen, &other.implementation_chosen),
            role_rooted_axioms: union(&self.role_rooted_axioms, &other.role_rooted_axioms),
            preserves_definedness: self
                .preserves_definedness
                .union(&other.preserves_definedness)
                .cloned()
                .collect(),
            short_circuit_conditions: union(
                &self.short_circuit_conditions,
                &other.short_circuit_conditions,
            ),
            short_circuit_rules: self
                .short_circuit_rules
                .union(&other.short_circuit_rules)
                .cloned()
                .collect(),
            short_circuit_results: union(&self.short_circuit_results, &other.short_circuit_results),
            short_circuit_symbols: self
                .short_circuit_symbols
                .union(&other.short_circuit_symbols)
                .cloned()
                .collect(),
            equals_conditions: union(&self.equals_conditions, &other.equals_conditions),
        }
    }

    /// The exclusion every run on this definition has, if any: a load stack stop first, then an
    /// implementation-chosen hook, then a rule whose condition, value or result depends on the
    /// short-circuit reading, then a condition that equates two terms.
    #[must_use]
    pub fn definition_exclusion(&self) -> Option<Exclusion> {
        if self.load_stack_stops > 0 {
            Some(Exclusion::LoadStackStop)
        } else if !self.implementation_chosen.is_empty() {
            Some(Exclusion::ImplementationChosenHook)
        } else if !self.short_circuit_conditions.is_empty()
            || !self.short_circuit_results.is_empty()
        {
            Some(Exclusion::ShortCircuitReading)
        } else if !self.equals_conditions.is_empty() {
            Some(Exclusion::EqualsCondition)
        } else {
            None
        }
    }

    /// Whether a collection term of this definition can be a terminal value: no axiom is rooted
    /// at a collection role symbol (KINK-05's collection denotation contract, finding C-10).
    #[must_use]
    pub fn collections_trusted(&self) -> bool {
        self.role_rooted_axioms.is_empty()
    }

    /// The exclusion of `execution`, a run on this definition, if any (see the module
    /// documentation), in this order: the definition's own; a stack stop; a contradicted claim (a
    /// leaf's, [`Self::contradicts_a_claim`], or any record on the run's list); a value the
    /// definition leaves open on the run's list; an undefined step of a rule whose result depends
    /// on the short-circuit reading; an allowance refusal (on a leaf or on the run's list); and an
    /// unsupported hook on the run's list (re-pin adoption A-1 added the lists). A timed-out run is
    /// a timeout before it is anything else, and is not asked.
    #[must_use]
    pub fn run_exclusion(&self, execution: &AdaptedExecution) -> Option<Exclusion> {
        if let Some(exclusion) = self.definition_exclusion() {
            return Some(exclusion);
        }
        if execution.stack_stops() > 0 {
            return Some(Exclusion::StackStop);
        }
        let leaves = execution.leaves();
        let facts: &RunFacts = execution.facts();
        if self.contradiction_on_a_leaf(execution) || !facts.contradicted_claims.is_empty() {
            return Some(Exclusion::ContradictedClaim);
        }
        if !facts.implementation_chosen_values.is_empty() {
            return Some(Exclusion::ImplementationChosenValue);
        }
        if leaves.iter().any(|leaf| self.short_circuit_step(leaf)) {
            return Some(Exclusion::ShortCircuitReading);
        }
        if leaves.iter().any(allowance_refusal) || !facts.allowance_refusals.is_empty() {
            return Some(Exclusion::AllowanceRefusal);
        }
        if !facts.unsupported_hooks.is_empty() {
            return Some(Exclusion::UnsupportedHook);
        }
        None
    }

    /// Whether a leaf of `execution` contradicts a trusted claim by decision 2's leaf rule
    /// ([`Self::contradicts_a_claim`]), the run's list not counted: the only contradiction for
    /// which kink-campaign's admission keeps a baseline and makes just its test unknown (re-pin
    /// R0c-fix-1). A record on the list alone (re-pin adoption A-1) refuses a baseline as any
    /// other exclusion does. Before A-1 such a run either was complete and compared, or had a leaf
    /// carrying the record, which made its side unknown and refused the baseline; so reading the
    /// list moves a baseline only toward a refusal, never out of one.
    #[must_use]
    pub fn contradiction_on_a_leaf(&self, execution: &AdaptedExecution) -> bool {
        execution
            .leaves()
            .iter()
            .any(|leaf| self.contradicts_a_claim(leaf))
    }

    /// Whether `leaf` is an undefined step that falsifies a trusted claim: k-rust names a
    /// contradicted `total` claim, or the leaf is `Trivial` and its rule carries
    /// `preserves-definedness`.
    #[must_use]
    pub fn contradicts_a_claim(&self, leaf: &AdaptedLeaf) -> bool {
        leaf.contradicted_total.is_some()
            || (leaf.halt == HaltClass::Trivial
                && leaf.undefined_rule.as_ref().is_some_and(|rule| {
                    self.undefined_step_exclusions(&rule.id)
                        .contains(&Exclusion::ContradictedClaim)
                }))
    }

    /// The exclusions an undefined step (a `Trivial` leaf) of the rule with unique id `rule_id`
    /// gives its run on this definition, in [`Self::run_exclusion`]'s order: a contradicted claim
    /// when the rule carries `preserves-definedness`, then the short-circuit reading when its
    /// result depends on it. The one reading of an undefined step's rule, shared by
    /// [`Self::contradicts_a_claim`], [`Self::short_circuit_step`] and clients that judge a
    /// leaf known by its rule id (kink-flow's witness filter, fz26 FZ-COMPARABLE-B).
    #[must_use]
    pub fn undefined_step_exclusions(&self, rule_id: &str) -> Vec<Exclusion> {
        let mut exclusions = Vec::new();
        if self.preserves_definedness.contains(rule_id) {
            exclusions.push(Exclusion::ContradictedClaim);
        }
        if self.short_circuit_rules.contains(rule_id) {
            exclusions.push(Exclusion::ShortCircuitReading);
        }
        exclusions
    }

    /// Whether `leaf` is an undefined step of a rewrite rule whose right-hand side applies a
    /// short-circuit operator over an operand that may be undefined (directly or through a
    /// function): k-rust reads the step as undefined, a short-circuiting backend may not.
    #[must_use]
    pub fn short_circuit_step(&self, leaf: &AdaptedLeaf) -> bool {
        leaf.halt == HaltClass::Trivial
            && leaf.undefined_rule.as_ref().is_some_and(|rule| {
                self.undefined_step_exclusions(&rule.id)
                    .contains(&Exclusion::ShortCircuitReading)
            })
    }

    /// The exclusion of `state`, a test's initial state on `definition` (the definition these
    /// facts were read from), if any: it applies an implementation-chosen hook
    /// ([`state_references_implementation_chosen`]), or a function or operator whose value
    /// depends on the short-circuit reading ([`Self::state_depends_on_short_circuit`]).
    #[must_use]
    pub fn state_exclusion(
        &self,
        definition: &BackendDefinition,
        state: &Pattern,
    ) -> Option<Exclusion> {
        state_references_implementation_chosen(definition, state)
            .then_some(Exclusion::ImplementationChosenHook)
            .or_else(|| {
                self.state_depends_on_short_circuit(definition, state)
                    .then_some(Exclusion::ShortCircuitReading)
            })
    }

    /// Whether `state`, a test's initial state on `definition` (the definition these facts were
    /// read from), applies a function whose value depends on the short-circuit reading, or a
    /// short-circuit operator over an operand that may be undefined.
    #[must_use]
    pub fn state_depends_on_short_circuit(
        &self,
        definition: &BackendDefinition,
        state: &Pattern,
    ) -> bool {
        let mut reading = ShortCircuitAnalysis::of(definition);
        reading.undefined.clone_from(&self.short_circuit_symbols);
        reading.applies(state, &self.short_circuit_symbols) || reading.direct(state)
    }
}

/// The short-circuit reading of one loaded definition ([`Exclusion::ShortCircuitReading`]): its
/// operators, its partial functions, and, once closed over the definition's equations, the
/// functions whose value depends on the reading.
struct ShortCircuitAnalysis {
    /// Each short-circuit operator symbol with the argument positions a backend may skip.
    operators: std::collections::BTreeMap<String, &'static [usize]>,
    /// The conjunction operator symbols ([`CONJUNCTION_HOOKS`]).
    conjunctions: BTreeSet<String>,
    /// The function symbols not declared `total`: an application of one may be undefined.
    partial: BTreeSet<String>,
    /// Functions that can be undefined in k-rust's reading where a short-circuiting backend gives
    /// a value: an equation's right-hand side skips an operand that may be undefined.
    undefined: BTreeSet<String>,
    /// Functions whose value can differ between the readings with no undefined step: an
    /// equation's condition depends on the reading, so k-rust may apply another equation.
    valued: BTreeSet<String>,
    /// The functions of [`Self::undefined`], not of [`Self::valued`], every equation of which is
    /// a conjunction (`andBool`, `andThenBool`) of terms that do not depend on the reading and of
    /// calls of such functions: where k-rust's reading makes a call undefined, the other makes
    /// it `false` (a skipped conjunct makes its conjunction `false`), and nowhere else do the
    /// readings differ. At the top of a condition such a call, like a conjunct, makes the rule
    /// inapplicable in both readings (a guard such as `lengthBytes(B) ==Int 1 andBool B[0] ==Int
    /// 128`).
    conjunctive: BTreeSet<String>,
}

impl ShortCircuitAnalysis {
    fn of(definition: &BackendDefinition) -> Self {
        let mut operators = std::collections::BTreeMap::new();
        let mut conjunctions = BTreeSet::new();
        let mut partial = BTreeSet::new();
        for symbol in definition.symbols().values() {
            let name = symbol.name.to_string();
            if let Some(hook) = symbol.attributes.hook.as_deref() {
                if let Some((_, positions)) = SHORT_CIRCUIT_HOOKS.iter().find(|(h, _)| *h == hook) {
                    operators.insert(name.clone(), *positions);
                }
                if CONJUNCTION_HOOKS.contains(&hook) {
                    conjunctions.insert(name.clone());
                }
            }
            if symbol.attributes.symbol_type == SymbolType::Function(FunctionType::Partial) {
                partial.insert(name);
            }
        }
        Self {
            operators,
            conjunctions,
            partial,
            undefined: BTreeSet::new(),
            valued: BTreeSet::new(),
            conjunctive: BTreeSet::new(),
        }
    }

    /// Close [`Self::undefined`] and [`Self::valued`] over every equation of `kore`, whatever its
    /// source (a prelude function can depend on the reading too).
    fn close_over(&mut self, kore: &Definition) {
        let equations = kore
            .modules
            .iter()
            .flat_map(|module| &module.sentences)
            .filter_map(|sentence| match sentence {
                Sentence::Axiom { pattern, .. } => equation_parts(pattern),
                _ => None,
            })
            .collect::<Vec<_>>();
        loop {
            let mut changed = false;
            for (head, condition, right) in &equations {
                if !self.undefined.contains(*head) && self.result(right) {
                    self.undefined.insert((*head).to_owned());
                    changed = true;
                }
                if !self.valued.contains(*head)
                    && (condition.is_some_and(|condition| self.condition_side(condition))
                        || self.applies(right, &self.valued))
                {
                    self.valued.insert((*head).to_owned());
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        // The greatest set of conjunctive functions: start from every function that can be
        // undefined and does not depend on the reading otherwise, and drop each one an equation
        // of which is not a conjunction of reading-independent terms and conjunctive calls.
        self.conjunctive = self.undefined.difference(&self.valued).cloned().collect();
        loop {
            let dropped = self
                .conjunctive
                .iter()
                .filter(|function| {
                    equations
                        .iter()
                        .any(|(head, _, right)| head == function && self.condition(right))
                })
                .cloned()
                .collect::<Vec<_>>();
            if dropped.is_empty() {
                break;
            }
            for function in dropped {
                self.conjunctive.remove(&function);
            }
        }
    }

    /// Whether `pattern` applies a symbol of `symbols`.
    fn applies(&self, pattern: &Pattern, symbols: &BTreeSet<String>) -> bool {
        let mut found = false;
        walk::for_each_post_order(pattern, |node| {
            if let Pattern::Application { symbol, .. } = node {
                found |= symbols.contains(symbol.name.as_str());
            }
        });
        found
    }

    /// Whether `symbol` depends on the reading ([`Self::undefined`], [`Self::valued`]).
    fn reading_dependent(&self, symbol: &str) -> bool {
        self.undefined.contains(symbol) || self.valued.contains(symbol)
    }

    /// `May(pattern)`: the applications anywhere in `pattern` that may be undefined, of a
    /// partial function or of a function that can be undefined in k-rust's reading
    /// ([`Self::undefined`]). Where `pattern` is undefined on an instance, one of them is: every
    /// other symbol is total, a constructor or a domain value, and every symbol is strict. (An
    /// application of a total function of [`Self::valued`] is flagged by every caller wherever
    /// it occurs.)
    fn may(&self, pattern: &Pattern) -> BTreeSet<Pattern> {
        let mut out = BTreeSet::new();
        walk::for_each_post_order(pattern, |node| {
            if let Pattern::Application { symbol, .. } = node
                && (self.partial.contains(symbol.name.as_str())
                    || self.undefined.contains(symbol.name.as_str()))
            {
                out.insert(node.clone());
            }
        });
        out
    }

    /// `Must(pattern)`: applications of partial functions that do not depend on the reading
    /// which every evaluation of `pattern` evaluates, under every order a short-circuit operator
    /// may take. A short-circuit operator contributes its other operands' `Must` and the
    /// intersection of its skippable operands' (it evaluates at least one skippable operand, and
    /// every other operand whenever it skips one: `SHORT_CIRCUIT_HOOKS`, pinned by the test
    /// `every_short_circuit_operator_evaluates_a_skippable_operand_and_every_other_one`); any
    /// other application its arguments' `Must` and, for such a partial function, itself. An
    /// application of a reading-dependent function is left out, so each term of `Must` is
    /// undefined in one reading exactly where it is in the other (for its arguments, see
    /// [`Self::direct`]). It is an under-approximation: a pattern that is no application
    /// contributes nothing.
    fn must(&self, pattern: &Pattern) -> BTreeSet<Pattern> {
        let Pattern::Application { symbol, arguments } = pattern else {
            return BTreeSet::new();
        };
        let mut out = BTreeSet::new();
        if let Some(positions) = self.operators.get(symbol.name.as_str()) {
            let mut skippable: Option<BTreeSet<Pattern>> = None;
            for (index, argument) in arguments.iter().enumerate() {
                let evaluated = self.must(argument);
                if positions.contains(&index) {
                    skippable = Some(match skippable {
                        None => evaluated,
                        Some(common) => common.intersection(&evaluated).cloned().collect(),
                    });
                } else {
                    out.extend(evaluated);
                }
            }
            out.extend(skippable.unwrap_or_default());
            return out;
        }
        for argument in arguments {
            out.extend(self.must(argument));
        }
        let name = symbol.name.as_str();
        if self.partial.contains(name) && !self.reading_dependent(name) {
            out.insert(pattern.clone());
        }
        out
    }

    /// Whether `pattern` applies a short-circuit operator with an operand a backend may skip
    /// whose value can differ between the readings: for some skippable position `i`,
    /// `May(arg_i)` is not contained in the union of `Must(arg_j)` over the other positions `j`
    /// (KINK-SC-DEFINED, fz26 `P7-SIMPLE-KINK-design.md`). The readings differ at an operator
    /// only on an instance where a skipped operand `arg_i` is undefined while the operands
    /// evaluated are defined. There some `t` of `May(arg_i)` is undefined; if `t` is in
    /// `Must(arg_j)`, the same pattern over the same variables, hence the same value, is
    /// evaluated by an operand evaluated whenever `arg_i` is skipped, so both readings are
    /// undefined there. No guard's truth is read, only the definedness of terms both readings
    /// evaluate (`#if A >=Int 0 #then A #else pd(A) #fi` stays flagged where `pd(A)` occurs in no
    /// other operand). The callers flag an application of a reading-dependent function wherever
    /// it occurs, and the walk visits every operator node, so below a node they do not flag every
    /// subterm has the same value and definedness in both readings.
    ///
    /// The reading-dependent functions are the least fixed point of [`Self::close_over`], so a
    /// recursive function is read as independent while its own equations are checked (the
    /// greatest fixed point of independence: `findChar`'s skipped recursive calls each occur in
    /// `Must` of the condition or of the other branch). That is sound by induction on the depth
    /// of evaluation, which needs evaluation to terminate (premise A1, k-rust `data_term`).
    fn direct(&self, pattern: &Pattern) -> bool {
        let mut found = false;
        walk::for_each_post_order(pattern, |node| {
            if !found
                && let Pattern::Application { symbol, arguments } = node
                && let Some(positions) = self.operators.get(symbol.name.as_str())
            {
                found = positions.iter().any(|position| {
                    let Some(skipped) = arguments.get(*position) else {
                        return false;
                    };
                    let mut evaluated = BTreeSet::new();
                    for (index, other) in arguments.iter().enumerate() {
                        if index != *position {
                            evaluated.extend(self.must(other));
                        }
                    }
                    self.may(skipped)
                        .iter()
                        .any(|term| !evaluated.contains(term))
                });
            }
        });
        found
    }

    /// Whether a rule's or an equation's right-hand side `right` can be undefined in k-rust's
    /// reading where a short-circuiting backend gives a value.
    fn result(&self, right: &Pattern) -> bool {
        self.direct(right) || self.applies(right, &self.undefined)
    }

    /// Whether a condition term (a `requires` clause, `Bool`) can be true in one reading and
    /// not in the other: below its top-level conjunctions, it applies a short-circuit operator
    /// over an operand that may be undefined, or a function that depends on the reading, other
    /// than as a conjunctive call ([`Self::conjunctive`]). A top-level conjunct or conjunctive
    /// call that is undefined in k-rust's reading is `false` or undefined in the other, and the
    /// rule applies in neither.
    fn condition(&self, condition: &Pattern) -> bool {
        match condition {
            // An equation's right-hand side `\and(term, ensures)`.
            Pattern::And { arguments, .. } => {
                arguments.iter().any(|argument| self.condition(argument))
            }
            Pattern::Application { symbol, arguments }
                if self.conjunctions.contains(symbol.name.as_str()) =>
            {
                arguments.iter().any(|argument| self.condition(argument))
            }
            // A conjunctive call is `false` where k-rust's reading makes it undefined, as a
            // conjunct is, so only its arguments can make the condition depend on the reading.
            Pattern::Application { symbol, arguments }
                if self.conjunctive.contains(symbol.name.as_str()) =>
            {
                arguments.iter().any(|argument| {
                    self.direct(argument)
                        || self.applies(argument, &self.undefined)
                        || self.applies(argument, &self.valued)
                })
            }
            _ => {
                self.direct(condition)
                    || self.applies(condition, &self.undefined)
                    || self.applies(condition, &self.valued)
            }
        }
    }

    /// [`Self::condition`] of the side of an axiom that holds its condition: a rewrite rule's
    /// left-hand side (its configuration and `\equals(requires, true)`), or an equation's
    /// antecedent (`\equals(requires, true)` and its argument constraints). Any part other than
    /// a `requires` clause counts as a whole.
    fn condition_side(&self, side: &Pattern) -> bool {
        match side {
            Pattern::And { arguments, .. } => arguments
                .iter()
                .any(|argument| self.condition_side(argument)),
            Pattern::Equals { left, right, .. } if is_true(right) => self.condition(left),
            Pattern::Implies { left, right, .. } => {
                self.condition_side(left) || self.condition_side(right)
            }
            Pattern::Top { .. } => false,
            other => self.condition(other),
        }
    }
}

/// Whether `sentence` is a rewrite axiom ([`rewrite_sides`]).
fn is_rewrite_axiom(sentence: &Sentence) -> bool {
    matches!(sentence, Sentence::Axiom { pattern, .. } if rewrite_sides(pattern).is_some())
}

/// Whether `pattern` is the Bool domain value `true`.
fn is_true(pattern: &Pattern) -> bool {
    matches!(pattern, Pattern::DomainValue { value, .. } if value.as_bytes() == b"true")
}

/// A rewrite axiom's conditions (the antecedents of any `\implies` around it), left-hand side
/// and right-hand side, under its binders; `None` for every other axiom.
fn rewrite_sides(pattern: &Pattern) -> Option<(Vec<&Pattern>, &Pattern, &Pattern)> {
    match pattern {
        Pattern::Forall { body, .. } | Pattern::Exists { body, .. } => rewrite_sides(body),
        Pattern::Implies { left, right, .. } => {
            let (mut conditions, lhs, rhs) = rewrite_sides(right)?;
            conditions.push(left);
            Some((conditions, lhs, rhs))
        }
        Pattern::Rewrites { left, right, .. } => Some((Vec::new(), left, right)),
        _ => None,
    }
}

/// Whether an axiom's conditions hold an `\equals` other than the Bool reading, whatever its
/// left-hand side is (an application, `#Ceil` or another predicate): every antecedent of an
/// `\implies` around its conclusion (an equation's or lemma's `requires` and argument
/// constraints), a rewrite rule's left-hand side (which holds its `requires`), and the `ensures`
/// of either kind.
///
/// - An equation's or lemma's `ensures` is every conjunct after the first of the right-hand side
///   `\and(rhs, ensures)` kompile emits, under any binder. The `\equals` that states the
///   equation or lemma, its left-hand side (the term or predicate the lemma rewrites) and its
///   right-hand side term are not conditions (a predicate lemma of the prelude rewrites one
///   equality into another).
/// - A rewrite rule's whole right-hand side is read. Its conclusion is `\rewrites`, not an
///   `\equals`, so every `\equals` in its right-hand side is a condition of the step: kompile
///   emits `\and(rhs, ensures)`, wrapped in `\exists ?Y` for each existential variable of the
///   right-hand side (k-rust 501f18b9 `module_to_kore/equations.rs` 197-207) and, under a module
///   reachability attribute, in a `weakExistsFinally` or `weakAlwaysFinally` application
///   (208-220). Reading every `\equals` there, the result term's included, reads the `ensures`
///   whatever wraps it.
///
/// Re-pin R0c-fix-4, R0c-fix-3 review minor 6: R0c-fix-3 read only rewrite rules and
/// application-headed equations, and no `ensures`. Re-pin R0-tail, R0c-fix-4 review minor 1:
/// R0c-fix-4 read the `ensures` only as the last conjunct of an `\and` at the top of the
/// right-hand side, so a rewrite rule with an existential variable was not read.
fn holds_condition_equality(pattern: &Pattern) -> bool {
    fn ensures(right: &Pattern) -> bool {
        match right {
            Pattern::Forall { body, .. } | Pattern::Exists { body, .. } => ensures(body),
            Pattern::And { arguments, .. } => arguments.iter().skip(1).any(holds_term_equality),
            _ => false,
        }
    }
    match pattern {
        Pattern::Forall { body, .. } | Pattern::Exists { body, .. } => {
            holds_condition_equality(body)
        }
        Pattern::Implies { left, right, .. } => {
            holds_term_equality(left) || holds_condition_equality(right)
        }
        Pattern::Equals { right, .. } => ensures(right),
        Pattern::Rewrites { left, right, .. } => {
            holds_term_equality(left) || holds_term_equality(right)
        }
        _ => false,
    }
}

/// Whether `condition` holds an `\equals` other than the Bool reading `\equals(C, true)` (either
/// order) by which kompile states a K condition: the KORE of a K `{ A #Equals B }` (re-pin
/// R0c-fix-3, R0c-fix-2 review minor 3). k-rust 501f18b9 `docs/compatibility.md` "Two gaps
/// remain": such an `\equals` between two possibly undefined terms in a rule or equation
/// condition is kept as written, its SMT translation has no model where both sides are
/// undefined, and answers over the definition "may wrongly be empty, `valid` or `proven`"; how
/// the evaluator should read it is itself open. Whether the terms may be undefined is not read:
/// every such condition excludes the definition, which costs no current fixture.
fn holds_term_equality(condition: &Pattern) -> bool {
    fn bool_true(pattern: &Pattern) -> bool {
        matches!(pattern, Pattern::DomainValue {
            sort: k_rust::kore::ast::Sort::Application { name, .. },
            value,
        } if name == "SortBool" && value.as_bytes() == b"true")
    }
    let mut found = false;
    walk::for_each_post_order(condition, |node| {
        if let Pattern::Equals { left, right, .. } = node
            && !bool_true(left)
            && !bool_true(right)
        {
            found = true;
        }
    });
    found
}

/// An equation axiom's head symbol, antecedent (its `requires` and argument constraints) and
/// right-hand side, under its binders: `\implies(antecedent, \equals(head(..), right))` or
/// `\equals(head(..), right)`; `None` for every other axiom.
fn equation_parts(pattern: &Pattern) -> Option<(&str, Option<&Pattern>, &Pattern)> {
    match pattern {
        Pattern::Forall { body, .. } | Pattern::Exists { body, .. } => equation_parts(body),
        Pattern::Implies { left, right, .. } => match &**right {
            Pattern::Equals {
                left: head, right, ..
            } => Some((term_head(head)?, Some(&**left), &**right)),
            _ => None,
        },
        Pattern::Equals { left, right, .. } => Some((term_head(left)?, None, &**right)),
        _ => None,
    }
}

/// Whether `leaf` reports an allowance hook left unevaluated, on the leaf, a candidate or the
/// remainder.
fn allowance_refusal(leaf: &AdaptedLeaf) -> bool {
    leaf.diagnostics
        .iter()
        .chain(leaf.candidate_diagnostics.iter().flatten())
        .chain(&leaf.remainder_diagnostics)
        .any(|diagnostic| {
            matches!(diagnostic, BackendDiagnosticOutput::UnsupportedHookUnevaluated { hook, .. }
                if ALLOWANCE_HOOKS.contains(&hook.as_str()))
        })
}

/// Whether `state`, a test's initial state, applies a symbol with an implementation-chosen hook
/// of `definition`: such a run evaluates a value the definition leaves open, whatever the
/// definition's own sentences say.
#[must_use]
pub fn state_references_implementation_chosen(
    definition: &BackendDefinition,
    state: &Pattern,
) -> bool {
    let mut found = false;
    walk::for_each_post_order(state, |node| {
        if let Pattern::Application { symbol, .. } = node {
            found |= definition
                .symbols()
                .get(symbol.name.as_str())
                .and_then(|symbol| symbol.attributes.hook.as_deref())
                .is_some_and(|hook| IMPLEMENTATION_CHOSEN_HOOKS.contains(&hook));
        }
    });
    found
}

/// Whether a sentence with `attributes` is the definition's own rather than the prelude's or
/// kompile's: it has a `Source` that does not start with a builtin prefix, or it has no `Source`
/// but a `UNIQUE_ID` (a sentence a patch inserted carries no position attribute, but every rule
/// compiles with an id). A sentence with neither is an axiom kompile derived from a declaration
/// (the `functional` axiom of a `total` builtin symbol is written into the main module that way),
/// which references only what the declaration declares.
fn authored(attributes: &Attributes, builtin_prefixes: &[String]) -> bool {
    match string_attribute(attributes, KoreAttribute::Source) {
        Some(source) => {
            let source = source
                .strip_prefix("Source(")
                .and_then(|source| source.strip_suffix(')'))
                .unwrap_or(source);
            !builtin_prefixes
                .iter()
                .any(|prefix| source.starts_with(prefix.as_str()))
        }
        None => string_attribute(attributes, KoreAttribute::UniqueId).is_some(),
    }
}

fn string_attribute(attributes: &Attributes, attribute: KoreAttribute) -> Option<&str> {
    attributes.string(attribute).ok().flatten()
}

/// A sentence's `UNIQUE_ID`, else its label, else its source and location, else `"<unnamed>"`.
fn sentence_name(attributes: &Attributes) -> String {
    if let Some(id) = string_attribute(attributes, KoreAttribute::UniqueId) {
        return id.to_owned();
    }
    if let Some(label) = string_attribute(attributes, KoreAttribute::Label) {
        return label.to_owned();
    }
    match (
        string_attribute(attributes, KoreAttribute::Source),
        string_attribute(attributes, KoreAttribute::Location),
    ) {
        (Some(source), Some(location)) => format!("{source} {location}"),
        (Some(source), None) => source.to_owned(),
        _ => "<unnamed>".to_owned(),
    }
}

/// The head symbol of the left-hand side of an equation or rewrite axiom
/// (`\implies(requires, \equals(lhs, rhs))`, `\equals(lhs, rhs)`, `\rewrites(lhs, rhs)`, under
/// binders), when it is an application.
fn axiom_head(pattern: &Pattern) -> Option<&str> {
    match pattern {
        Pattern::Implies { right, .. } => axiom_head(right),
        Pattern::Forall { body, .. } | Pattern::Exists { body, .. } => axiom_head(body),
        Pattern::Equals { left, .. } | Pattern::Rewrites { left, .. } => term_head(left),
        _ => None,
    }
}

fn term_head(pattern: &Pattern) -> Option<&str> {
    match pattern {
        Pattern::Application { symbol, .. } => Some(symbol.name.as_str()),
        Pattern::And { arguments, .. } => arguments.iter().find_map(|argument| match argument {
            Pattern::Application { symbol, .. } => Some(symbol.name.as_str()),
            _ => None,
        }),
        _ => None,
    }
}
