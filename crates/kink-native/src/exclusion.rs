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
//!   definition is inconsistent there, and any verdict follows from an inconsistent theory. Under
//!   PathSet (the only modality kink requests) a `Trivial` leaf's rule id is its own rule; under
//!   StateSet it is witness metadata, and closing the case there needs k-rust's flag (KINK-18).
//! - [`Exclusion::ImplementationChosenHook`]: the definition references a hook for which k-rust
//!   chooses a value the definition leaves open (re-pin decision 1, findings D-10, E-10, E-11):
//!   kills are relative to the definition, not to k-rust's model of it. The hooks are k-rust's
//!   own list and those whose value k-rust's builtin files (`domains.md`, `substitution.md`,
//!   `json.md`, `timer.md`, `ffi.md`, `unification.k`) leave to the backend, the implementation
//!   or the environment ([`IMPLEMENTATION_CHOSEN_HOOKS`], [`DOMAINS_OPEN_HOOKS`],
//!   [`BUILTIN_OPEN_HOOKS`]). The census reads the definition's own sentences and every rewrite
//!   rule whatever its source: kompile copies the prelude's stream rules (`#getc`, `#write`,
//!   `Float2String`) into a definition with stream cells, keeping their prelude source.
//! - [`Exclusion::ShortCircuitReading`]: the run's result can depend on whether `andBool`,
//!   `orBool`, `impliesBool`, `#if`, `andThenBool` or `orElseBool` skip an operand that may be
//!   undefined
//!   (re-pin decision 1 applied to domains.md lines 1115-1117 and 2314-2317; R0c review 1 minor):
//!   k-rust evaluates every operand (an application is strict in all its arguments, k-rust
//!   `deferred.rs`), so such a step is undefined where a short-circuiting backend gives a value.
//!   A `Trivial` leaf of a rewrite rule whose right-hand side applies one makes the run
//!   excluded; a rule whose condition depends on one, or whose right-hand side applies a
//!   function whose condition does, gives no leaf signal (the rule is just not applied), so the
//!   definition is excluded ([`DefinitionExclusions::short_circuit_conditions`]).
//! - [`Exclusion::AllowanceRefusal`]: a leaf reports a hook left unevaluated whose refusal reads
//!   the process's memory allowance (Execute promise exclusion, findings A-07, B-02, B-07): the
//!   result is a function of the host, not of the inputs a key names.
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

use crate::execution::{AdaptedExecution, AdaptedLeaf, HaltClass};

/// The hooks for which k-rust 501f18b9 says it may compute a value the definition leaves open,
/// exactly the hooks for which its `implementation_chosen_in` (`k-rust-backend/src/builtin.rs`)
/// can return `Some`: the match arms (`MAP.keys_list`, `MAP.values`, `SET.set2list`,
/// `MAP.choice`, `SET.choice`), the six Float operations `float::mixed_destination` reads
/// (`BinaryOperation::of`) and `FLOAT.sign` (`float::nan_sign`). Pinned against the k-rust
/// source, and the source text of those functions by digest, by the kink-native test
/// `implementation_chosen_hooks_are_k_rusts`.
pub const K_RUST_IMPLEMENTATION_CHOSEN_HOOKS: &[&str] = &[
    "MAP.keys_list",
    "MAP.values",
    "SET.set2list",
    "MAP.choice",
    "SET.choice",
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
/// - `Base2String`'s letter case and `Float2String`'s string are "determined by the backend";
///   `Float2String` with a format is what `mpfr_printf` gives.
/// - `RangeMap`'s `choice` is "arbitrarily chosen", and its `keys_list` and `values` state no
///   order, as `Map`'s, which k-rust names.
/// - `randInt`/`srandInt` are pseudorandom on concrete backends and uninterpreted on symbolic
///   ones; the deprecated String hooks and the `K-REFLECTION` hooks that read the process or
///   the environment are "largely unsupported"; and every I/O hook returns what "the underlying
///   system call" gives (a `#read` may return "fewer characters than requested").
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
        "STRING.base2string",
        "1829-1831",
        "returned by `Base2String` are upper or lowercase is determined by the backend",
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
        "IO.read",
        "2548-2549",
        "resulting read characters are returned, which may be fewer characters than",
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
        "SUBSTITUTION.substOne",
        "83-88",
        "the rewriter will automatically assign unique names",
    ),
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

/// Decision 1's census hooks: [`K_RUST_IMPLEMENTATION_CHOSEN_HOOKS`], the hooks of
/// [`DOMAINS_OPEN_HOOKS`] and those of [`BUILTIN_OPEN_HOOKS`], in that order (the kink-native
/// test `implementation_chosen_hooks_are_k_rusts` checks that it is exactly their union).
pub const IMPLEMENTATION_CHOSEN_HOOKS: &[&str] = &[
    "MAP.keys_list",
    "MAP.values",
    "SET.set2list",
    "MAP.choice",
    "SET.choice",
    "FLOAT.add",
    "FLOAT.sub",
    "FLOAT.mul",
    "FLOAT.div",
    "FLOAT.min",
    "FLOAT.max",
    "FLOAT.sign",
    "BYTES.string2bytes",
    "BYTES.bytes2string",
    "STRING.base2string",
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
    "IO.read",
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
    "SUBSTITUTION.substOne",
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

/// The hooks of the operators whose operands a backend may or may not skip (domains.md
/// 1115-1117: `andBool` and `orBool` "may be short-circuited in concrete backends", and
/// `impliesBool` is `notBool P orBool Q`, 1110-1111; 2314-2317: `#if` "does not short-circuit
/// on symbolic backends"; 1115 calls `andThenBool` and `orElseBool` short-circuiting, but k-rust
/// reads their skipped operand's definedness too, so a step through one over an undefined
/// operand is undefined in k-rust where the text gives a value): re-pin decision 1 applied to the
/// short-circuit reading ([`Exclusion::ShortCircuitReading`]). Each with the argument positions a
/// backend may skip: both operands of a Boolean operator (a `[simplification]` such as
/// `_ andBool false => false` skips the left one), the branches of `#if`.
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
        }
    }
}

/// A non-prelude sentence of a definition that references a symbol with an
/// [`IMPLEMENTATION_CHOSEN_HOOKS`] hook.
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
    /// The non-prelude sentences that reference an implementation-chosen hook.
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
    /// The function symbols whose value depends on the short-circuit reading (an equation's
    /// condition or right-hand side does, directly or through another such symbol): a test's
    /// initial state that applies one is no evidence.
    pub short_circuit_symbols: BTreeSet<String>,
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
                IMPLEMENTATION_CHOSEN_HOOKS
                    .contains(&hook)
                    .then(|| (symbol.name.to_string(), hook.to_owned()))
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
                // copied into a definition with stream cells and keep their prelude source.
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
                if short_circuit.result(right)
                    && let Some(id) = string_attribute(attributes, KoreAttribute::UniqueId)
                {
                    short_circuit_rules.insert(id.to_owned());
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
            short_circuit_symbols: short_circuit
                .undefined
                .union(&short_circuit.valued)
                .cloned()
                .collect(),
        }
    }

    /// The exclusions of a compiled side loaded for `module` (its encoded KORE name) on this
    /// thread, as kink-campaign's runner computes them for a side it prepares.
    pub fn of_validated(side: &crate::ValidatedDefinition, module: &str) -> Result<Self, String> {
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
        Ok(Self::of(
            &kore,
            &selected,
            &side.compile_options().builtin_source_prefixes,
        ))
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
            short_circuit_symbols: self
                .short_circuit_symbols
                .union(&other.short_circuit_symbols)
                .cloned()
                .collect(),
        }
    }

    /// The exclusion every run on this definition has, if any: a load stack stop first, then an
    /// implementation-chosen hook, then a rule whose condition or value depends on the
    /// short-circuit reading.
    #[must_use]
    pub fn definition_exclusion(&self) -> Option<Exclusion> {
        if self.load_stack_stops > 0 {
            Some(Exclusion::LoadStackStop)
        } else if !self.implementation_chosen.is_empty() {
            Some(Exclusion::ImplementationChosenHook)
        } else if !self.short_circuit_conditions.is_empty() {
            Some(Exclusion::ShortCircuitReading)
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
    /// documentation): the definition's own, then a stack stop, a contradicted claim, an undefined
    /// step of a rule whose result depends on the short-circuit reading, and an allowance
    /// refusal, in that order. A timed-out run is a timeout before it is anything else, and is
    /// not asked.
    #[must_use]
    pub fn run_exclusion(&self, execution: &AdaptedExecution) -> Option<Exclusion> {
        if let Some(exclusion) = self.definition_exclusion() {
            return Some(exclusion);
        }
        if execution.stack_stops() > 0 {
            return Some(Exclusion::StackStop);
        }
        let leaves = execution.leaves();
        if leaves.iter().any(|leaf| self.contradicts_a_claim(leaf)) {
            return Some(Exclusion::ContradictedClaim);
        }
        if leaves.iter().any(|leaf| self.short_circuit_step(leaf)) {
            return Some(Exclusion::ShortCircuitReading);
        }
        if leaves.iter().any(allowance_refusal) {
            return Some(Exclusion::AllowanceRefusal);
        }
        None
    }

    /// Whether `leaf` is an undefined step that falsifies a trusted claim: k-rust names a
    /// contradicted `total` claim, or the leaf is `Trivial` and its rule carries
    /// `preserves-definedness`.
    #[must_use]
    pub fn contradicts_a_claim(&self, leaf: &AdaptedLeaf) -> bool {
        leaf.contradicted_total.is_some()
            || (leaf.halt == HaltClass::Trivial
                && leaf
                    .undefined_rule
                    .as_ref()
                    .is_some_and(|rule| self.preserves_definedness.contains(&rule.id)))
    }

    /// Whether `leaf` is an undefined step of a rewrite rule whose right-hand side applies a
    /// short-circuit operator over an operand that may be undefined (directly or through a
    /// function): k-rust reads the step as undefined, a short-circuiting backend may not.
    #[must_use]
    pub fn short_circuit_step(&self, leaf: &AdaptedLeaf) -> bool {
        leaf.halt == HaltClass::Trivial
            && leaf
                .undefined_rule
                .as_ref()
                .is_some_and(|rule| self.short_circuit_rules.contains(&rule.id))
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

    /// Whether `pattern` may be undefined: it applies a partial function, or a function that can
    /// be undefined in k-rust's reading.
    fn may_be_undefined(&self, pattern: &Pattern) -> bool {
        self.applies(pattern, &self.partial) || self.applies(pattern, &self.undefined)
    }

    /// Whether `pattern` applies a short-circuit operator with an operand a backend may skip
    /// that may be undefined.
    fn direct(&self, pattern: &Pattern) -> bool {
        let mut found = false;
        walk::for_each_post_order(pattern, |node| {
            if !found
                && let Pattern::Application { symbol, arguments } = node
                && let Some(positions) = self.operators.get(symbol.name.as_str())
            {
                found = positions.iter().any(|position| {
                    arguments
                        .get(*position)
                        .is_some_and(|argument| self.may_be_undefined(argument))
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
