//! The results that fail today, each with the set of tickets that must all land before it
//! passes: an entry passes only when every ticket of its set has landed, so a ticket's acceptance
//! is that every entry whose set it completes leaves the list, and that every other entry naming
//! it keeps its kind and changes its signature only in that ticket's own sentences.
//!
//! The tickets, and the reason each of their results fails:
//! - `BIND/A3` (FU-26, FU-32/D1) has landed and holds no entry: the converter binds exactly a
//!   quantifier's own variable, whatever its spelling, so a quantifier over an anonymous
//!   variable binds nothing but itself; a variable of a rule's condition alone is quantified
//!   existentially inside the condition, in the rule's axiom and in the owise competitor that
//!   restates it (a search pattern's free variables are existential already), in the order of
//!   first occurrence; and an owise competitor's outer binders follow their sorts and first
//!   occurrences, never the spellings of the names minted for them (`condition-only/*`,
//!   `owise-cross/*-minted-*`).
//! - `BIND/A4` (FU-33/D2) has landed and holds no entry of its own: existential lifting
//!   quantifies the `?` variables free in the right side or the `ensures`, so a `?` variable that
//!   only a binder there binds is not lifted again (named `?` binders, and a `?` binder renamed
//!   apart from a free right-side `?Y`).
//! - `BIND/A3` and `BIND/A4` together have landed and hold no entry: an anonymous `?_` binder in
//!   the `ensures` binds only itself, so the body's `?_` is lifted and no lifted binder is vacuous.
//! - `BIND/A5` (FU-34/D3, FU-39) has landed and holds no entry of its own: the definition check
//!   binds a binder's variable in the binder's body only, so a right-side variable spelled like an
//!   `ensures` binder is unbound, and the parser's sort inference gives each binder's variable its
//!   own sort within its scope, so the parse stage of every source twin (`text-shadow-*-parse`) is
//!   the base's parse with the binder renamed.
//! - `BIND/A5` and `BIND/A6` together: a compiled source twin (`text-shadow-*`), and a base with
//!   one name bound at two sorts in separate scopes. Both have landed and the set holds no
//!   entry: the scope-correct parse loads both, and the binders are renamed apart before
//!   `resolve semantic casts` reads cast bounds.
//! - `BIND/A6` (FU-35/D4, FU-36/D5, and the name maps after them) has landed for binding: the
//!   first transformation stage renames each bound variable whose name occurs elsewhere in its
//!   sentence (the search route renames its pattern the same way), so macro substitution,
//!   `minimize term construction`, cast resolution, the search route's sort predicates and every
//!   later name map read one name as one variable, and the rule `UNIQUE_ID` digest numbers a
//!   quantifier's variable as its own. It holds no entry of its own. A binder whose name only a
//!   variable-naming attribute mentions (`concrete(Z)` beside `#Exists Z . P`) is renamed apart
//!   from it: an attribute lies outside every quantifier's scope, so it names a free variable of
//!   the rule or none, and such a rule is refused whatever its binder is called (`attribute/*`).
//!   Renaming apart also showed two defects the old spelling merges hid: a `?` binder in the
//!   `ensures` beside a free right-side `?Y` was lifted to a vacuous outer binder
//!   (`existential/*-q-shadow`, fixed by A4), and a macro binder minted at a use site, or a
//!   competitor's anonymous binder in a rule that no longer fails to compile, binds the use
//!   site's anonymous variables (`macro/*-anon-*`, `owise/anon-*-Y-*`, fixed by A3).
//! - FU-53, an out-of-scope class and no BIND ticket: a rule `UNIQUE_ID` digests the names a
//!   variable-naming attribute lists (`concrete(X)`, `symbolic(X)`: the prelude, `concrete-rw2`)
//!   and the labels of the functions a `#fun` or `#let` lowers to, which carry a variable's
//!   spelling, as written. Normalizing them would change the identifier of nearly every corpus
//!   definition (the prelude's `concrete` lemmas), so they stay spelling-dependent by design,
//!   as claim identifiers do (FU-44), and alpha-variants that differ there have distinct
//!   identifiers and the same answers (kind `Id`).
//! - `BIND/A7` (FU-37/D6, and orderings by spelling) has landed and holds no entry: the
//!   strictness variables avoid every name of a context alias, fresh constants take their counter
//!   offsets by first occurrence, and the search route conjoins the sort tests of casts to one
//!   sort by first occurrence. Its landing also cleared the search-pattern `A6` entries whose
//!   renamings only reordered those tests (`search/shapes`, and `search-named-apart` and
//!   `search-named-capture` under `binder-apart` or `rotate`); the captures left then, where a
//!   renaming merged or split the tests, were cleared by A6's renaming apart and by MLP/9, which
//!   places the sort test of a cast of a bound variable inside its binder.
//!
//! An entry's needle is its result's whole signature (every differing sentence, the first
//! differing run and the first identifier difference), so a second defect in a listed result
//! changes the signature and fails the test until the entry is updated.

pub use super::harness::Kind;

/// The fixed texts of the reports: the kinds' templates and the labels of a signature. A needle
/// made of these alone binds an entry to its kind and nothing more.
const GENERIC: &[&str] = &[
    "the base panics",
    "the variant panics",
    "load panics",
    "load refused",
    "the base compiles and the variant is refused",
    "the base is refused",
    "and the variant compiles",
    "is alpha-equivalent, and its UNIQUE_ID differs",
    "UNIQUE_ID not alpha-invariant",
    "UNIQUE_ID differs",
    "UNIQUE_ID",
    "could not parse rule",
    "the compiled search patterns differ",
    "differs:",
    "variant refused",
    "base refused",
    "variant pattern",
    "base pattern",
    "pattern: base",
    "base:",
    "variant:",
    "variant",
    "base",
    "under all",
    "under any",
    "run ",
    "at: ",
    "sentence",
    "-heat",
    "MACROS",
    "K3",
];

/// Whether `needle` is specific: at least 12 characters, of which something beyond the fixed
/// texts of the reports ([`GENERIC`]) is a name or a number.
pub fn needle_is_specific(needle: &str) -> bool {
    let mut rest = needle.to_owned();
    for generic in GENERIC {
        rest = rest.replace(generic, " ");
    }
    needle.chars().count() >= 12 && rest.chars().filter(|c| c.is_alphanumeric()).count() >= 2
}

/// One expected failure: the case, the result (a strategy, a twin or a pattern's variant, or `*`
/// for a failure of the base itself), the set of tickets that must all land before it passes,
/// the kind of failure and its signature, with the portable build's signature where it differs:
/// a run's leaves (the portable backend decides no SMT query) or a parser refusal's message (the
/// native build infers sorts with Z3).
pub struct Expected {
    pub case: &'static str,
    pub strategy: &'static str,
    pub tickets: &'static [&'static str],
    pub kind: Kind,
    pub needle: &'static str,
    pub portable: Option<&'static str>,
}

/// The ticket sets of the entries, by name.
pub const A3: &[&str] = &["BIND/A3"];
pub const A3_A4: &[&str] = &["BIND/A3", "BIND/A4"];
pub const A4: &[&str] = &["BIND/A4"];
pub const A5: &[&str] = &["BIND/A5"];
pub const A5_A6: &[&str] = &["BIND/A5", "BIND/A6"];
pub const A6: &[&str] = &["BIND/A6"];
pub const A7: &[&str] = &["BIND/A7"];
pub const FU53: &[&str] = &["FU-53"];

/// Every ticket set an entry may name, with the name of its constant.
pub const TICKET_SETS: &[(&str, &[&str])] = &[
    ("A3", A3),
    ("A3_A4", A3_A4),
    ("A4", A4),
    ("A5", A5),
    ("A5_A6", A5_A6),
    ("A6", A6),
    ("A7", A7),
    ("FU53", FU53),
];

/// The name of the constant of a ticket set, for the listing.
pub fn ticket_set_name(tickets: &[&str]) -> &'static str {
    TICKET_SETS
        .iter()
        .find(|(_, set)| *set == tickets)
        .map_or("?", |(name, _)| name)
}

impl Expected {
    pub fn key(&self) -> String {
        format!("{} {}", self.case, self.strategy)
    }

    /// The signature this build gives: the native build's (`z3-inference`), or the portable
    /// build's.
    pub fn signature(&self) -> &'static str {
        if cfg!(feature = "z3-inference") {
            self.needle
        } else {
            self.portable.unwrap_or(self.needle)
        }
    }
}

const fn expected(
    case: &'static str,
    strategy: &'static str,
    tickets: &'static [&'static str],
    kind: Kind,
    needle: &'static str,
) -> Expected {
    Expected {
        case,
        strategy,
        tickets,
        kind,
        needle,
        portable: None,
    }
}

/// An expected failure whose signature differs by build: `native` is the native build's
/// signature and `portable` the portable build's. No entry needs it while every listed result
/// fails alike in both builds; the regenerator writes it when one does not.
#[allow(dead_code)]
const fn expected_by_build(
    case: &'static str,
    strategy: &'static str,
    tickets: &'static [&'static str],
    kind: Kind,
    native: &'static str,
    portable: &'static str,
) -> Expected {
    Expected {
        case,
        strategy,
        tickets,
        kind,
        needle: native,
        portable: Some(portable),
    }
}

#[rustfmt::skip]
pub const EXPECTED: &[Expected] = &[
    // FU53 (43)
    expected("compile/concrete-rw2", "fresh", FU53, Kind::Id, "CONCRETE-RW2.test.k:4:3: UNIQUE_ID not alpha-invariant; CONCRETE-RW2.test.k:5:3: UNIQUE_ID not alpha-invariant; CONCRETE-RW2.test.k:7:3: UNIQUE_ID not alpha-invariant"),
    expected("compile/concrete-rw2", "k-index", FU53, Kind::Id, "CONCRETE-RW2.test.k:4:3: UNIQUE_ID not alpha-invariant; CONCRETE-RW2.test.k:5:3: UNIQUE_ID not alpha-invariant; CONCRETE-RW2.test.k:7:3: UNIQUE_ID not alpha-invariant"),
    expected("compile/let-list-binder", "fresh", FU53, Kind::Id, "LET-LIST-BINDER.test.k:15:3: UNIQUE_ID not alpha-invariant; LET-LIST-BINDER.test.k:18:3: UNIQUE_ID not alpha-invariant; LET-LIST-BINDER.test.k:21:3: UNIQUE_ID not alpha-invariant; LET-LIST-BINDER.02b077d04cae75986c1173b0655837ffe68b37158f734313528da812c89052f2: UNIQUE_ID not alpha-invariant; LET-LIST-BINDER.438e1166fbaa405ea5a77d0db2d26349905424c7d0b63debbe5adb200a024caa: UNIQUE_ID not alpha-invariant; LET-LIST-BINDER.c771ea7e874175f5e7ea0350711a0dca7d9c71391f0ef37ad35c4ecbb3fd4f6c: UNIQUE_ID not alpha-invariant"),
    expected("compile/let-list-binder", "k-index", FU53, Kind::Id, "LET-LIST-BINDER.test.k:15:3: UNIQUE_ID not alpha-invariant; LET-LIST-BINDER.test.k:18:3: UNIQUE_ID not alpha-invariant; LET-LIST-BINDER.test.k:21:3: UNIQUE_ID not alpha-invariant; LET-LIST-BINDER.02b077d04cae75986c1173b0655837ffe68b37158f734313528da812c89052f2: UNIQUE_ID not alpha-invariant; LET-LIST-BINDER.438e1166fbaa405ea5a77d0db2d26349905424c7d0b63debbe5adb200a024caa: UNIQUE_ID not alpha-invariant; LET-LIST-BINDER.c771ea7e874175f5e7ea0350711a0dca7d9c71391f0ef37ad35c4ecbb3fd4f6c: UNIQUE_ID not alpha-invariant"),
    expected("compile/let-list-binder", "rotate", FU53, Kind::Id, "LET-LIST-BINDER.test.k:15:3: UNIQUE_ID not alpha-invariant; LET-LIST-BINDER.test.k:18:3: UNIQUE_ID not alpha-invariant; LET-LIST-BINDER.test.k:21:3: UNIQUE_ID not alpha-invariant; LET-LIST-BINDER.02b077d04cae75986c1173b0655837ffe68b37158f734313528da812c89052f2: UNIQUE_ID not alpha-invariant; LET-LIST-BINDER.438e1166fbaa405ea5a77d0db2d26349905424c7d0b63debbe5adb200a024caa: UNIQUE_ID not alpha-invariant; LET-LIST-BINDER.c771ea7e874175f5e7ea0350711a0dca7d9c71391f0ef37ad35c4ecbb3fd4f6c: UNIQUE_ID not alpha-invariant"),
    expected("fixture/fixtures/sentence-typing/collection-cell-content.k", "fresh", FU53, Kind::Id, "TEST.TEST.applied: UNIQUE_ID not alpha-invariant; TEST.03238f622891452911e6e18b3650ec239fb865826a37a39f5ff871bffdcd125b: UNIQUE_ID not alpha-invariant"),
    expected("fixture/fixtures/sentence-typing/collection-cell-content.k", "k-index", FU53, Kind::Id, "TEST.TEST.applied: UNIQUE_ID not alpha-invariant; TEST.03238f622891452911e6e18b3650ec239fb865826a37a39f5ff871bffdcd125b: UNIQUE_ID not alpha-invariant"),
    expected("fixture/fixtures/sentence-typing/collection-cell-content.k", "rotate", FU53, Kind::Id, "TEST.TEST.applied: UNIQUE_ID not alpha-invariant; TEST.03238f622891452911e6e18b3650ec239fb865826a37a39f5ff871bffdcd125b: UNIQUE_ID not alpha-invariant"),
    expected("fixture/fixtures/sentence-typing/generated-rule-syntax.k", "fresh", FU53, Kind::Id, "TYPER-PROBE.TYPER-PROBE.let: UNIQUE_ID not alpha-invariant; TYPER-PROBE.TYPER-PROBE.fun: UNIQUE_ID not alpha-invariant; TYPER-PROBE.TYPER-PROBE.fun-cast: UNIQUE_ID not alpha-invariant; TYPER-PROBE.8c96a11bc12e0b2cfc8f0645085ea33cade6ae22d5182aa89c99d56857de4643: UNIQUE_ID not alpha-invariant; TYPER-PROBE.960bbc25cfbc882d80b129238abc34ee5264a9943c1783415eac6633fdab9b3d: UNIQUE_ID not alpha-invariant; TYPER-PROBE.2dd31814f3c4ff68dce298fbb5acddfa814819f270157c4a75a8cb436d0d978b: UNIQUE_ID not alpha-invariant"),
    expected("fixture/fixtures/sentence-typing/generated-rule-syntax.k", "k-index", FU53, Kind::Id, "TYPER-PROBE.TYPER-PROBE.let: UNIQUE_ID not alpha-invariant; TYPER-PROBE.TYPER-PROBE.fun: UNIQUE_ID not alpha-invariant; TYPER-PROBE.TYPER-PROBE.fun-cast: UNIQUE_ID not alpha-invariant; TYPER-PROBE.8c96a11bc12e0b2cfc8f0645085ea33cade6ae22d5182aa89c99d56857de4643: UNIQUE_ID not alpha-invariant; TYPER-PROBE.960bbc25cfbc882d80b129238abc34ee5264a9943c1783415eac6633fdab9b3d: UNIQUE_ID not alpha-invariant; TYPER-PROBE.2dd31814f3c4ff68dce298fbb5acddfa814819f270157c4a75a8cb436d0d978b: UNIQUE_ID not alpha-invariant"),
    expected("fixture/fixtures/sentence-typing/generated-rule-syntax.k", "rotate", FU53, Kind::Id, "TYPER-PROBE.TYPER-PROBE.let: UNIQUE_ID not alpha-invariant; TYPER-PROBE.TYPER-PROBE.fun: UNIQUE_ID not alpha-invariant; TYPER-PROBE.TYPER-PROBE.fun-cast: UNIQUE_ID not alpha-invariant; TYPER-PROBE.8c96a11bc12e0b2cfc8f0645085ea33cade6ae22d5182aa89c99d56857de4643: UNIQUE_ID not alpha-invariant; TYPER-PROBE.960bbc25cfbc882d80b129238abc34ee5264a9943c1783415eac6633fdab9b3d: UNIQUE_ID not alpha-invariant; TYPER-PROBE.2dd31814f3c4ff68dce298fbb5acddfa814819f270157c4a75a8cb436d0d978b: UNIQUE_ID not alpha-invariant"),
    expected("fixture/fixtures/sentence-typing/regression/equals-pattern.k", "fresh", FU53, Kind::Id, "TEST.equals-pattern.k:23:1: UNIQUE_ID not alpha-invariant; TEST.equals-pattern.k:27:1: UNIQUE_ID not alpha-invariant; TEST.equals-pattern.k:30:1: UNIQUE_ID not alpha-invariant; TEST.8242c7e2f30c75c5e204c9266babeb31ece651ab6e08fd2c6db7b35ef810ca65: UNIQUE_ID not alpha-invariant; TEST.a953dadfd0037faa70566c7252d1ef24b9b19152b82a838bf3b3fe153376f3cd: UNIQUE_ID not alpha-invariant; TEST.1121eb11f4bd4afb8d3e5967cbd2dccc1ec7542fdfd65d98a1d0334d147092ed: UNIQUE_ID not alpha-invariant; TEST.3aa01781829292aba837d156247cb9e4a6bdd05a4bedfd35cdc32da08939ebdc: UNIQUE_ID not alpha-invariant; TEST.cd6a17ec30fa1c4c020be3af92b2bc24c841acf72e514eebc4910686fa40ad0d: UNIQUE_ID not alpha-invariant; TEST.17b63af2b2715ba78e9c744e3e0a84ee80bf4125effa20b21dc6868df9c9d291: UNIQUE_ID not alpha-invariant; TEST.66a82ad6a1f5ebbcb620c6710ee0e03cd8100672949dc3d257199708d5f194af: UNIQUE_ID not alpha-invariant; TEST.b9a5d729a21fc25f97d91077062eb2256761e54f9907628a02a289bb697b72e4: UNIQUE_ID not alpha-invariant; TEST.dd9c165e7dfe5f914f9515a12c78dc0da72e42d9f68dcaa0a84cf5bf249c7c07: UNIQUE_ID not alpha-invariant; TEST.d1b0d3dee9a5dac0b1443fa8f1aa6bc984e366b1c32d6b5e1a8c6d1764951f02: UNIQUE_ID not alpha-invariant; TEST.38d84a60a3333c7ca31e8d728cdab68b34c6a393d637533007cf3577892a64a5: UNIQUE_ID not alpha-invariant; TEST.d0ecedb2582bfc08d12df627cd55533bcf0d37d45b48d5ba3db2fbcad9267104: UNIQUE_ID not alpha-invariant"),
    expected("fixture/fixtures/sentence-typing/regression/equals-pattern.k", "k-index", FU53, Kind::Id, "TEST.equals-pattern.k:23:1: UNIQUE_ID not alpha-invariant; TEST.equals-pattern.k:27:1: UNIQUE_ID not alpha-invariant; TEST.equals-pattern.k:30:1: UNIQUE_ID not alpha-invariant; TEST.8242c7e2f30c75c5e204c9266babeb31ece651ab6e08fd2c6db7b35ef810ca65: UNIQUE_ID not alpha-invariant; TEST.a953dadfd0037faa70566c7252d1ef24b9b19152b82a838bf3b3fe153376f3cd: UNIQUE_ID not alpha-invariant; TEST.1121eb11f4bd4afb8d3e5967cbd2dccc1ec7542fdfd65d98a1d0334d147092ed: UNIQUE_ID not alpha-invariant; TEST.3aa01781829292aba837d156247cb9e4a6bdd05a4bedfd35cdc32da08939ebdc: UNIQUE_ID not alpha-invariant; TEST.cd6a17ec30fa1c4c020be3af92b2bc24c841acf72e514eebc4910686fa40ad0d: UNIQUE_ID not alpha-invariant; TEST.17b63af2b2715ba78e9c744e3e0a84ee80bf4125effa20b21dc6868df9c9d291: UNIQUE_ID not alpha-invariant; TEST.66a82ad6a1f5ebbcb620c6710ee0e03cd8100672949dc3d257199708d5f194af: UNIQUE_ID not alpha-invariant; TEST.b9a5d729a21fc25f97d91077062eb2256761e54f9907628a02a289bb697b72e4: UNIQUE_ID not alpha-invariant; TEST.dd9c165e7dfe5f914f9515a12c78dc0da72e42d9f68dcaa0a84cf5bf249c7c07: UNIQUE_ID not alpha-invariant; TEST.d1b0d3dee9a5dac0b1443fa8f1aa6bc984e366b1c32d6b5e1a8c6d1764951f02: UNIQUE_ID not alpha-invariant; TEST.38d84a60a3333c7ca31e8d728cdab68b34c6a393d637533007cf3577892a64a5: UNIQUE_ID not alpha-invariant; TEST.d0ecedb2582bfc08d12df627cd55533bcf0d37d45b48d5ba3db2fbcad9267104: UNIQUE_ID not alpha-invariant"),
    expected("fixture/fixtures/sentence-typing/regression/equals-pattern.k", "rotate", FU53, Kind::Id, "TEST.equals-pattern.k:23:1: UNIQUE_ID not alpha-invariant; TEST.8242c7e2f30c75c5e204c9266babeb31ece651ab6e08fd2c6db7b35ef810ca65: UNIQUE_ID not alpha-invariant; TEST.a953dadfd0037faa70566c7252d1ef24b9b19152b82a838bf3b3fe153376f3cd: UNIQUE_ID not alpha-invariant; TEST.1121eb11f4bd4afb8d3e5967cbd2dccc1ec7542fdfd65d98a1d0334d147092ed: UNIQUE_ID not alpha-invariant; TEST.3aa01781829292aba837d156247cb9e4a6bdd05a4bedfd35cdc32da08939ebdc: UNIQUE_ID not alpha-invariant"),
    expected("fixture/fixtures/sentence-typing/regression/let-test.k", "fresh", FU53, Kind::Id, "TEST.let-test.k:11:3: UNIQUE_ID not alpha-invariant; TEST.4175653a3b772b2d5f99420cf747d8afc4c77bc977f9907b9ba40320730dd2f1: UNIQUE_ID not alpha-invariant; TEST.a3f5b72edc0dab7e8b33b84261cbe7ae5667bbda5930aceebae95c1b01fe5e1d: UNIQUE_ID not alpha-invariant; TEST.858746cc356908fdb0dda8ad9aa4acfa5a6a56371bffb49fcdfcc57cc2abb569: UNIQUE_ID not alpha-invariant; TEST.a5076e29b0e520a55576c9ff69c0a93b5f4fcae5fdb46a8ea2aede0743b0ebb2: UNIQUE_ID not alpha-invariant; TEST.a12288107c87da68834d35db6f658301b01a56c592177b3045a5f87218bc6349: UNIQUE_ID not alpha-invariant; TEST.aaceb3a9b4d16003cd94aa0b7875d0445f5a5c05f9ec9153f65ee936a98733cc: UNIQUE_ID not alpha-invariant"),
    expected("fixture/fixtures/sentence-typing/regression/let-test.k", "k-index", FU53, Kind::Id, "TEST.let-test.k:11:3: UNIQUE_ID not alpha-invariant; TEST.4175653a3b772b2d5f99420cf747d8afc4c77bc977f9907b9ba40320730dd2f1: UNIQUE_ID not alpha-invariant; TEST.a3f5b72edc0dab7e8b33b84261cbe7ae5667bbda5930aceebae95c1b01fe5e1d: UNIQUE_ID not alpha-invariant; TEST.858746cc356908fdb0dda8ad9aa4acfa5a6a56371bffb49fcdfcc57cc2abb569: UNIQUE_ID not alpha-invariant; TEST.a5076e29b0e520a55576c9ff69c0a93b5f4fcae5fdb46a8ea2aede0743b0ebb2: UNIQUE_ID not alpha-invariant; TEST.a12288107c87da68834d35db6f658301b01a56c592177b3045a5f87218bc6349: UNIQUE_ID not alpha-invariant; TEST.aaceb3a9b4d16003cd94aa0b7875d0445f5a5c05f9ec9153f65ee936a98733cc: UNIQUE_ID not alpha-invariant"),
    expected("fixture/fixtures/sentence-typing/regression/let-test.k", "rotate", FU53, Kind::Id, "TEST.let-test.k:11:3: UNIQUE_ID not alpha-invariant; TEST.4175653a3b772b2d5f99420cf747d8afc4c77bc977f9907b9ba40320730dd2f1: UNIQUE_ID not alpha-invariant; TEST.a3f5b72edc0dab7e8b33b84261cbe7ae5667bbda5930aceebae95c1b01fe5e1d: UNIQUE_ID not alpha-invariant; TEST.858746cc356908fdb0dda8ad9aa4acfa5a6a56371bffb49fcdfcc57cc2abb569: UNIQUE_ID not alpha-invariant; TEST.a5076e29b0e520a55576c9ff69c0a93b5f4fcae5fdb46a8ea2aede0743b0ebb2: UNIQUE_ID not alpha-invariant; TEST.a12288107c87da68834d35db6f658301b01a56c592177b3045a5f87218bc6349: UNIQUE_ID not alpha-invariant; TEST.aaceb3a9b4d16003cd94aa0b7875d0445f5a5c05f9ec9153f65ee936a98733cc: UNIQUE_ID not alpha-invariant"),
    expected("fun-parameter-other-sort", "fresh", FU53, Kind::Id, "LAMB.LAMB.p: UNIQUE_ID not alpha-invariant; LAMB.45f388d96e587e310770583c32298636db3315ef5d840709a1e5e9e19931e165: UNIQUE_ID not alpha-invariant"),
    expected("fun-parameter-other-sort", "k-index", FU53, Kind::Id, "LAMB.LAMB.p: UNIQUE_ID not alpha-invariant; LAMB.45f388d96e587e310770583c32298636db3315ef5d840709a1e5e9e19931e165: UNIQUE_ID not alpha-invariant"),
    expected("fun-parameter-other-sort", "rotate", FU53, Kind::Id, "LAMB.LAMB.p: UNIQUE_ID not alpha-invariant; LAMB.45f388d96e587e310770583c32298636db3315ef5d840709a1e5e9e19931e165: UNIQUE_ID not alpha-invariant"),
    expected("lambda/fun-fresh", "fresh", FU53, Kind::Id, "G.G.p: UNIQUE_ID not alpha-invariant; G.8c96a11bc12e0b2cfc8f0645085ea33cade6ae22d5182aa89c99d56857de4643: UNIQUE_ID not alpha-invariant"),
    expected("lambda/fun-fresh", "k-index", FU53, Kind::Id, "G.G.p: UNIQUE_ID not alpha-invariant; G.8c96a11bc12e0b2cfc8f0645085ea33cade6ae22d5182aa89c99d56857de4643: UNIQUE_ID not alpha-invariant"),
    expected("lambda/fun-fresh", "rotate", FU53, Kind::Id, "G.G.p: UNIQUE_ID not alpha-invariant; G.8c96a11bc12e0b2cfc8f0645085ea33cade6ae22d5182aa89c99d56857de4643: UNIQUE_ID not alpha-invariant"),
    expected("lambda/fun-lhs", "fresh", FU53, Kind::Id, "G.G.p: UNIQUE_ID not alpha-invariant; G.8c96a11bc12e0b2cfc8f0645085ea33cade6ae22d5182aa89c99d56857de4643: UNIQUE_ID not alpha-invariant"),
    expected("lambda/fun-lhs", "k-index", FU53, Kind::Id, "G.G.p: UNIQUE_ID not alpha-invariant; G.8c96a11bc12e0b2cfc8f0645085ea33cade6ae22d5182aa89c99d56857de4643: UNIQUE_ID not alpha-invariant"),
    expected("lambda/fun-other-sort-annotated", "fresh", FU53, Kind::Id, "G.G.p: UNIQUE_ID not alpha-invariant; G.45f388d96e587e310770583c32298636db3315ef5d840709a1e5e9e19931e165: UNIQUE_ID not alpha-invariant"),
    expected("lambda/fun-other-sort-annotated", "k-index", FU53, Kind::Id, "G.G.p: UNIQUE_ID not alpha-invariant; G.45f388d96e587e310770583c32298636db3315ef5d840709a1e5e9e19931e165: UNIQUE_ID not alpha-invariant"),
    expected("lambda/fun-other-sort-annotated", "rotate", FU53, Kind::Id, "G.G.p: UNIQUE_ID not alpha-invariant; G.45f388d96e587e310770583c32298636db3315ef5d840709a1e5e9e19931e165: UNIQUE_ID not alpha-invariant"),
    expected("lambda/fun-other-sort-inferred", "fresh", FU53, Kind::Id, "G.G.p: UNIQUE_ID not alpha-invariant; G.45f388d96e587e310770583c32298636db3315ef5d840709a1e5e9e19931e165: UNIQUE_ID not alpha-invariant"),
    expected("lambda/fun-other-sort-inferred", "k-index", FU53, Kind::Id, "G.G.p: UNIQUE_ID not alpha-invariant; G.45f388d96e587e310770583c32298636db3315ef5d840709a1e5e9e19931e165: UNIQUE_ID not alpha-invariant"),
    expected("lambda/fun-other-sort-inferred", "rotate", FU53, Kind::Id, "G.G.p: UNIQUE_ID not alpha-invariant; G.45f388d96e587e310770583c32298636db3315ef5d840709a1e5e9e19931e165: UNIQUE_ID not alpha-invariant"),
    expected("lambda/let-other-sort-annotated", "fresh", FU53, Kind::Id, "G.G.p: UNIQUE_ID not alpha-invariant; G.45f388d96e587e310770583c32298636db3315ef5d840709a1e5e9e19931e165: UNIQUE_ID not alpha-invariant"),
    expected("lambda/let-other-sort-annotated", "k-index", FU53, Kind::Id, "G.G.p: UNIQUE_ID not alpha-invariant; G.45f388d96e587e310770583c32298636db3315ef5d840709a1e5e9e19931e165: UNIQUE_ID not alpha-invariant"),
    expected("lambda/let-other-sort-annotated", "rotate", FU53, Kind::Id, "G.G.p: UNIQUE_ID not alpha-invariant; G.45f388d96e587e310770583c32298636db3315ef5d840709a1e5e9e19931e165: UNIQUE_ID not alpha-invariant"),
    expected("lambda/let-other-sort-inferred", "fresh", FU53, Kind::Id, "G.G.p: UNIQUE_ID not alpha-invariant; G.45f388d96e587e310770583c32298636db3315ef5d840709a1e5e9e19931e165: UNIQUE_ID not alpha-invariant"),
    expected("lambda/let-other-sort-inferred", "k-index", FU53, Kind::Id, "G.G.p: UNIQUE_ID not alpha-invariant; G.45f388d96e587e310770583c32298636db3315ef5d840709a1e5e9e19931e165: UNIQUE_ID not alpha-invariant"),
    expected("lambda/let-other-sort-inferred", "rotate", FU53, Kind::Id, "G.G.p: UNIQUE_ID not alpha-invariant; G.45f388d96e587e310770583c32298636db3315ef5d840709a1e5e9e19931e165: UNIQUE_ID not alpha-invariant"),
    expected("let-parameter-other-sort", "fresh", FU53, Kind::Id, "LETB.LETB.p: UNIQUE_ID not alpha-invariant; LETB.45f388d96e587e310770583c32298636db3315ef5d840709a1e5e9e19931e165: UNIQUE_ID not alpha-invariant"),
    expected("let-parameter-other-sort", "k-index", FU53, Kind::Id, "LETB.LETB.p: UNIQUE_ID not alpha-invariant; LETB.45f388d96e587e310770583c32298636db3315ef5d840709a1e5e9e19931e165: UNIQUE_ID not alpha-invariant"),
    expected("let-parameter-other-sort", "rotate", FU53, Kind::Id, "LETB.LETB.p: UNIQUE_ID not alpha-invariant; LETB.45f388d96e587e310770583c32298636db3315ef5d840709a1e5e9e19931e165: UNIQUE_ID not alpha-invariant"),
    expected("prelude", "fresh", FU53, Kind::Id, "MAIN.domains.md:1415:3: UNIQUE_ID not alpha-invariant; MAIN.domains.md:1416:3: UNIQUE_ID not alpha-invariant; MAIN.domains.md:1418:3: UNIQUE_ID not alpha-invariant; MAIN.domains.md:1419:3: UNIQUE_ID not alpha-invariant; MAIN.domains.md:1420:3: UNIQUE_ID not alpha-invariant; MAIN.domains.md:1421:3: UNIQUE_ID not alpha-invariant; MAIN.domains.md:1422:3: UNIQUE_ID not alpha-invariant; MAIN.domains.md:1423:3: UNIQUE_ID not alpha-invariant; MAIN.domains.md:1424:3: UNIQUE_ID not alpha-invariant; MAIN.domains.md:1425:3: UNIQUE_ID not alpha-invariant; MAIN.domains.md:1426:3: UNIQUE_ID not alpha-invariant; MAIN.domains.md:1428:3: UNIQUE_ID not alpha-invariant"),
    expected("prelude", "k-index", FU53, Kind::Id, "MAIN.domains.md:1415:3: UNIQUE_ID not alpha-invariant; MAIN.domains.md:1416:3: UNIQUE_ID not alpha-invariant; MAIN.domains.md:1418:3: UNIQUE_ID not alpha-invariant; MAIN.domains.md:1419:3: UNIQUE_ID not alpha-invariant; MAIN.domains.md:1420:3: UNIQUE_ID not alpha-invariant; MAIN.domains.md:1421:3: UNIQUE_ID not alpha-invariant; MAIN.domains.md:1422:3: UNIQUE_ID not alpha-invariant; MAIN.domains.md:1423:3: UNIQUE_ID not alpha-invariant; MAIN.domains.md:1424:3: UNIQUE_ID not alpha-invariant; MAIN.domains.md:1425:3: UNIQUE_ID not alpha-invariant; MAIN.domains.md:1426:3: UNIQUE_ID not alpha-invariant; MAIN.domains.md:1428:3: UNIQUE_ID not alpha-invariant"),
    expected("prelude", "rotate", FU53, Kind::Id, "MAIN.domains.md:1415:3: UNIQUE_ID not alpha-invariant; MAIN.domains.md:1416:3: UNIQUE_ID not alpha-invariant; MAIN.domains.md:1418:3: UNIQUE_ID not alpha-invariant; MAIN.domains.md:1419:3: UNIQUE_ID not alpha-invariant; MAIN.domains.md:1420:3: UNIQUE_ID not alpha-invariant; MAIN.domains.md:1421:3: UNIQUE_ID not alpha-invariant; MAIN.domains.md:1422:3: UNIQUE_ID not alpha-invariant; MAIN.domains.md:1423:3: UNIQUE_ID not alpha-invariant; MAIN.domains.md:1424:3: UNIQUE_ID not alpha-invariant; MAIN.domains.md:1425:3: UNIQUE_ID not alpha-invariant; MAIN.domains.md:1426:3: UNIQUE_ID not alpha-invariant; MAIN.domains.md:1428:3: UNIQUE_ID not alpha-invariant"),
];
