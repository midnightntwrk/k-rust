//! The attribute axis (K8): every attribute an author writes on a sentence, on every sentence
//! form, and what it means there.
//!
//! An *attribute* is a key of a sentence's own marker (`#[k::rule(owise)]`,
//! `#[k::equation(concrete)]`, `#[k::claim(all_paths, trusted)]`) or a helper attribute written
//! beside it (`#[k::requires(..)]`, `#[k::ensures(..)]`, `#[k::exists(..)]`, `#[k::fresh(..)]`).
//! [`Attribute`] lists them, each with a representative well-formed value; the keys the product's
//! parsers recognize are read from the parsers by `tests/attributes.rs`, which fails on a key no
//! attribute covers, and the helper attributes from `krs_syntax::surface::AttributeMacro`.
//!
//! A *form* ([`FORMS`]) is one of the term family's sentence forms, by its slot name, with what
//! kind of sentence it is ([`Sentence`]). Each pair is one case, `attrs/FORM/ATTRIBUTE`, written
//! on the form's subject slot template (`class_matrix::terms`): the attribute in the form's own
//! marker, or a helper beside it. [`MALFORMED`] adds a few malformed values and the keys that
//! cannot stand together, on a form that takes the key.
//!
//! **The oracle** ([`expected`]) states what each attribute means on each kind of sentence, from
//! what the attribute denotes, never from what KRS does with it:
//!
//! - a sentence's *order* (`owise`, `priority = N`, `nondet = g`) chooses among the sentences of
//!   one kind that match one term: transitions, and a function's equations (`nondet` only among
//!   transitions, since a function is deterministic); a simplification's priority orders the
//!   simplifications a prover tries, and `owise` says where no other sentence applies, which a
//!   prover never decides. A claim is proved, a context and a context alias say where
//!   evaluation happens and are ordered by their hole, and a static production's clauses expand
//!   each of its applications, as the definition and a program are read, into one term, so they
//!   may not overlap (a production may have several clauses, each for its own shapes): none of
//!   them is chosen against another;
//! - `skipped_operand = ".."` states why a transition's or an equation's value or condition may
//!   depend on an operand `&&`, `||` or `kequal::ite` does not evaluate: `krs check` warns there,
//!   at the sentences of the definition, and the key silences that warning at the sentence it
//!   marks, or, on a function's marker (a function shorthand's), at the function's equations.
//!   Every other sentence is no transition or equation of the definition (a claim is proved
//!   against it), or is written by no marker of its own; the key states nothing about what the
//!   sentence means, so an accepted case emits the K it emits without the key. The warning, and
//!   its stale form where the key has nothing to silence, are the `native-rust` route's, which
//!   the axis does not judge, so a case owes no lint for it;
//! - `anywhere` makes a transition rewrite its subject's root application wherever it occurs, which
//!   a term-shaped transition has, a single-body rule's included (its subject's right image
//!   replaces the application); a configuration-shaped one matches cells, which occur only at
//!   their place, a `for Sort` clause's header anchors it at the head of the computation cell,
//!   which `anywhere` would contradict, and a function's equations apply wherever its application
//!   occurs already;
//! - `heat`/`cool` (with `hole = x`) make a transition a heating or cooling step, which K orders
//!   by whether its hole is a result; `result = S` names the sort a heated hole's evaluation ends
//!   in, which a context and a context alias name too, and which means nothing on a sentence
//!   that heats nothing;
//! - a context, and each position of a strict production, heats its hole while it is no result
//!   and cools it once it is a result of the step's sort `R` (`result = R` on the context, the
//!   strictness or the context alias the position is evaluated through, `KResult` otherwise):
//!   both steps match the hole at its sort `H`, so a term of the hole is cooled exactly when its
//!   sort is below both `H` and `R`. Where no sort that has terms is below both, nothing the
//!   heating moves is ever plugged back, and a run that reaches it stays under the freezer; that
//!   is well defined, so it is accepted with the lint `never-cools` ([`COOLINGS`], [`cools`]);
//! - `concrete`, `symbolic` and `smt_lemma` restrict when an equation or a simplification applies
//!   (or hand it to the solver): on a transition a restriction would leave out of a symbolic
//!   search the steps it applies to, which is unsound, and on the other forms there is no
//!   function application to restrict;
//! - `one_path`, `circularity` and `trusted` say how a claim is proved;
//! - a label names a sentence for what refers to its steps (a run's, a proof's, a trace's), as
//!   a clause's or a fn's name does by default, a function shorthand's one equation included: a
//!   context alias is named by its `name`, which the strict productions that use it refer to, a
//!   static clause takes no step, and an initializer and a constant are no sentence of the
//!   author's to name;
//! - `#[k::requires(c)]` makes a sentence apply only where `c` holds: a transition, an equation,
//!   a simplification, a claim's start and a context; a static clause applies unconditionally
//!   when a term is read, and an initializer, a constant and a context alias apply to nothing;
//! - `#[k::ensures(c)]` and `#[k::exists(n: S)]` state what a step's result satisfies and which
//!   of its values are existential: a transition's and a claim's, which reach a result state;
//! - `#[k::fresh(l: S)]` draws a value in a transition step;
//! - an `anywhere` rule replaces an application in place by the term its result writes, as an
//!   equation gives an application its value: no value of its result is existential or drawn
//!   fresh ([`TOGETHER`], [`together`]);
//! - `unbound_variables = [..]` names the names a desugar clause's result leaves to the sentence
//!   it is expanded in, which only a desugar clause is;
//! - `recursive` is a property of a static production (on its own marker, [`Extra`]), not of a
//!   sentence;
//! - the retired `#[k::priority(N)]` is no attribute any more;
//! - a Rust attribute on a clause means on it what it means on an item: `#[doc]` documents it,
//!   and `#[cfg(..)]` keeps it in the definition where the configuration holds, as on a rule fn.
//!
//! An initializer's, a constant's and a function shorthand's attribute declares (the initial
//! configuration, a value, a function's production): a sentence's key there is the key of no
//! sentence. `smt_lemma` means something on an equation and a simplification, but only of a
//! function the solver has a symbol for, which the terms base's `Probe` is not.
//!
//! **Classes.** A refused attribute's class names the mistake, whatever the form it is made on:
//! an order on a sentence that is chosen against none (`owise` on a simplification apart, which
//! states what a prover cannot decide), `nondet` on a function, a restriction outside a
//! function, `anywhere` outside a term-shaped transition or on a `for Sort` clause, `result`
//! without heating, `recursive` on a sentence, `unbound_variables` elsewhere than on a desugar
//! clause, a condition on a static clause, an existential or a postcondition on a sentence that
//! reaches no result, a fresh value outside a transition, an existential or a fresh value on an
//! `anywhere` rule. Any other key, and every sentence key on a declaration's marker (an
//! initializer's, a constant's, a function shorthand's, which declare and order nothing), is a
//! key the marker does not take (`unknown-key`); and a helper the form's own grammar takes none
//! of is that form's mistake (an initializer's, a constant's, a function shorthand's, a table
//! row's, a context alias's).

use super::oracle::{Class, Outcome, Refusal, Stage};

/// The priority of the terms base's driver rules (`class_matrix::terms`), which set a run's cells
/// up and apply the equation forms' functions: ahead of every case's sentence.
pub const DRIVER_PRIORITY: u32 = 10;

/// The priority a case's `priority` key writes ([`Attribute::Priority`]): after the driver rules'
/// and before the default, 50.
pub const CASE_PRIORITY: u32 = 20;

/// The priority of the sibling a `priority` case is written beside: after the case's, before the
/// default, so a sentence that dropped the case's key would lose to it.
pub const PRIORITY_SIBLING_PRIORITY: u32 = 30;

/// The priority a late `priority` case writes ([`Attribute::PriorityLate`]): after its sibling's
/// and before the default, so the sibling wins where both match. With [`CASE_PRIORITY`], before
/// the sibling's, the two cases have opposite winners, and a key dropped (both sentences at one
/// priority) shows in one of them whichever way the tie breaks.
pub const LATE_CASE_PRIORITY: u32 = 40;

/// The priority of the sibling an `owise` case is written beside: before `owise` (200) and after
/// the default, so a sentence that dropped `owise` would win over it.
pub const OWISE_SIBLING_PRIORITY: u32 = 60;

/// What kind of sentence a form writes, for what an attribute means on it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Sentence {
    /// A transition: a step of the configuration, chosen among the transitions that match.
    Transition {
        /// Whether its subject is a term (`#[k::rule]` fn, `for Sort` clause), not cells.
        term_shaped: bool,
        /// Whether its block's `for Sort` header anchors it at the head of the computation cell.
        anchored: bool,
    },
    /// An equation of a function, chosen among the function's equations.
    Equation {
        /// Whether it is a row of a `k::equations!` table.
        row: bool,
    },
    /// The one equation a function shorthand's body states, under its function's declaration.
    Shorthand,
    /// A simplification, which a prover may use where it applies.
    Simplification,
    /// A claim, which is proved.
    Claim,
    /// A context: where evaluation may happen, a heating and a cooling step.
    Context,
    /// A context alias: the configuration around a strict argument, which contexts instantiate.
    ContextAlias,
    /// A static clause, which rewrites its production's applications as a term is read.
    Static {
        /// Whether it is a desugar clause (rather than an alias clause).
        desugar: bool,
    },
    /// An initializer, which declares the initial configuration.
    Initializer,
    /// A constant, which declares a value.
    Constant,
}

/// One sentence form of the attribute axis: the term family's slot form, the slot whose
/// template its cases are written on, the spelling at that slot's hole, and what kind of
/// sentence it writes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Form {
    /// The term family's slot form (`rule`, `readable`, ..), the case ID's second segment.
    pub name: &'static str,
    /// The slot of the form whose template the cases are written on.
    pub position: &'static str,
    /// The spelling at the slot's hole: `_`, or `x` where a condition reads a bound `x`, or `1`
    /// where `_` cannot stand.
    pub hole: &'static str,
    /// What kind of sentence the form writes.
    pub sentence: Sentence,
    /// The path of the form's marker, `#[k::PATH]`: the sentence's, or a declaration's (a
    /// function shorthand's `function`); a clause's or a row's, which the case writes where it
    /// writes a key (`#[k::rule(..)]`, a row's `#[k::equation(..)]`).
    pub marker: &'static str,
}

const fn form(
    name: &'static str,
    position: &'static str,
    hole: &'static str,
    sentence: Sentence,
    marker: &'static str,
) -> Form {
    Form {
        name,
        position,
        hole,
        sentence,
        marker,
    }
}

const TERM_RULE: Sentence = Sentence::Transition {
    term_shaped: true,
    anchored: false,
};
const HEAD_RULE: Sentence = Sentence::Transition {
    term_shaped: true,
    anchored: true,
};
const CELLS_RULE: Sentence = Sentence::Transition {
    term_shaped: false,
    anchored: false,
};

/// Every form of the attribute axis, one per slot form of the term family.
pub const FORMS: [Form; 18] = [
    form("rule", "subject", "_", TERM_RULE, "rule"),
    form("local-rule", "subject", "_", TERM_RULE, "rule"),
    form("sort-rule", "subject", "_", HEAD_RULE, "rule"),
    form("readable", "subject", "_", CELLS_RULE, "rule"),
    form("cells", "subject", "_", CELLS_RULE, "rule"),
    form("cells-local", "subject", "_", CELLS_RULE, "rule"),
    form("claim", "subject", "_", Sentence::Claim, "claim"),
    form("cells-claim", "subject", "_", Sentence::Claim, "claim"),
    form(
        "equation",
        "subject",
        "x",
        Sentence::Equation { row: false },
        "equation",
    ),
    form(
        "table",
        "subject",
        "x",
        Sentence::Equation { row: true },
        "equation",
    ),
    form("shorthand", "result", "x", Sentence::Shorthand, "function"),
    form(
        "simplification",
        "subject",
        "x",
        Sentence::Simplification,
        "simplification",
    ),
    form("context", "subject", "_", Sentence::Context, "context"),
    form(
        "context-alias",
        "subject",
        "_",
        Sentence::ContextAlias,
        "context_alias",
    ),
    form(
        "desugar",
        "subject",
        "_",
        Sentence::Static { desugar: true },
        "desugar",
    ),
    form(
        "alias",
        "subject",
        "1",
        Sentence::Static { desugar: false },
        "alias",
    ),
    form("init", "item", "1", Sentence::Initializer, "init"),
    form("constant", "value", "1", Sentence::Constant, "constant"),
];

/// Where an attribute is written.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Written {
    /// A key of the form's own marker, after the keys the form's base writes.
    Key(&'static str),
    /// A claim's modality, in place of the base's `all_paths`.
    Modality(&'static str),
    /// A helper attribute, after the marker (before a readable clause or a table row).
    Helper(&'static str),
    /// A helper attribute before the form's marker.
    HelperBefore(&'static str),
    /// A key of the marker of the production the form's clause is of (the case's command).
    Production(&'static str),
    /// A key of the form's marker, on a sentence of a function the solver has a symbol for: the
    /// case declares the function, with `smtlib`, and states its sentence about it.
    SolverFunction(&'static str),
    /// The form's whole marker with its keys, and the helpers after it, in place of the base's
    /// marker.
    Marker(&'static str),
    /// The strictness marker of a production the case declares (`#[k::strict(..)]`), or the
    /// marker of its constructors where it names the production's result sort
    /// (`#[k::constructors(.., result = S)]`), written beside the form's sentence or alone.
    Strictness(&'static str),
}

impl Written {
    /// What is written, `TAG` unexpanded.
    #[must_use]
    pub const fn text(self) -> &'static str {
        match self {
            Self::Key(text)
            | Self::Modality(text)
            | Self::Helper(text)
            | Self::HelperBefore(text)
            | Self::Production(text)
            | Self::SolverFunction(text)
            | Self::Marker(text)
            | Self::Strictness(text) => text,
        }
    }
}

macro_rules! attributes {
    ($($(#[$doc:meta])* $variant:ident => $written:expr, [$($key:literal),*],)*) => {
        /// One attribute of the axis, with a representative well-formed value.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Attribute {
            $($(#[$doc])* $variant,)*
        }

        impl Attribute {
            /// Every attribute.
            pub const ALL: [Self; [$(stringify!($variant)),*].len()] = [$(Self::$variant),*];

            /// Where and how the attribute is written; `TAG` is the case's tag.
            #[must_use]
            pub const fn written(self) -> Written {
                match self {
                    $(Self::$variant => $written,)*
                }
            }

            /// The keys of the product's attribute parsers the attribute writes.
            #[must_use]
            pub const fn keys(self) -> &'static [&'static str] {
                match self {
                    $(Self::$variant => &[$($key),*],)*
                }
            }
        }
    };
}

attributes! {
    /// `label = ".."`: the sentence's name.
    Label => Written::Key("label = \"named-TAG\""), ["label"],
    /// `owise`: the sentence applies where no other of its kind does.
    Owise => Written::Key("owise"), ["owise"],
    /// `priority = 20`: the sentence is tried before those of a larger priority.
    Priority => Written::Key("priority = 20"), ["priority"],
    /// `priority = 40`: the sentence is tried after its sibling's 30.
    PriorityLate => Written::Key("priority = 40"), ["priority"],
    /// `anywhere`: the transition rewrites its subject wherever it occurs.
    Anywhere => Written::Key("anywhere"), ["anywhere"],
    /// `nondet = g`: the transition overlaps the others of its group, one of which is chosen.
    Nondet => Written::Key("nondet = gTAG"), ["nondet"],
    /// `skipped_operand = ".."`: the sentence's value may depend on an operand a short-circuit
    /// operator skips, as intended.
    SkippedOperand => Written::Key("skipped_operand = \"the strict meaning\""), ["skipped_operand"],
    /// `heat, hole = x`: a heating step, where its hole is no result.
    Heat => Written::Key("heat, hole = x"), ["heat", "hole"],
    /// `cool, hole = x`: a cooling step, where its hole is a result.
    Cool => Written::Key("cool, hole = x"), ["cool", "hole"],
    /// `result = KResult`: the sort a heated hole's evaluation ends in.
    EvaluationResult => Written::Key("result = KResult"), ["result"],
    /// `heat, hole = x, result = Word`: a heating step, where its hole is no `Word`.
    HeatResult => Written::Key("heat, hole = x, result = Word"), ["heat", "hole", "result"],
    /// `concrete`: the equation applies to concrete values only.
    Concrete => Written::Key("concrete"), ["concrete"],
    /// `concrete(x)`: the equation applies where `x` is concrete.
    ConcreteBinders => Written::Key("concrete(x)"), ["concrete"],
    /// `symbolic`: the equation applies to symbolic values only.
    Symbolic => Written::Key("symbolic"), ["symbolic"],
    /// `smt_lemma`: the equation is also given to the solver.
    SmtLemma => Written::Key("smt_lemma"), ["smt_lemma"],
    /// `one_path`: a claim of one path, in place of `all_paths`.
    OnePath => Written::Modality("one_path"), ["one_path", "all_paths"],
    /// `circularity`: the claim may be used in its own proof.
    Circularity => Written::Key("circularity"), ["circularity"],
    /// `trusted`: the claim is assumed, not proved.
    Trusted => Written::Key("trusted"), ["trusted"],
    /// `unbound_variables = [y]`: a desugar clause's result name its pattern does not bind.
    UnboundVariables => Written::Key("unbound_variables = [y]"), ["unbound_variables"],
    /// `recursive`: a static production's own key, on a clause.
    Recursive => Written::Key("recursive"), ["recursive"],
    /// A condition that holds at `x` = 1, an `Int`.
    RequiresHolds => Written::Helper("#[k::requires(k::is!(Int, x))]"), [],
    /// A condition that does not hold at `x` = 1, which is no `Word`.
    RequiresFails => Written::Helper("#[k::requires(k::is!(Word, x))]"), [],
    /// A condition on the result state that holds at `x` = 1.
    Ensures => Written::Helper("#[k::ensures(k::is!(Int, x))]"), [],
    /// A condition on the result state that does not hold at `x` = 1.
    EnsuresFails => Written::Helper("#[k::ensures(k::is!(Word, x))]"), [],
    /// An existential value of the result.
    Exists => Written::Helper("#[k::exists(n: Int)]"), [],
    /// A fresh value of the step.
    Fresh => Written::Helper("#[k::fresh(l: Int)]"), [],
    /// The retired `#[k::priority(N)]`.
    RetiredPriority => Written::Helper("#[k::priority(20)]"), [],
}

impl Attribute {
    /// The attribute as the case ID spells it: what is written, `TAG` unexpanded.
    #[must_use]
    pub const fn text(self) -> &'static str {
        self.written().text()
    }

    /// The name the result of the sentence uses where the attribute needs a use to mean what it
    /// says: an existential's, a fresh value's, an unbound result name's.
    #[must_use]
    pub const fn used_name(self) -> Option<&'static str> {
        match self {
            Self::Exists => Some("n"),
            Self::Fresh => Some("l"),
            Self::UnboundVariables => Some("y"),
            _ => None,
        }
    }
}

/// The keys a form's base marker writes, which the axis covers through every case of the form:
/// a claim's modality and (on a `cells!` claim) its label, a context's hole, a context alias's
/// name and place.
pub const BASE_KEYS: [(&str, &[&str]); 4] = [
    ("claim", &["all_paths"]),
    ("cells-claim", &["all_paths", "label"]),
    ("context", &["hole"]),
    ("context-alias", &["name", "here"]),
];

/// The helper attribute macros (`krs_syntax::surface::AttributeMacro`) the axis writes, and the
/// sentence markers it writes keys into. Every other attribute macro declares a sort, a
/// production, a configuration or a module ([`DECLARATION_MACROS`]).
pub const SENTENCE_MACROS: [&str; 16] = [
    "rule",
    "equation",
    "simplification",
    "claim",
    "alias",
    "desugar",
    "context",
    "context_alias",
    "init",
    "constant",
    "function",
    "requires",
    "ensures",
    "exists",
    "fresh",
    "priority",
];

/// The attribute macros that declare (a sort, a production, a configuration, a module or an end): their
/// keys are out of the axis, and their headers are K5's.
pub const DECLARATION_MACROS: [&str; 14] = [
    "sort",
    "symbol",
    "constructor",
    "constructors",
    "token",
    "bracket",
    "subsort",
    "strict",
    "seqstrict",
    "configuration",
    "cell",
    "syntax_list",
    "spec_module",
    "end",
];

/// A malformed attribute, or keys that cannot stand together, on a form that takes the key, and
/// the mistake.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Malformed {
    /// The form.
    pub form: &'static str,
    /// What is written.
    pub written: Written,
    /// The mistake.
    pub class: Class,
}

const fn malformed(form: &'static str, written: Written, class: Class) -> Malformed {
    Malformed {
        form,
        written,
        class,
    }
}

/// The malformed values (a value of the wrong shape or out of range, a key written twice, a key
/// the marker does not have, a missing key) and the pairs of keys that cannot stand together.
pub const MALFORMED: [Malformed; 26] = [
    malformed(
        "rule",
        Written::Key("priority = \"20\""),
        Class::KeyValueShape,
    ),
    malformed("rule", Written::Key("priority = 300"), Class::PriorityRange),
    malformed(
        "rule",
        Written::Key("priority = 20, priority = 30"),
        Class::DuplicateKey,
    ),
    malformed("rule", Written::Key("owise, owise"), Class::DuplicateKey),
    malformed("rule", Written::Key("label = 1"), Class::KeyValueShape),
    malformed("rule", Written::Key("nondet = 1"), Class::KeyValueShape),
    malformed("rule", Written::Key("bogus"), Class::UnknownKey),
    malformed(
        "rule",
        Written::Key("owise, priority = 20"),
        Class::KeysTogether,
    ),
    malformed(
        "rule",
        Written::Key("heat, cool, hole = x"),
        Class::KeysTogether,
    ),
    malformed(
        "rule",
        Written::Key("anywhere, priority = 20"),
        Class::KeysTogether,
    ),
    malformed(
        "rule",
        Written::Key("heat, hole = x, owise"),
        Class::KeysTogether,
    ),
    malformed("rule", Written::Key("heat"), Class::MissingKey),
    malformed("rule", Written::Key("hole = x"), Class::MissingKey),
    malformed("equation", Written::Key("bogus"), Class::UnknownKey),
    malformed(
        "equation",
        Written::Key("owise, priority = 20"),
        Class::KeysTogether,
    ),
    malformed(
        "equation",
        Written::Key("concrete, concrete"),
        Class::DuplicateKey,
    ),
    malformed(
        "equation",
        Written::Key("concrete = x"),
        Class::RestrictionShape,
    ),
    malformed(
        "equation",
        Written::Key("concrete()"),
        Class::RestrictionShape,
    ),
    malformed(
        "equation",
        Written::Key("concrete(z)"),
        Class::RestrictionBinder,
    ),
    malformed("simplification", Written::Key("bogus"), Class::UnknownKey),
    malformed("cells-claim", Written::Key("bogus"), Class::UnknownKey),
    malformed(
        "cells-claim",
        Written::Modality("one_path, circularity"),
        Class::KeysTogether,
    ),
    malformed(
        "cells-claim",
        Written::Key("trusted, circularity"),
        Class::KeysTogether,
    ),
    malformed(
        "cells-claim",
        Written::Key("trusted = true"),
        Class::KeyValueShape,
    ),
    malformed("context", Written::Key("bogus"), Class::UnknownKey),
    malformed(
        "desugar",
        Written::Key("unbound_variables = []"),
        Class::UnboundVariablesShape,
    ),
];

/// What K7 shows of an accepted [`Extra`]: the form's sentence applies as the slot's plan states,
/// or does not apply to the program it would.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Effect {
    /// The sentence applies as without the attribute.
    Applies,
    /// The sentence does not apply: a condition fails, or the sentence is configured out.
    Unapplied,
    /// The sentence applies, and its instance at what it wrote is `t = t`: what it wrote is the
    /// value (an `anywhere` rule whose result its own subject matches, with nothing more to
    /// write there).
    Fixed,
}

/// An attribute case beyond the axis's product: a placement or a combination of attributes, on
/// the forms where it says something, each accepted. Its ID's construct is its `name`, and its
/// spelling what is written.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Extra {
    /// The form.
    pub form: &'static str,
    /// The case ID's construct.
    pub name: &'static str,
    /// What is written, and where.
    pub written: Written,
    /// What K7 shows.
    pub effect: Effect,
}

const fn extra(form: &'static str, name: &'static str, written: Written, effect: Effect) -> Extra {
    Extra {
        form,
        name,
        written,
        effect,
    }
}

/// Two conditions on one sentence, which applies where both hold: here one that holds at `x` = 1
/// and one that does not.
const REQUIRES_TWICE: &str = "#[k::requires(k::is!(Int, x))]\n#[k::requires(k::is!(Word, x))]";

/// The extra cases:
/// - `recursive` on a static production's own marker, its clauses' plain;
/// - `smt_lemma` on an equation, a table row and a simplification of a function the solver has a
///   symbol for (`smtlib`), which a lemma can be stated about;
/// - a helper before the sentence's marker, which belongs to the sentence as after it: a
///   condition and a postcondition that fail, so the run shows them kept;
/// - two conditions on one sentence, which applies where both hold;
/// - `#[doc]` and `#[cfg(..)]` on a clause: documentation, and a configuration that holds
///   (`all()`) or does not (`any()`), which keeps the clause out of the definition;
/// - `anywhere` on a single-body rule whose subject's right image its left image matches again
///   (the slot's `x => Cmd::Go()`): the rule is an equation, applied wherever its subject occurs,
///   and its instance at what it wrote is `t = t`, which states nothing more of that term, so
///   what it wrote is the value, built before any step.
pub const EXTRAS: [Extra; 21] = [
    extra(
        "desugar",
        "recursive production",
        Written::Production("recursive"),
        Effect::Applies,
    ),
    extra(
        "alias",
        "recursive production",
        Written::Production("recursive"),
        Effect::Applies,
    ),
    extra(
        "equation",
        "smt_lemma of an smtlib function",
        Written::SolverFunction("smt_lemma"),
        Effect::Applies,
    ),
    extra(
        "table",
        "smt_lemma of an smtlib function",
        Written::SolverFunction("smt_lemma"),
        Effect::Applies,
    ),
    extra(
        "simplification",
        "smt_lemma of an smtlib function",
        Written::SolverFunction("smt_lemma"),
        Effect::Applies,
    ),
    extra(
        "rule",
        "requires before the marker",
        Written::HelperBefore("#[k::requires(k::is!(Word, x))]"),
        Effect::Unapplied,
    ),
    extra(
        "equation",
        "requires before the marker",
        Written::HelperBefore("#[k::requires(k::is!(Word, x))]"),
        Effect::Unapplied,
    ),
    extra(
        "rule",
        "ensures before the marker",
        Written::HelperBefore("#[k::ensures(k::is!(Word, x))]"),
        Effect::Unapplied,
    ),
    extra(
        "rule",
        "requires twice",
        Written::Helper(REQUIRES_TWICE),
        Effect::Unapplied,
    ),
    extra(
        "equation",
        "requires twice",
        Written::Helper(REQUIRES_TWICE),
        Effect::Unapplied,
    ),
    extra(
        "readable",
        "requires twice",
        Written::Helper(REQUIRES_TWICE),
        Effect::Unapplied,
    ),
    extra(
        "sort-rule",
        "doc",
        Written::Helper("#[doc = \"a clause\"]"),
        Effect::Applies,
    ),
    extra(
        "readable",
        "doc",
        Written::Helper("#[doc = \"a clause\"]"),
        Effect::Applies,
    ),
    extra(
        "table",
        "doc",
        Written::Helper("#[doc = \"a clause\"]"),
        Effect::Applies,
    ),
    extra(
        "sort-rule",
        "cfg that holds",
        Written::Helper("#[cfg(all())]"),
        Effect::Applies,
    ),
    extra(
        "readable",
        "cfg that holds",
        Written::Helper("#[cfg(all())]"),
        Effect::Applies,
    ),
    extra(
        "table",
        "cfg that holds",
        Written::Helper("#[cfg(all())]"),
        Effect::Applies,
    ),
    extra(
        "sort-rule",
        "cfg that does not hold",
        Written::Helper("#[cfg(any())]"),
        Effect::Unapplied,
    ),
    extra(
        "readable",
        "cfg that does not hold",
        Written::Helper("#[cfg(any())]"),
        Effect::Unapplied,
    ),
    extra(
        "table",
        "cfg that does not hold",
        Written::Helper("#[cfg(any())]"),
        Effect::Unapplied,
    ),
    extra(
        "local-rule",
        "anywhere on what it writes",
        Written::Key("anywhere"),
        Effect::Fixed,
    ),
];

/// A key of a sentence's marker and a helper beside it, on a form that takes each alone, whose
/// meanings may not combine ([`together`]). Its ID's construct is its `name`, and its spelling
/// the marker and the helper as written.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Together {
    /// The form.
    pub form: &'static str,
    /// The case ID's construct.
    pub name: &'static str,
    /// The marker's key.
    pub key: Attribute,
    /// The helper.
    pub helper: Attribute,
    /// The marker with the key and the helper after it, as written.
    pub written: &'static str,
}

const fn together_case(
    form: &'static str,
    name: &'static str,
    key: Attribute,
    helper: Attribute,
    written: &'static str,
) -> Together {
    Together {
        form,
        name,
        key,
        helper,
        written,
    }
}

/// The pairs: `anywhere` with an existential and with a fresh value, on a `#[k::rule]` fn whose
/// result is written apart and on a single-body one.
pub const TOGETHER: [Together; 4] = [
    together_case(
        "rule",
        "anywhere with exists",
        Attribute::Anywhere,
        Attribute::Exists,
        "#[k::rule(anywhere)]\n#[k::exists(n: Int)]",
    ),
    together_case(
        "local-rule",
        "anywhere with exists",
        Attribute::Anywhere,
        Attribute::Exists,
        "#[k::rule(anywhere)]\n#[k::exists(n: Int)]",
    ),
    together_case(
        "rule",
        "anywhere with fresh",
        Attribute::Anywhere,
        Attribute::Fresh,
        "#[k::rule(anywhere)]\n#[k::fresh(l: Int)]",
    ),
    together_case(
        "local-rule",
        "anywhere with fresh",
        Attribute::Anywhere,
        Attribute::Fresh,
        "#[k::rule(anywhere)]\n#[k::fresh(l: Int)]",
    ),
];

/// What a key and a helper mean together on a sentence of the kind `sentence`: each one's
/// refusal where the sentence takes it not alone; otherwise accepted, but where their meanings
/// contradict. An `anywhere` rule replaces an application, wherever it occurs, by the one term
/// its result writes, in place, as an equation gives an application its value: it reaches no
/// result state of a step, so no value of its result can be existential (some value, which the
/// replacement would not determine), and none is drawn fresh by a step. A postcondition beside
/// it still reads the term it writes, so `ensures` stands.
#[must_use]
pub fn together(sentence: Sentence, key: Attribute, helper: Attribute) -> Outcome {
    use Attribute as A;
    for attribute in [key, helper] {
        let alone = expected(sentence, attribute);
        if alone != Outcome::Accept {
            return alone;
        }
    }
    match (key, helper) {
        (A::Anywhere, A::Exists) => refuse(Class::ExistentialOutsideStep),
        (A::Anywhere, A::Fresh) => refuse(Class::FreshOutsideStep),
        _ => Outcome::Accept,
    }
}

/// The lint a step whose hole can never be a result owes (the module documentation).
pub const NEVER_COOLS: &str = "never-cools";

/// The sorts of the terms base (`class_matrix::terms`) declared below others: `Int` below
/// `Value`, which is below `Stmt` and `KResult`. Every sort is below `KItem`.
const SUBSORTS: [(&str, &str); 3] = [("Int", "Value"), ("Value", "Stmt"), ("Value", "KResult")];

/// The sorts of the terms base that have terms of their own: the integers, the `Word` tokens,
/// the commands (`Cmd`) and the cons list (`Seq`). `Value` has only the terms of `Int`, below it,
/// and the framework's `KItem` and `KResult` only those of the sorts below them.
const INHABITED: [&str; 4] = ["Int", "Word", "Stmt", "Items"];

/// Whether a term of `sort` is a term of `expected` in the terms base.
fn below(sort: &str, expected: &str) -> bool {
    sort == expected
        || expected == "KItem"
        || SUBSORTS
            .iter()
            .any(|(lower, upper)| *lower == sort && below(upper, expected))
}

/// Whether a step whose hole has sort `hole` and whose result sort is `result` may cool, in the
/// terms base: some sort that has terms is below both.
#[must_use]
pub fn cools(hole: &str, result: &str) -> bool {
    INHABITED
        .iter()
        .any(|sort| below(sort, hole) && below(sort, result))
}

/// What evaluates a [`Cooling`] case's hole.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Step {
    /// The context form's context, `#[k::context(hole = h, ..)]`, over the case's command, whose
    /// fields have the hole's sort.
    Context,
    /// The one position of a production the case declares strict, `#[k::strict(..)]`.
    Strict,
    /// The one position of a production the case declares strict through the context alias the
    /// form's sentence is (`#[k::strict(using = case_TAG)]`).
    StrictUsing,
}

/// A step whose hole may or may not be a result: a context, or a position of a strict
/// production, with the hole's sort and the step's result sort. Its ID's construct is its
/// `name`, and its spelling the marker as written.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Cooling {
    /// The form: `context` for a context or a strict position, `context-alias` for a strict
    /// position evaluated through the case's alias.
    pub form: &'static str,
    /// The case ID's construct.
    pub name: &'static str,
    /// What evaluates the hole.
    pub step: Step,
    /// The hole's sort.
    pub hole: &'static str,
    /// The `result = S` the step names (on the context, the strictness, or the alias), `None`
    /// where it names none: the step's result sort is then `KResult` (a context's default, and
    /// the production's `#[k::constructors(.., result = KResult)]`).
    pub result: Option<&'static str>,
    /// The marker as written: the context's, the production's strictness, or its constructors'
    /// where they name its result sort.
    pub written: &'static str,
}

impl Cooling {
    /// The step's result sort.
    #[must_use]
    pub fn result_sort(self) -> &'static str {
        self.result.unwrap_or("KResult")
    }
}

const fn cooling(
    form: &'static str,
    name: &'static str,
    step: Step,
    hole: &'static str,
    result: Option<&'static str>,
    written: &'static str,
) -> Cooling {
    Cooling {
        form,
        name,
        step,
        hole,
        result,
        written,
    }
}

/// The cooling cases of contexts, each warned one beside a control that differs in one sort: a
/// context whose hole is a `Word` (no `Word` is below `KResult`) and one whose `result = Word`; a
/// context whose hole is an `Int` (below `KResult`) and one whose `result = Word`, which no `Int`
/// is. The strict positions' are [`STRICT_COOLINGS`]; [`pairs`] generates both.
pub const COOLINGS: [Cooling; 4] = [
    cooling(
        "context",
        "hole of sort Word",
        Step::Context,
        "Word",
        None,
        "#[k::context(hole = h)]",
    ),
    cooling(
        "context",
        "hole of sort Word with result = Word",
        Step::Context,
        "Word",
        Some("Word"),
        "#[k::context(hole = h, result = Word)]",
    ),
    cooling(
        "context",
        "hole of sort Int",
        Step::Context,
        "Int",
        None,
        "#[k::context(hole = h)]",
    ),
    cooling(
        "context",
        "hole of sort Int with result = Word",
        Step::Context,
        "Int",
        Some("Word"),
        "#[k::context(hole = h, result = Word)]",
    ),
];

/// The cooling cases of strict positions, each warned one beside its control: a position of
/// sort `Word` and one of sort `Int` with the production's `result = KResult`, each beside the
/// same position with `result = Word` (on the production's constructors), and a `Word` position
/// evaluated through the form's context alias, whose `result = Value` no `Word` is and whose
/// `result = Word` every `Word` is. Each case declares its production in a constructors family
/// of its own, which K3 places as the case's item (krs-cli `class_matrix/pipeline.rs` `locate`).
pub const STRICT_COOLINGS: [Cooling; 6] = [
    cooling(
        "context",
        "strict position of sort Word",
        Step::Strict,
        "Word",
        None,
        "#[k::strict]",
    ),
    cooling(
        "context",
        "strict position of sort Word with result = Word",
        Step::Strict,
        "Word",
        Some("Word"),
        "#[k::constructors(sort = Stmt, result = Word)]",
    ),
    cooling(
        "context",
        "strict position of sort Int",
        Step::Strict,
        "Int",
        None,
        "#[k::strict]",
    ),
    cooling(
        "context",
        "strict position of sort Int with result = Word",
        Step::Strict,
        "Int",
        Some("Word"),
        "#[k::constructors(sort = Stmt, result = Word)]",
    ),
    cooling(
        "context-alias",
        "strict position of sort Word using an alias with result = Value",
        Step::StrictUsing,
        "Word",
        Some("Value"),
        "#[k::strict(using = case_TAG)]",
    ),
    cooling(
        "context-alias",
        "strict position of sort Word using an alias with result = Word",
        Step::StrictUsing,
        "Word",
        Some("Word"),
        "#[k::strict(using = case_TAG)]",
    ),
];

/// What an attribute case writes: an attribute of the axis, a malformed one, or an extra.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Pair {
    /// An attribute on a form.
    Attribute(Form, Attribute),
    /// A malformed attribute on a form.
    Malformed(Form, Malformed),
    /// An extra case on a form.
    Extra(Form, Extra),
    /// A key and a helper together on a form.
    Together(Form, Together),
    /// A step whose hole may or may not be a result, on a form.
    Cooling(Form, Cooling),
}

impl Pair {
    /// The form.
    #[must_use]
    pub const fn form(self) -> Form {
        match self {
            Self::Attribute(form, _)
            | Self::Malformed(form, _)
            | Self::Extra(form, _)
            | Self::Together(form, _)
            | Self::Cooling(form, _) => form,
        }
    }

    /// What is written.
    #[must_use]
    pub const fn written(self) -> Written {
        match self {
            Self::Attribute(_, attribute) => attribute.written(),
            Self::Malformed(_, malformed) => malformed.written,
            Self::Extra(_, extra) => extra.written,
            Self::Together(_, together) => Written::Marker(together.written),
            Self::Cooling(_, cooling) => match cooling.step {
                Step::Context => Written::Marker(cooling.written),
                Step::Strict | Step::StrictUsing => Written::Strictness(cooling.written),
            },
        }
    }

    /// The case ID's construct: what is written, or an extra's name.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Extra(_, extra) => extra.name,
            Self::Together(_, together) => together.name,
            Self::Cooling(_, cooling) => cooling.name,
            _ => self.written().text(),
        }
    }

    /// The oracle's outcome.
    #[must_use]
    pub fn expected(self) -> Outcome {
        match self {
            Self::Attribute(form, attribute) => expected(form.sentence, attribute),
            Self::Malformed(_, malformed) => refuse(malformed.class),
            Self::Extra(..) | Self::Cooling(..) => Outcome::Accept,
            Self::Together(form, pair) => together(form.sentence, pair.key, pair.helper),
        }
    }

    /// The hole's sort and the result sort of the step an accepted case writes, where it writes
    /// one: a cooling case's, and the context form's, whose hole `h` is its command's first
    /// field, a `KItem`, and whose result sort is `KResult`, named (`result = KResult`) or not.
    /// A context alias alone evaluates nothing: only a production strict in it does.
    #[must_use]
    pub fn step(self) -> Option<(&'static str, &'static str)> {
        if self.expected() != Outcome::Accept {
            return None;
        }
        match self {
            Self::Cooling(_, cooling) => Some((cooling.hole, cooling.result_sort())),
            _ if self.form().sentence == Sentence::Context => Some(("KItem", "KResult")),
            _ => None,
        }
    }

    /// The lint the oracle owes the case: [`NEVER_COOLS`] where its step can never cool
    /// ([`cools`]), none elsewhere.
    #[must_use]
    pub fn lint(self) -> Option<&'static str> {
        self.step()
            .filter(|(hole, result)| !cools(hole, result))
            .map(|_| NEVER_COOLS)
    }
}

/// The form named `name`.
///
/// # Panics
///
/// Panics if no form is named `name`.
#[must_use]
pub fn form_named(name: &str) -> Form {
    *FORMS
        .iter()
        .find(|form| form.name == name)
        .unwrap_or_else(|| panic!("no attribute form is named {name}"))
}

/// Every pair of the axis: every attribute on every form, then the malformed ones, the extras,
/// the attributes together and the cooling cases.
#[must_use]
pub fn pairs() -> Vec<Pair> {
    let mut pairs = FORMS
        .iter()
        .flat_map(|form| {
            Attribute::ALL
                .iter()
                .map(move |attribute| Pair::Attribute(*form, *attribute))
        })
        .collect::<Vec<_>>();
    pairs.extend(
        MALFORMED
            .iter()
            .map(|malformed| Pair::Malformed(form_named(malformed.form), *malformed)),
    );
    pairs.extend(
        EXTRAS
            .iter()
            .map(|extra| Pair::Extra(form_named(extra.form), *extra)),
    );
    pairs.extend(
        TOGETHER
            .iter()
            .map(|together| Pair::Together(form_named(together.form), *together)),
    );
    pairs.extend(
        COOLINGS
            .iter()
            .chain(STRICT_COOLINGS.iter())
            .map(|cooling| Pair::Cooling(form_named(cooling.form), *cooling)),
    );
    pairs
}

const fn refuse(class: Class) -> Outcome {
    Outcome::Refuse(Refusal {
        class,
        stage: Stage::Placement,
        outer: false,
    })
}

/// Whether `attribute` means something on a sentence of the kind `sentence`
/// ([module docs](self)).
#[must_use]
pub const fn means(sentence: Sentence, attribute: Attribute) -> bool {
    use Attribute as A;
    use Sentence as S;
    let transition = matches!(sentence, S::Transition { .. });
    let function = matches!(sentence, S::Equation { .. } | S::Simplification);
    match attribute {
        A::Label => !matches!(
            sentence,
            S::ContextAlias | S::Static { .. } | S::Initializer | S::Constant
        ),
        A::Owise => transition || matches!(sentence, S::Equation { .. }),
        A::Priority | A::PriorityLate => transition || function,
        A::Nondet | A::Heat | A::Cool | A::HeatResult | A::Fresh => transition,
        A::SkippedOperand => transition || matches!(sentence, S::Equation { .. } | S::Shorthand),
        A::Anywhere => matches!(
            sentence,
            S::Transition {
                term_shaped: true,
                anchored: false
            }
        ),
        A::EvaluationResult => matches!(sentence, S::Context | S::ContextAlias),
        A::Concrete | A::ConcreteBinders | A::Symbolic | A::SmtLemma => function,
        A::OnePath | A::Circularity | A::Trusted => matches!(sentence, S::Claim),
        A::UnboundVariables => matches!(sentence, S::Static { desugar: true }),
        A::Recursive | A::RetiredPriority => false,
        A::RequiresHolds | A::RequiresFails => {
            transition || function || matches!(sentence, S::Shorthand | S::Claim | S::Context)
        }
        A::Ensures | A::EnsuresFails | A::Exists => transition || matches!(sentence, S::Claim),
    }
}

/// What `attribute` means on a sentence of the kind `sentence`: accepted, or the class of its
/// mistake ([module docs](self)).
#[must_use]
pub fn expected(sentence: Sentence, attribute: Attribute) -> Outcome {
    use Attribute as A;
    if means(sentence, attribute) {
        // The terms base's `Probe` has no solver symbol, so no lemma about it can be stated.
        return if attribute == A::SmtLemma {
            refuse(Class::SmtLemmaUntranslatable)
        } else {
            Outcome::Accept
        };
    }
    let class = if matches!(attribute.written(), Written::Helper(_)) {
        helper_class(sentence, attribute)
    } else {
        key_class(sentence, attribute)
    };
    refuse(class)
}

/// The mistake of a helper that means nothing on a sentence of the kind `sentence`: where the
/// form's grammar takes no helper, that form's; otherwise the helper's.
fn helper_class(sentence: Sentence, attribute: Attribute) -> Class {
    use Attribute as A;
    use Sentence as S;
    match sentence {
        S::Initializer => Class::HelperOnInitializer,
        S::Shorthand => Class::HelperOnShorthand,
        S::Equation { row: true } => Class::HelperOnTableRow,
        _ if attribute == A::RetiredPriority => Class::RetiredAttribute,
        S::Constant => Class::HelperOnConstant,
        _ if attribute == A::Fresh => Class::FreshOutsideStep,
        S::ContextAlias => Class::HelperOnContextAlias,
        S::Static { .. } if matches!(attribute, A::RequiresHolds | A::RequiresFails) => {
            Class::ConditionOnStaticClause
        }
        _ => Class::ExistentialOutsideStep,
    }
}

/// The mistake of a key that means nothing on a sentence of the kind `sentence`: the key's,
/// whatever the form; any key on a declaration's marker is one it does not take.
fn key_class(sentence: Sentence, attribute: Attribute) -> Class {
    use Attribute as A;
    use Sentence as S;
    let function = matches!(sentence, S::Equation { .. } | S::Simplification);
    if matches!(sentence, S::Initializer | S::Constant | S::Shorthand) {
        return Class::UnknownKey;
    }
    match attribute {
        A::Owise if sentence == S::Simplification => Class::OwiseOnSimplification,
        A::Nondet if function => Class::NondetOnFunction,
        A::Owise | A::Priority | A::PriorityLate | A::Nondet => Class::OrderOnUnorderedSentence,
        A::Anywhere => Class::AnywhereOutsideTermRule,
        A::Concrete | A::ConcreteBinders | A::Symbolic | A::SmtLemma => {
            Class::RestrictionOutsideFunction
        }
        A::EvaluationResult => Class::EvaluationKeyWithoutEvaluation,
        A::Recursive => Class::RecursiveOutsideProduction,
        A::UnboundVariables => Class::UnboundVariablesOutsideDesugar,
        _ => Class::UnknownKey,
    }
}
