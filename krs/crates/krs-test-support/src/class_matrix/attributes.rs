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
//!   evaluation happens and are ordered by their hole, and a static clause rewrites every
//!   application of its production once, as the definition and a program are read: none of them
//!   is chosen against another;
//! - `anywhere` makes a transition rewrite its subject's root application wherever it occurs, which
//!   a term-shaped transition has; a configuration-shaped one matches cells, which occur only at
//!   their place, and a function's equations apply wherever its application occurs already;
//! - `heat`/`cool` (with `hole = x`) make a transition a heating or cooling step, which K orders
//!   by whether its hole is a result; `result = S` names the sort a heated hole's evaluation ends
//!   in, which a context and a context alias name too, and which means nothing on a sentence
//!   that heats nothing;
//! - `concrete`, `symbolic` and `smt_lemma` restrict when an equation or a simplification applies
//!   (or hand it to the solver): on a transition a restriction would leave out of a symbolic
//!   search the steps it applies to, which is unsound, and on the other forms there is no
//!   function application to restrict;
//! - `one_path`, `circularity` and `trusted` say how a claim is proved;
//! - a label names a sentence for what refers to its steps (a run's, a proof's, a trace's), as
//!   a clause's or a fn's name does by default: a context alias is named by its `name`, which
//!   the strict productions that use it refer to, a static clause takes no step, and an
//!   initializer, a constant and a function shorthand's declaration are no sentence of the
//!   author's to name;
//! - `#[k::requires(c)]` makes a sentence apply only where `c` holds: a transition, an equation,
//!   a simplification, a claim's start and a context; a static clause applies unconditionally
//!   when a term is read, and an initializer, a constant and a context alias apply to nothing;
//! - `#[k::ensures(c)]` and `#[k::exists(n: S)]` state what a step's result satisfies and which
//!   of its values are existential: a transition's and a claim's, which reach a result state;
//! - `#[k::fresh(l: S)]` draws a value in a transition step;
//! - `unbound_variables = [..]` names the names a desugar clause's result leaves to the sentence
//!   it is expanded in, which only a desugar clause is;
//! - `recursive` is a property of a static production, not of a clause;
//! - the retired `#[k::priority(N)]` is no attribute any more.
//!
//! An initializer's, a constant's and a function shorthand's attribute declares (the initial
//! configuration, a value, a function's production): a sentence's key there is the key of no
//! sentence. `smt_lemma` means something on an equation and a simplification, but only of a
//! function the solver has a symbol for, which the terms base's `Probe` is not.
//!
//! **Classes.** A refused attribute's class is the most specific statement of the mistake the
//! sentence kind has: an order on a static clause, `owise` on a simplification, `nondet` on a
//! function, a restriction on a transition, `anywhere` on a configuration-shaped transition,
//! `result` without heating, `recursive` on a static clause, `unbound_variables` elsewhere than
//! on a desugar clause, a condition on a static clause, an existential or a postcondition on a
//! sentence that reaches no result, a fresh value outside a transition. Otherwise a key is one
//! the sentence's marker does not take (`unknown-key`), or, on a marker that takes no key of
//! its kind (an alias clause's, a desugar clause's but for `unbound_variables`, an
//! initializer's, a constant's), a payload of that marker (`payload-on-bare-marker`); and a
//! helper the form's own grammar takes none of is that form's mistake (an initializer's, a
//! constant's, a function shorthand's, a table row's, a context alias's).

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
}

const fn form(
    name: &'static str,
    position: &'static str,
    hole: &'static str,
    sentence: Sentence,
) -> Form {
    Form {
        name,
        position,
        hole,
        sentence,
    }
}

const TERM_RULE: Sentence = Sentence::Transition { term_shaped: true };
const CELLS_RULE: Sentence = Sentence::Transition { term_shaped: false };

/// Every form of the attribute axis, one per slot form of the term family.
pub const FORMS: [Form; 18] = [
    form("rule", "subject", "_", TERM_RULE),
    form("local-rule", "subject", "_", TERM_RULE),
    form("sort-rule", "subject", "_", TERM_RULE),
    form("readable", "subject", "_", CELLS_RULE),
    form("cells", "subject", "_", CELLS_RULE),
    form("cells-local", "subject", "_", CELLS_RULE),
    form("claim", "subject", "_", Sentence::Claim),
    form("cells-claim", "subject", "_", Sentence::Claim),
    form(
        "equation",
        "subject",
        "x",
        Sentence::Equation { row: false },
    ),
    form("table", "subject", "x", Sentence::Equation { row: true }),
    form("shorthand", "result", "x", Sentence::Shorthand),
    form("simplification", "subject", "x", Sentence::Simplification),
    form("context", "subject", "_", Sentence::Context),
    form("context-alias", "subject", "_", Sentence::ContextAlias),
    form(
        "desugar",
        "subject",
        "_",
        Sentence::Static { desugar: true },
    ),
    form("alias", "subject", "1", Sentence::Static { desugar: false }),
    form("init", "item", "1", Sentence::Initializer),
    form("constant", "value", "1", Sentence::Constant),
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
    /// `anywhere`: the transition rewrites its subject wherever it occurs.
    Anywhere => Written::Key("anywhere"), ["anywhere"],
    /// `nondet = g`: the transition overlaps the others of its group, one of which is chosen.
    Nondet => Written::Key("nondet = gTAG"), ["nondet"],
    /// `heat, hole = x`: a heating step, where its hole is no result.
    Heat => Written::Key("heat, hole = x"), ["heat", "hole"],
    /// `cool, hole = x`: a cooling step, where its hole is a result.
    Cool => Written::Key("cool, hole = x"), ["cool", "hole"],
    /// `result = KResult`: the sort a heated hole's evaluation ends in.
    EvaluationResult => Written::Key("result = KResult"), ["result"],
    /// `concrete`: the equation applies to concrete values only.
    Concrete => Written::Key("concrete"), ["concrete"],
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
    /// A condition on the result state.
    Ensures => Written::Helper("#[k::ensures(k::is!(Int, x))]"), [],
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
        match self.written() {
            Written::Key(text) | Written::Modality(text) | Written::Helper(text) => text,
        }
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

/// The attribute macros that declare (a sort, a production, a configuration or a module): their
/// keys are out of the axis, and their headers are K5's.
pub const DECLARATION_MACROS: [&str; 13] = [
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

impl Malformed {
    /// What is written, as the case ID spells it.
    #[must_use]
    pub const fn text(self) -> &'static str {
        match self.written {
            Written::Key(text) | Written::Modality(text) | Written::Helper(text) => text,
        }
    }
}

/// What an attribute case writes: an attribute of the axis, or a malformed one.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Pair {
    /// An attribute on a form.
    Attribute(Form, Attribute),
    /// A malformed attribute on a form.
    Malformed(Form, Malformed),
}

impl Pair {
    /// The form.
    #[must_use]
    pub const fn form(self) -> Form {
        match self {
            Self::Attribute(form, _) | Self::Malformed(form, _) => form,
        }
    }

    /// What is written.
    #[must_use]
    pub const fn written(self) -> Written {
        match self {
            Self::Attribute(_, attribute) => attribute.written(),
            Self::Malformed(_, malformed) => malformed.written,
        }
    }

    /// The oracle's outcome.
    #[must_use]
    pub fn expected(self) -> Outcome {
        match self {
            Self::Attribute(form, attribute) => expected(form.sentence, attribute),
            Self::Malformed(_, malformed) => refuse(malformed.class),
        }
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

/// Every pair of the axis: every attribute on every form, then the malformed ones.
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
            S::ContextAlias | S::Static { .. } | S::Initializer | S::Constant | S::Shorthand
        ),
        A::Owise => transition || matches!(sentence, S::Equation { .. }),
        A::Priority => transition || function,
        A::Nondet | A::Heat | A::Cool | A::Fresh => transition,
        A::Anywhere => matches!(sentence, S::Transition { term_shaped: true }),
        A::EvaluationResult => matches!(sentence, S::Context | S::ContextAlias),
        A::Concrete | A::Symbolic | A::SmtLemma => function,
        A::OnePath | A::Circularity | A::Trusted => matches!(sentence, S::Claim),
        A::UnboundVariables => matches!(sentence, S::Static { desugar: true }),
        A::Recursive | A::RetiredPriority => false,
        A::RequiresHolds | A::RequiresFails => {
            transition || function || matches!(sentence, S::Shorthand | S::Claim | S::Context)
        }
        A::Ensures | A::Exists => transition || matches!(sentence, S::Claim),
    }
}

/// What `attribute` means on a sentence of the kind `sentence`: accepted, or the class of its
/// mistake ([module docs](self)).
#[must_use]
pub fn expected(sentence: Sentence, attribute: Attribute) -> Outcome {
    use Attribute as A;
    use Sentence as S;
    if means(sentence, attribute) {
        // The terms base's `Probe` has no solver symbol, so no lemma about it can be stated.
        return if attribute == A::SmtLemma {
            refuse(Class::SmtLemmaUntranslatable)
        } else {
            Outcome::Accept
        };
    }
    let class = match (attribute.written(), sentence) {
        // The forms whose grammar lists the attributes they take refuse it as any other.
        (Written::Helper(_), _) if attribute == A::RetiredPriority => match sentence {
            S::Initializer => Class::HelperOnInitializer,
            S::Shorthand => Class::HelperOnShorthand,
            S::Equation { row: true } => Class::HelperOnTableRow,
            _ => Class::RetiredAttribute,
        },
        (Written::Helper(_), S::Initializer) => Class::HelperOnInitializer,
        (Written::Helper(_), S::Constant) => Class::HelperOnConstant,
        (Written::Helper(_), S::Shorthand) => Class::HelperOnShorthand,
        (Written::Helper(_), S::Equation { row: true }) => Class::HelperOnTableRow,
        (Written::Helper(_), _) if attribute == A::Fresh => Class::FreshOutsideStep,
        (Written::Helper(_), S::ContextAlias) => Class::HelperOnContextAlias,
        (Written::Helper(_), S::Static { .. })
            if attribute == A::RequiresHolds || attribute == A::RequiresFails =>
        {
            Class::ConditionOnStaticClause
        }
        (Written::Helper(_), _) => Class::ExistentialOutsideStep,
        (_, S::Initializer | S::Constant) => Class::PayloadOnBareMarker,
        (_, S::Static { .. }) => match attribute {
            A::Owise | A::Priority | A::Nondet => Class::OrderOnUnorderedSentence,
            A::Recursive => Class::RecursiveOnClause,
            A::UnboundVariables => Class::UnboundVariablesOutsideDesugar,
            _ => Class::PayloadOnBareMarker,
        },
        (_, S::Shorthand) => Class::UnknownKey,
        _ if attribute == A::UnboundVariables => Class::UnboundVariablesOutsideDesugar,
        (_, S::Transition { .. }) => match attribute {
            A::Concrete | A::Symbolic | A::SmtLemma => Class::RestrictionOutsideFunction,
            A::Anywhere => Class::AnywhereOutsideTermRule,
            A::EvaluationResult => Class::EvaluationKeyWithoutEvaluation,
            _ => Class::UnknownKey,
        },
        (_, S::Equation { .. } | S::Simplification) => match attribute {
            A::Nondet => Class::NondetOnFunction,
            A::Owise => Class::OrderOnUnorderedSentence,
            _ => Class::UnknownKey,
        },
        _ => Class::UnknownKey,
    };
    refuse(class)
}
