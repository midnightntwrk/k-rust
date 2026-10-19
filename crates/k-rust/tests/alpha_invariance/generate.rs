//! The generated grammar: small definitions whose sentences hold up to three binders, each
//! along the axes of a binding relation. Every generated definition goes through the full
//! compile path and `krun`, together with each alpha-variant the strategies of `rename.rs` give.
//!
//! The axes:
//! - the binder kind: `#Exists` or `#Forall`;
//! - the bound name's relation to the other names of the sentence: fresh, the left side's
//!   variable, another binder's name, a macro parameter, a context alias's variable, a function
//!   rule's variable, a name the compiler mints (`K0`), an anonymous variable, or a name only a
//!   `concrete` or `symbolic` attribute of the rule mentions (`attribute`);
//! - the bound variable's sort: the sort of the related variable (`Int`), or another (`Bool`);
//! - the position: the `requires`, the `ensures`, an argument of a function in the condition, or
//!   the right side;
//! - the number of binders and how they are placed: one; two or three conjoined, nested, or split
//!   between `requires` and `ensures`;
//! - the sentence kind: a rewrite rule, an `anywhere` rule, a `simplification`, a function rule
//!   with an `owise` competitor, a macro rule (`macro`, `macro-rec`, `alias`), a context with
//!   `HOLE`, a context alias, or a claim (compiled `--for-proving`);
//! - a binder in a part that a stage copies into a second position of its sentence: a rule's or
//!   claim's context shared by both sides of its rewrite, the argument of a macro parameter that
//!   occurs twice, and a context's body (`copy`);
//! - the frozen variables of a context: two or more, written in a context (`f(HOLE, X, Y)`, in
//!   occurrence order or not) or a context alias's variable beside the strictness variables
//!   (`wrap(HERE, V)` with `V` spelled `S`, `K0` or `A`), with no cell or inside the main cell,
//!   so the freezer's argument order meets every renaming;
//! - the connective around the binder: none, `#Not`, `#Or`;
//! - the sigil of the bound variable: none, or `?` beside a free right-side `?` variable, in the
//!   right side, the `ensures` or a claim's `ensures`, nested and spelled alike or apart, with no
//!   free `?` variable, and in a function, an `anywhere` or a macro rule (`existential`);
//! - the route: the parsed definition renamed and relinked (every strategy), source text written
//!   beside the base with a binder annotated or left to the parser's sort inference (`source`),
//!   or a search pattern compiled against the definition, written beside the base or renamed by
//!   every strategy (`search`, with the binder shapes of `one`, `two` and `anon`);
//! - the capture target of a renamed binder: a free variable of the sentence at the same sort or
//!   any sort, or a sibling binder (a disjoint scope) at another sort;
//! - a written name holding U+E000, which a declared `#KVariable` token allows: a free variable
//!   renamed to a binder's spelling or another variable's followed by U+E000 and digits, beside a
//!   binder the parser renames apart (`mark`);
//! - a local function's parameter spelled like a variable of the rule at another sort (`lambda`),
//!   and a binder spelled like the variable of a list update (`list`).
//!
//! The `owise` cross product of `owise_binders.rs` (its `shapes.rs`) is a family here too
//! (`owise-cross`), so the competitors' binders are renamed under every strategy.
//!
//! A reviewer's binding finding is added as a new family or a new value of an axis here, so the
//! finding becomes cases of the harness (`docs/testing.md`, "Alpha-invariance harness").
//!
//! The case name spells its axes: `<family>/<axis>-<axis>-...`.

use super::{
    harness::Case,
    owise_shapes::{cross_product, source},
};

const HEADER: &str = "  imports INT
  imports BOOL
  syntax Wrap ::= s(Int)
  syntax KItem ::= go(Int) | goS(Wrap) | done(Int)
  syntax Bool ::= h(Bool) [function]
  rule h(B) => B
";

fn case(name: String, module: &str, body: &str, programs: &[&str]) -> Case {
    Case::inline(
        name,
        module,
        format!("module {module}\n{HEADER}{body}endmodule\n"),
    )
    .programs("K", programs)
}

#[derive(Clone, Copy, PartialEq)]
enum Quantifier {
    Exists,
    Forall,
}

impl Quantifier {
    fn text(self) -> &'static str {
        match self {
            Quantifier::Exists => "#Exists",
            Quantifier::Forall => "#Forall",
        }
    }

    fn tag(self) -> &'static str {
        match self {
            Quantifier::Exists => "E",
            Quantifier::Forall => "F",
        }
    }
}

const KINDS: [Quantifier; 2] = [Quantifier::Exists, Quantifier::Forall];

/// A binder over `name` at sort `Int` whose body mentions `s(name)`, the constructor the left
/// side `goS(s(X))` matches, so a pass that replaces that subterm meets the binder.
fn int_formula(kind: Quantifier, name: &str) -> String {
    match kind {
        Quantifier::Exists => format!("#Exists {name}:Int . {{s({name}) #Equals s(2)}}"),
        Quantifier::Forall => {
            format!("#Forall {name}:Int . {{s({name}) #Equals s({name} +Int 0)}}")
        }
    }
}

fn bool_formula(kind: Quantifier, name: &str) -> String {
    match kind {
        Quantifier::Exists => format!("#Exists {name}:Bool . {{{name} #Equals true}}"),
        Quantifier::Forall => {
            format!("#Forall {name}:Bool . {{{name} orBool notBool {name} #Equals true}}")
        }
    }
}

/// One binder in a rewrite rule `goS(s(X)) => done(X)`.
fn single_binder() -> Vec<Case> {
    let mut cases = Vec::new();
    for kind in KINDS {
        for (relation, name) in [("fresh", "B"), ("lhs", "X"), ("minted", "K0")] {
            for (sort, formula) in [
                ("same", int_formula(kind, name)),
                ("other", bool_formula(kind, name)),
            ] {
                for position in ["requires", "ensures", "argument", "rhs"] {
                    let rule = match position {
                        "requires" => format!(
                            "  rule [p]: <k> goS(s(X)) => done(X) ... </k> requires {formula}\n"
                        ),
                        "ensures" => format!(
                            "  rule [p]: <k> goS(s(X)) => done(X) ... </k> ensures {formula}\n"
                        ),
                        "argument" => format!(
                            "  rule [p]: <k> goS(s(X)) => done(X) ... </k> requires h({formula})\n"
                        ),
                        _ => format!(
                            "  rule [p]: <k> goS(s(X)) => done(X) #And ({formula}) ... </k>\n"
                        ),
                    };
                    cases.push(case(
                        format!("one/{}-{relation}-{sort}-{position}", kind.tag()),
                        "G",
                        &rule,
                        &["goS(s(3))", "goS(s(2))"],
                    ));
                }
            }
        }
    }
    cases
}

/// Two binders in one rule: conjoined in the `requires`, nested, or one in the `requires` and
/// one in the `ensures`.
fn two_binders() -> Vec<Case> {
    let mut cases = Vec::new();
    for (first, second) in [
        (Quantifier::Exists, Quantifier::Exists),
        (Quantifier::Exists, Quantifier::Forall),
        (Quantifier::Forall, Quantifier::Exists),
    ] {
        for (names, a, b) in [
            ("distinct", "B", "C"),
            ("same", "B", "B"),
            ("lhs", "X", "X"),
        ] {
            for structure in ["conj", "nested", "split"] {
                let (requires, ensures) = match structure {
                    "conj" => (
                        format!(
                            "({}) #And ({})",
                            int_formula(first, a),
                            int_formula(second, b)
                        ),
                        None,
                    ),
                    "nested" => (
                        format!(
                            "{} {a}:Int . ({} {b}:Int . {{s({a}) #Equals s({b} +Int 0)}})",
                            first.text(),
                            second.text()
                        ),
                        None,
                    ),
                    _ => (int_formula(first, a), Some(int_formula(second, b))),
                };
                let ensures =
                    ensures.map_or(String::new(), |ensures| format!(" ensures {ensures}"));
                cases.push(case(
                    format!("two/{}{}-{names}-{structure}", first.tag(), second.tag()),
                    "G",
                    &format!(
                        "  rule [p]: <k> goS(s(X)) => done(X) ... </k> requires {requires}{ensures}\n"
                    ),
                    &["goS(s(3))", "goS(s(2))"],
                ));
            }
        }
    }
    // Two binders of one name at two sorts, in separate scopes.
    for (names, a, b) in [("distinct", "B", "C"), ("same", "B", "B")] {
        cases.push(case(
            format!("two/EE-{names}-conj-other-sort"),
            "G",
            &format!(
                "  rule [p]: <k> goS(s(X)) => done(X) ... </k> requires ({}) #And ({})\n",
                int_formula(Quantifier::Exists, a),
                bool_formula(Quantifier::Exists, b)
            ),
            &["goS(s(3))"],
        ));
    }
    cases
}

/// Three binders in one rule.
fn three_binders() -> Vec<Case> {
    let mut cases = Vec::new();
    for kinds in [
        [Quantifier::Exists, Quantifier::Exists, Quantifier::Exists],
        [Quantifier::Exists, Quantifier::Forall, Quantifier::Exists],
    ] {
        let tag: String = kinds.iter().map(|kind| kind.tag()).collect();
        for (names, [a, b, c]) in [
            ("distinct", ["A", "B", "C"]),
            ("same", ["B", "B", "B"]),
            ("lhs", ["X", "X", "X"]),
            ("mixed", ["X", "B", "X"]),
        ] {
            for structure in ["nested", "conj", "nested-split"] {
                let [q1, q2, q3] = kinds.map(Quantifier::text);
                let (requires, ensures) = match structure {
                    "nested" => (
                        format!(
                            "{q1} {a}:Int . ({q2} {b}:Int . ({q3} {c}:Int . {{s({a}) #Equals s({b} +Int {c})}}))"
                        ),
                        None,
                    ),
                    "conj" => (
                        format!(
                            "({}) #And ({}) #And ({})",
                            int_formula(kinds[0], a),
                            int_formula(kinds[1], b),
                            int_formula(kinds[2], c)
                        ),
                        None,
                    ),
                    _ => (
                        format!("{q1} {a}:Int . ({q2} {b}:Int . {{s({a}) #Equals s({b} +Int 0)}})"),
                        Some(int_formula(kinds[2], c)),
                    ),
                };
                let ensures =
                    ensures.map_or(String::new(), |ensures| format!(" ensures {ensures}"));
                cases.push(case(
                    format!("three/{tag}-{names}-{structure}"),
                    "G",
                    &format!(
                        "  rule [p]: <k> goS(s(X)) => done(X) ... </k> requires {requires}{ensures}\n"
                    ),
                    &["goS(s(3))", "goS(s(2))"],
                ));
            }
        }
    }
    cases
}

/// A binder in a macro's right side, named apart from its parameters or like one of them,
/// with use sites that pass a variable twice, a literal, or an anonymous variable.
fn macro_binders() -> Vec<Case> {
    let mut cases = Vec::new();
    for kind in KINDS {
        for (relation, name) in [("fresh", "B"), ("param1", "N"), ("param2", "M")] {
            for (use_site, arguments) in [
                ("twice", "X, X"),
                ("literal", "X, 5"),
                ("anon-first", "_, X"),
                ("anon-second", "X, _"),
            ] {
                let body = match kind {
                    Quantifier::Exists => {
                        format!(
                            "#Exists {name}:Int . ({{N #Equals {name}}} #And {{{name} #Equals M}})"
                        )
                    }
                    Quantifier::Forall => {
                        format!("#Forall {name}:Int . {{N +Int {name} #Equals {name} +Int M}}")
                    }
                };
                cases.push(case(
                    format!("macro/{}-{relation}-{use_site}", kind.tag()),
                    "G",
                    &format!(
                        "  syntax Bool ::= m(Int, Int) [macro]\n  rule m(N, M) => {body}\n  rule [p]: <k> go(X) => done(X) ... </k> requires m({arguments})\n"
                    ),
                    &["go(3)", "go(5)", "go(0)"],
                ));
            }
        }
    }
    cases
}

/// Binders over anonymous variables, and anonymous variables under a named binder.
fn anonymous_binders() -> Vec<Case> {
    let mut cases = Vec::new();
    for kind in KINDS {
        for (form, formula) in [
            (
                "anon-binder",
                format!("{} _ . {{X #Equals _ +Int 1}}", kind.text()),
            ),
            (
                "anon-binder-sorted",
                format!("{} _:Int . {{X #Equals _ +Int 1}}", kind.text()),
            ),
            (
                "named-binder-anon-body",
                format!("{} B:Int . {{X #Equals _ +Int B}}", kind.text()),
            ),
        ] {
            cases.push(case(
                format!("anon/{}-{form}-requires", kind.tag()),
                "G",
                &format!("  rule [p]: <k> go(X) => done(X) ... </k> requires {formula}\n"),
                &["go(3)", "go(0)"],
            ));
        }
    }
    for (form, formula) in [
        ("anon-binder", "#Exists ?_ . (X ==Int ?_)"),
        ("named-binder", "#Exists ?B . (X ==Int ?B)"),
    ] {
        cases.push(case(
            format!("anon/E-{form}-ensures"),
            "G",
            &format!("  rule [p]: <k> done(X) => go(X) ... </k> ensures {formula}\n"),
            &["done(3)"],
        ));
    }
    cases
}

/// A context alias with one variable beside the strictness variables the compiler mints.
fn context_aliases() -> Vec<Case> {
    let mut cases = Vec::new();
    for strictness in ["seqstrict", "strict"] {
        for variable in ["S", "K0", "K1", "I1"] {
            let module = "GC";
            let mut case = Case::inline(
                format!("context/{strictness}-{variable}"),
                module,
                format!(
                    "module {module}\n  imports INT\n  imports BOOL\n  syntax Exp ::= Int | \"(\" Exp \")\" [bracket] | Exp \"+\" Exp [{strictness}(c)]\n  syntax KResult ::= Int\n  configuration <k> $PGM:Exp </k> <s> 0 </s>\n  context alias [c]: <k> HERE ... </k> <s> {variable} </s>\n  rule <k> I1:Int + I2:Int => I1 +Int I2 ... </k>\nendmodule\n"
                ),
            )
            .programs("Exp", &["1 + (2 + 3)"]);
            case.depth = 40;
            cases.push(case);
        }
    }
    cases
}

/// A binder in the condition of a function rule that has an `owise` competitor.
fn function_binders() -> Vec<Case> {
    let mut cases = Vec::new();
    for kind in KINDS {
        for (relation, name) in [("fresh", "B"), ("lhs", "Y")] {
            let formula = match kind {
                Quantifier::Exists => format!("#Exists {name}:Int . {{s({name}) #Equals s(Y)}}"),
                Quantifier::Forall => {
                    format!("#Forall {name}:Int . {{s({name} +Int 0) #Equals s({name})}}")
                }
            };
            cases.push(case(
                format!("function/{}-{relation}-owise", kind.tag()),
                "G",
                &format!(
                    "  syntax Int ::= f(Wrap) [function]\n  rule f(s(Y)) => Y requires {formula}\n  rule f(_) => 0 [owise]\n  rule [p]: <k> goS(W) => done(f(W)) ... </k>\n"
                ),
                &["goS(s(3))"],
            ));
        }
    }
    cases
}

const OWISE_HEADER: &str = "module P-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Pgm ::= go(Int) [symbol(go)]
endmodule
module P
  imports P-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Pgm </k>
  syntax KItem ::= done(Int) [symbol(done)]
  syntax Pair ::= g(Int, Int) [symbol(g)]
  syntax Int ::= f(Pair) [function, symbol(f)]
  rule [go]: <k> go(N) => done(f(g(N, 0))) ... </k>
";

/// A function with `owise`: binders in its competitors' conditions, named like each other, like
/// a name the `owise` axiom mints when it renames a competitor's binder apart (`Y0`), like the
/// `owise` rule's variable, or anonymous; and a binder in the `owise` rule's own condition.
fn owise_binders() -> Vec<Case> {
    let mut cases = Vec::new();
    for (first, competitor) in [
        (
            "Y",
            "  rule [p]: f(g(X:Int, _)) => 1 requires #Exists Y:Int . {X #Equals Y *Int 2}\n",
        ),
        (
            "Y0",
            "  rule [p]: f(g(X:Int, _)) => 1 requires #Exists Y0:Int . {X #Equals Y0 *Int 2}\n",
        ),
        (
            "anon",
            "  rule [p]: f(g(X:Int, _)) => 1 requires #Exists _:Int . {X #Equals _ *Int 2}\n",
        ),
    ] {
        for (second, other) in [
            ("none", String::new()),
            ("Y0", "  rule [q]: f(g(X:Int, _)) => 2 requires #Exists Y0:Bool . {Y0 #Equals X >Int 3}\n".to_owned()),
            ("Y", "  rule [q]: f(g(X:Int, _)) => 2 requires #Exists Y:Bool . {Y #Equals X >Int 3}\n".to_owned()),
        ] {
            for variable in ["Y", "P"] {
                for (condition, text) in [
                    ("plain", ""),
                    ("requires", " requires #Exists Y:Bool . {Y #Equals true}"),
                    ("ensures", " ensures #Exists Y:Bool . {Y #Equals true}"),
                ] {
                    cases.push(
                        Case::inline(
                            format!("owise/{first}-{second}-{variable}-{condition}"),
                            "P",
                            format!(
                                "{OWISE_HEADER}{competitor}{other}  rule [o]: f({variable}:Pair) => 0{text} [owise]\nendmodule\n"
                            ),
                        )
                        .syntax("P-SYNTAX")
                        .programs("Pgm", &["go(4)", "go(3)", "go(1)"]),
                    );
                }
            }
        }
    }
    cases
}

/// `#let` and `#fun` binders beside a quantifier, and a parameter beside a variable of the rule
/// at another sort, written as source text beside its base (`text-shadow-parameter`) so that the
/// parser infers the parameter's sort on its own.
fn local_function_binders() -> Vec<Case> {
    let mut cases = Vec::new();
    for (form, apart, shadow) in [
        ("fun", "#fun(Z:Int => Z", "#fun(X:Int => X"),
        ("let", "#let Z:Int = N #in Z", "#let X:Int = N #in X"),
    ] {
        let local = match form {
            "fun" => "#fun(Z:Int => Z +Int 1)(N)",
            _ => "#let Z:Int = N #in Z +Int 1",
        };
        for (annotation, outer) in [("annotated", "X:Bool"), ("inferred", "X")] {
            cases.push(
                case(
                    format!("lambda/{form}-other-sort-{annotation}"),
                    "G",
                    &format!(
                        "  syntax KItem ::= gob(Bool, Int)\n  rule [p]: <k> gob({outer}, N) => done({local}) ... </k> requires X\n"
                    ),
                    &["gob(true, 3)", "gob(false, 3)"],
                )
                .twin_variable("text-shadow-parameter", apart, shadow, ("Z", "X")),
            );
        }
    }
    for (relation, name) in [("fresh", "B"), ("lhs", "X")] {
        cases.push(case(
            format!("lambda/let-{relation}"),
            "G",
            &format!(
                "  rule [p]: <k> goS(s(X)) => done(#let {name} = 5 #in ({name} +Int X)) ... </k> requires {}\n",
                int_formula(Quantifier::Exists, "C")
            ),
            &["goS(s(3))"],
        ));
        cases.push(case(
            format!("lambda/fun-{relation}"),
            "G",
            &format!(
                "  rule [p]: <k> goS(s(X)) => done(#fun({name} => {name} +Int 1)(X)) ... </k> requires {}\n",
                int_formula(Quantifier::Exists, name)
            ),
            &["goS(s(3))"],
        ));
    }
    cases
}

/// A binder over `name` whose body has the sort `Int` (`same`, the left side's `X:Int`) or
/// `Bool` (`other`), with the binder's sort annotated or left to the parser's sort inference.
fn sorted_formula(kind: Quantifier, name: &str, sort: &str, annotated: bool) -> String {
    let annotation = match (annotated, sort) {
        (false, _) => "",
        (true, "same") => ":Int",
        (true, _) => ":Bool",
    };
    match (kind, sort) {
        (Quantifier::Exists, "same") => {
            format!("#Exists {name}{annotation} . {{{name} #Equals 2}}")
        }
        (Quantifier::Forall, "same") => {
            format!("#Forall {name}{annotation} . {{{name} +Int 0 #Equals {name}}}")
        }
        (Quantifier::Exists, _) => format!("#Exists {name}{annotation} . {{{name} #Equals true}}"),
        (Quantifier::Forall, _) => {
            format!("#Forall {name}{annotation} . {{{name} orBool notBool {name} #Equals true}}")
        }
    }
}

/// Source-text twins: a binder named apart from the other variables of its rule, and the twin
/// text that names it like one of them (the left side's `X:Int`, or a sibling binder `Y` of
/// another scope), so the parser infers the sorts of both spellings on its own. Under the
/// binding rule the two texts are alpha-variants whatever the sorts, so a twin the parser
/// refuses or sorts differently is a defect of the parser's scoping.
fn source_twins() -> Vec<Case> {
    let mut cases = Vec::new();
    for kind in KINDS {
        for sort in ["same", "other"] {
            for (annotation, annotated) in [("annotated", true), ("inferred", false)] {
                let apart = sorted_formula(kind, "Y", sort, annotated);
                let shadow = sorted_formula(kind, "X", sort, annotated);
                for position in ["requires", "ensures", "argument", "rhs"] {
                    let rule = match position {
                        "requires" => {
                            format!("  rule [p]: <k> go(X) => done(X) ... </k> requires {apart}\n")
                        }
                        "ensures" => {
                            format!("  rule [p]: <k> go(X) => done(X) ... </k> ensures {apart}\n")
                        }
                        "argument" => format!(
                            "  rule [p]: <k> go(X) => done(X) ... </k> requires h({apart})\n"
                        ),
                        _ => format!("  rule [p]: <k> go(X) => done(X) #And ({apart}) ... </k>\n"),
                    };
                    cases.push(
                        case(
                            format!("source/{}-lhs-{sort}-{annotation}-{position}", kind.tag()),
                            "G",
                            &rule,
                            &["go(3)", "go(2)"],
                        )
                        .twin("text-shadow-lhs", &apart, &shadow),
                    );
                }
                // A sibling binder `Y` at `Bool`, and a second binder at `sort` named apart
                // (`Z`) or like the sibling.
                let sibling = sorted_formula(Quantifier::Exists, "Y", "other", annotated);
                let second = sorted_formula(kind, "Z", sort, annotated);
                let clash = sorted_formula(kind, "Y", sort, annotated);
                cases.push(
                    case(
                        format!("source/{}-sibling-{sort}-{annotation}-requires", kind.tag()),
                        "G",
                        &format!(
                            "  rule [p]: <k> go(X) => done(X) ... </k> requires ({sibling}) #And ({second})\n"
                        ),
                        &["go(3)"],
                    )
                    .twin("text-shadow-sibling", &second, &clash),
                );
            }
        }
    }
    cases
}

/// Source-text twins whose renaming writes a variable with U+E000 in its name, which a
/// definition's own `#KVariable` token makes writable: a free variable renamed to
/// `<binder>\u{E000}<n>` beside a binder that shares its spelling with a free variable
/// (`text-mark-binder`), and a free variable renamed to `<other>\u{E000}<digits>`, another
/// variable's spelling, in a rule whose binder the parser renames apart (`text-mark-other`). The
/// parser's names for binders renamed apart must avoid every written name.
fn marked_twins() -> Vec<Case> {
    let mut cases = Vec::new();
    for kind in KINDS {
        let formula = sorted_formula(kind, "Y", "same", true);
        for position in ["requires", "ensures"] {
            for (relation, number, other) in [("binder", "0", "Y"), ("other", "5", "Z")] {
                let free = format!("Q\u{E000}{number}");
                let renamed = format!("{other}\u{E000}{number}");
                cases.push(
                    case(
                        format!("mark/{}-{relation}-{position}", kind.tag()),
                        "G",
                        &format!(
                            "{}  syntax KItem ::= go3(Int, Int, Int) | done3(Int, Int, Int)\n  rule [p]: <k> go3(Y:Int, Z:Int, {free}:Int) => done3(Y, Z, {free}) ... </k> {position} {formula}\n",
                            super::probes::MARKED_VARIABLES
                        ),
                        &["go3(1, 2, 3)", "go3(1, 2, 2)"],
                    )
                    .twin_variable(
                        &format!("text-mark-{relation}"),
                        &free,
                        &renamed,
                        (&free, &renamed),
                    ),
                );
            }
        }
    }
    cases
}

/// A simplification whose condition binds a name that only its `concrete` or `symbolic`
/// attribute mentions, and its twin with the binder alone renamed (`text-attribute-binder`): the
/// attribute is outside the binder's scope, so the two are judged alike.
fn attribute_binders() -> Vec<Case> {
    let mut cases = Vec::new();
    for kind in KINDS {
        let formula = |name: &str| match kind {
            Quantifier::Exists => format!("#Exists {name}:Int . {{{name} #Equals X}}"),
            Quantifier::Forall => format!("#Forall {name}:Int . {{{name} +Int 0 #Equals {name}}}"),
        };
        for attribute in ["concrete", "symbolic"] {
            cases.push(
                case(
                    format!("attribute/{}-{attribute}", kind.tag()),
                    "G",
                    &format!(
                        "  syntax Int ::= f(Int) [function, total]\n  rule f(_) => 0\n  rule f(X) => X requires {} [simplification, {attribute}(Z)]\n  rule [p]: <k> go(X) => done(f(X)) ... </k>\n",
                        formula("Z")
                    ),
                    &["go(3)"],
                )
                .twin("text-attribute-binder", &formula("Z"), &formula("W")),
            );
        }
    }
    cases
}

/// A binder in the `requires` or `ensures` spelled apart from the variable of a list update the
/// left side matches outside a collection argument, and its twin spelled like it
/// (`text-shadow-list`): the binder reads no list, so the two are judged alike.
fn list_update_binders() -> Vec<Case> {
    let mut cases = Vec::new();
    for kind in KINDS {
        let formula = |name: &str| match kind {
            Quantifier::Exists => format!("#Exists {name}:List . {{{name} #Equals .List}}"),
            Quantifier::Forall => format!("#Forall {name}:List . {{{name} #Equals {name}}}"),
        };
        for position in ["requires", "ensures"] {
            cases.push(
                Case::inline(
                    format!("list/{}-{position}", kind.tag()),
                    "G",
                    format!(
                        "module G\n  imports INT\n  imports BOOL\n  imports LIST\n  syntax KItem ::= gol(List) | done(Int)\n  rule [p]: <k> gol(L:List [ 0 <- 2 ]) => done(1) ... </k> {position} {}\nendmodule\n",
                        formula("M")
                    ),
                )
                .programs("K", &["gol(ListItem(2))", "gol(ListItem(5))"])
                .twin("text-shadow-list", &formula("M"), &formula("L")),
            );
        }
    }
    cases
}

/// Claims, compiled `--for-proving`: a binder in a claim's `requires` or `ensures` beside the
/// claim's left-side variable, and the anonymous binders of FU-26 and D2 in a claim.
fn claim_binders() -> Vec<Case> {
    let claim = |name: String, claim: &str| {
        case(
            name,
            "G",
            &format!("  rule <k> goS(s(X)) => done(X) ... </k>\n  rule <k> go(X) => done(X) ... </k>\n  {claim}\n"),
            &[],
        )
        .for_proving()
    };
    let mut cases = Vec::new();
    for kind in KINDS {
        for (relation, name, sort) in [
            ("fresh", "B", "same"),
            ("fresh", "B", "other"),
            ("lhs", "X", "same"),
        ] {
            let formula = if sort == "same" {
                int_formula(kind, name)
            } else {
                bool_formula(kind, name)
            };
            for position in ["requires", "ensures"] {
                cases.push(claim(
                    format!("claim/{}-{relation}-{sort}-{position}", kind.tag()),
                    &format!("claim <k> goS(s(X)) => done(X) ... </k> {position} {formula}"),
                ));
            }
        }
        cases.push(claim(
            format!("claim/{}-anon-binder-requires", kind.tag()),
            &format!(
                "claim <k> go(X) => done(X) ... </k> requires {} _ . (X =/=Int _)",
                kind.text()
            ),
        ));
    }
    cases.push(claim(
        "claim/E-anon-binder-ensures".to_owned(),
        "claim <k> go(X) => done(?Y) ... </k> ensures #Exists ?_ . (?Y ==Int ?_)",
    ));
    cases
}

/// A binder beside the left side's `X` of `s(X)` in an `anywhere` rule and in a
/// `simplification` of a function.
fn rule_kinds() -> Vec<Case> {
    let mut cases = Vec::new();
    for kind in KINDS {
        for (relation, name) in [("fresh", "B"), ("lhs", "X")] {
            let formula = int_formula(kind, name);
            cases.push(case(
                format!("rulekind/anywhere-{}-{relation}", kind.tag()),
                "G",
                &format!(
                    "  syntax KItem ::= t(Wrap)\n  rule t(s(X)) => done(X) requires {formula} [anywhere]\n  rule <k> goS(W) => t(W) ... </k>\n"
                ),
                &["goS(s(3))", "goS(s(2))"],
            ));
            cases.push(case(
                format!("rulekind/simplification-{}-{relation}", kind.tag()),
                "G",
                &format!(
                    "  syntax Int ::= f(Wrap) [function, total]\n  rule f(_) => 0\n  rule f(s(X)) => X requires {formula} [simplification]\n  rule <k> goS(W) => done(f(W)) ... </k>\n"
                ),
                &["goS(s(3))", "goS(s(2))"],
            ));
        }
    }
    cases
}

/// A binder under `#Not` or beside `#Or` in a rule's `requires`.
fn connectives() -> Vec<Case> {
    let mut cases = Vec::new();
    for kind in KINDS {
        for (relation, name) in [("fresh", "B"), ("lhs", "X")] {
            let formula = int_formula(kind, name);
            for (connective, requires) in [
                ("not", format!("#Not({formula})")),
                ("or", format!("({formula}) #Or {{X #Equals 7}}")),
            ] {
                cases.push(case(
                    format!("connective/{connective}-{}-{relation}", kind.tag()),
                    "G",
                    &format!("  rule [p]: <k> goS(s(X)) => done(X) ... </k> requires {requires}\n"),
                    &["goS(s(3))", "goS(s(2))"],
                ));
            }
        }
    }
    cases
}

/// A binder in the right side of an `alias` or `macro-rec` rule, as in `macro_binders`.
fn macro_attributes() -> Vec<Case> {
    let mut cases = Vec::new();
    for attribute in ["alias", "macro-rec"] {
        for kind in KINDS {
            for (relation, name) in [("fresh", "B"), ("param1", "N"), ("param2", "M")] {
                for (use_site, arguments) in [("twice", "X, X"), ("literal", "X, 5")] {
                    let body = match kind {
                        Quantifier::Exists => format!(
                            "#Exists {name}:Int . ({{N #Equals {name}}} #And {{{name} #Equals M}})"
                        ),
                        Quantifier::Forall => {
                            format!("#Forall {name}:Int . {{N +Int {name} #Equals {name} +Int M}}")
                        }
                    };
                    cases.push(case(
                        format!("macroattr/{attribute}-{}-{relation}-{use_site}", kind.tag()),
                        "G",
                        &format!(
                            "  syntax Bool ::= m(Int, Int) [{attribute}]\n  rule m(N, M) => {body}\n  rule [p]: <k> go(X) => done(X) ... </k> requires m({arguments})\n"
                        ),
                        &["go(3)", "go(5)", "go(0)"],
                    ));
                }
            }
        }
    }
    cases
}

/// `?` binders, which bind their variable in their body only, so existential lifting quantifies
/// only the `?` variables free in the right side and the `ensures`:
/// - beside the right side's free `?Y`, a binder named apart (`?Z`), without a sigil (`Z`), or
///   named `?Y`, which shadows it, in the `ensures` (`ensures`), in the right side (`rhs`), or in
///   a claim's `ensures` (`claim`);
/// - two nested `?` binders (`nested`): named apart (`distinct`), spelled alike (`same`), or the
///   inner one named `?Y` beside the free `?Y` (`shadow`);
/// - a `?` binder with no free `?` variable in the sentence: in the right side (`rhs-only`), in
///   the `ensures` beside a `?Z` free in the `ensures` only (`ensures-free`), and in a function, an
///   `anywhere` or a macro rule, alone (`one`) or nested inside a binder spelled alike (`same`).
fn existential_binders() -> Vec<Case> {
    let mut cases = Vec::new();
    let body = |kind: Quantifier, binder: &str| match kind {
        Quantifier::Exists => format!("{{?Y #Equals {binder} +Int X}}"),
        Quantifier::Forall => format!("{{?Y +Int {binder} #Equals {binder} +Int X}}"),
    };
    for kind in KINDS {
        for (form, binder) in [("q-apart", "?Z"), ("plain-apart", "Z"), ("q-shadow", "?Y")] {
            let formula = format!("{} {binder}:Int . {}", kind.text(), body(kind, binder));
            cases.push(case(
                format!("existential/{}-{form}", kind.tag()),
                "G",
                &format!("  rule [p]: <k> go(X) => done(?Y) ... </k> ensures {formula}\n"),
                &["go(3)"],
            ));
            cases.push(case(
                format!("existential/{}-{form}-rhs", kind.tag()),
                "G",
                &format!(
                    "  rule [p]: <k> go(X) => done(?Y) #And ({formula}) ... </k> ensures {{?Y #Equals X +Int 1}}\n"
                ),
                &["go(3)"],
            ));
            cases.push(
                case(
                    format!("existential/{}-{form}-claim", kind.tag()),
                    "G",
                    &format!(
                        "  rule <k> go(X) => done(X) ... </k>\n  claim <k> go(X) => done(?Y) ... </k> ensures {formula}\n"
                    ),
                    &[],
                )
                .for_proving(),
            );
        }
    }
    for (outer, inner) in [
        (Quantifier::Exists, Quantifier::Forall),
        (Quantifier::Exists, Quantifier::Exists),
        (Quantifier::Forall, Quantifier::Exists),
    ] {
        let (q1, q2) = (outer.text(), inner.text());
        for (names, formula) in [
            (
                "distinct",
                format!("{q1} ?A:Int . ({q2} ?B:Int . {{?A +Int ?B #Equals ?B +Int ?Y}})"),
            ),
            (
                "same",
                format!("{q1} ?A:Int . ({{?A #Equals X}} #And ({q2} ?A:Int . {{?A #Equals ?Y}}))"),
            ),
            (
                "shadow",
                format!("{q1} ?A:Int . ({q2} ?Y:Int . {{?A +Int ?Y #Equals ?Y +Int X}})"),
            ),
        ] {
            cases.push(case(
                format!("existential/{}{}-nested-{names}", outer.tag(), inner.tag()),
                "G",
                &format!(
                    "  rule [p]: <k> go(X) => done(?Y) ... </k> ensures ({formula}) #And {{?Y #Equals X +Int 1}}\n"
                ),
                &["go(2)"],
            ));
        }
    }
    for kind in KINDS {
        let q = kind.text();
        let tag = kind.tag();
        cases.push(case(
            format!("existential/{tag}-rhs-only"),
            "G",
            &format!(
                "  syntax KItem ::= wrap(Bool)\n  rule [p]: <k> go(X) => wrap({q} ?B:Int . {{?B #Equals X}}) ... </k>\n"
            ),
            &["go(3)"],
        ));
        cases.push(case(
            format!("existential/{tag}-ensures-free"),
            "G",
            &format!(
                "  rule [p]: <k> go(X) => done(X) ... </k> ensures {{?Z #Equals X}} #And ({q} ?W:Int . {{?W #Equals ?Z}})\n"
            ),
            &["go(3)"],
        ));
        // The binder over `?B` whose body equates it with the rule's variable `v`.
        let one = |v: &str| format!("{q} ?B:Int . {{?B #Equals {v}}}");
        let same = |v: &str| format!("{q} ?B:Int . ({{?B #Equals {v}}} #And ({}))", one(v));
        // Each shape over the rule's variable `X` and over the macro's parameter `N`.
        for (shape, rule, parameter) in
            [("one", one("X"), one("N")), ("same", same("X"), same("N"))]
        {
            cases.push(case(
                format!("existential/function-{tag}-{shape}"),
                "G",
                &format!(
                    "  syntax Int ::= f(Int) [function]\n  rule f(X) => X +Int 1 ensures {rule}\n  rule [p]: <k> go(X) => done(f(X)) ... </k>\n"
                ),
                &["go(2)", "go(0)"],
            ));
            cases.push(case(
                format!("existential/anywhere-{tag}-{shape}"),
                "G",
                &format!(
                    "  syntax Foo ::= g(Int) | q(Int)\n  syntax KItem ::= box(Foo)\n  rule g(X) => q(X) ensures {rule} [anywhere]\n  rule [p]: <k> go(X) => box(g(X)) ... </k>\n"
                ),
                &["go(3)"],
            ));
            cases.push(case(
                format!("existential/macro-{tag}-{shape}"),
                "G",
                &format!(
                    "  syntax Bool ::= m(Int) [macro]\n  rule m(N) => {parameter}\n  rule [p]: <k> go(X) => done(X) ... </k> requires m(X)\n"
                ),
                &["go(3)"],
            ));
        }
    }
    cases
}

/// A binder in the `requires` of a context with `HOLE`, named apart from the context's variable
/// or like it.
fn hole_contexts() -> Vec<Case> {
    let mut cases = Vec::new();
    for kind in KINDS {
        for (relation, name) in [("fresh", "B"), ("shadow", "X")] {
            let formula = match kind {
                Quantifier::Exists => format!("#Exists {name}:Int . {{{name} #Equals 1}}"),
                Quantifier::Forall => {
                    format!("#Forall {name}:Int . {{{name} +Int 0 #Equals {name}}}")
                }
            };
            let module = "GH";
            cases.push(
                Case::inline(
                    format!("hole/{}-{relation}", kind.tag()),
                    module,
                    format!(
                        "module {module}\n  imports INT\n  imports BOOL\n  syntax Exp ::= Int | f(Exp, Int)\n  syntax KResult ::= Int\n  configuration <k> $PGM:Exp </k>\n  context f(HOLE, X) requires {formula}\n  rule <k> f(I:Int, J) => I +Int J ... </k>\nendmodule\n"
                    ),
                )
                .programs("Exp", &["f(1, 2)"]),
            );
        }
    }
    cases
}

/// A binder in a part of a sentence that a stage copies into a second position of it: the context
/// of a rule or claim outside its rewrite, which both sides share and injection copies into each
/// when it lifts the rewrite to the top (also beside a condition binder spelled like the name a
/// renamed copy would take), the argument of a macro parameter that occurs twice, and the body of
/// a context, from which the freezer is built. The copies bind their names in disjoint scopes, so
/// they are renamed apart, and every renaming of the written binder gives the same sentence.
fn copied_binders() -> Vec<Case> {
    let mut cases = Vec::new();
    for kind in KINDS {
        let quantifier = kind.text();
        let tag = kind.tag();
        let shared = format!("pair({quantifier} Y:Int . Y, (sa => sb))");
        let pair = "  syntax KItem ::= pair(Int, KItem) | \"sa\" | \"sb\"\n";
        cases.push(case(
            format!("copy/{tag}-rule-shared"),
            "G",
            &format!("{pair}  rule [p]: <k> {shared} ... </k>\n"),
            &[],
        ));
        cases.push(case(
            format!("copy/{tag}-rule-shared-beside-mint"),
            "G",
            &format!(
                "{pair}  rule [p]: <k> {shared} ... </k> requires #Exists Y0:Int . {{Y0 #Equals 1}}\n"
            ),
            &[],
        ));
        cases.push(
            case(
                format!("copy/{tag}-claim-shared"),
                "G",
                &format!(
                    "{pair}  rule <k> pair(_, sa) => pair(1, sb) ... </k>\n  claim <k> {shared} ... </k>\n"
                ),
                &[],
            )
            .for_proving(),
        );
        cases.push(case(
            format!("copy/{tag}-macro-parameter-twice"),
            "G",
            &format!(
                "  syntax KItem ::= two(Int) [macro] | pr(Int, Int)\n  rule two(I) => pr(I, I)\n  rule [p]: <k> go(_) => two({quantifier} Y:Int . Y) ... </k>\n"
            ),
            &[],
        ));
        let module = "GC";
        cases.push(Case::inline(
            format!("copy/{tag}-context-body"),
            module,
            format!(
                "module {module}\n  imports INT\n  imports BOOL\n  syntax Exp ::= Int | f(Exp, Int)\n  syntax KResult ::= Int\n  configuration <k> $PGM:Exp </k>\n  context f(HOLE, {quantifier} Y:Int . Y)\n  rule <k> f(I:Int, J) => I +Int J ... </k>\nendmodule\n"
            ),
        ));
    }
    cases
}

/// Contexts whose freezer holds two or more variables. A written context holds two variables
/// besides `HOLE`, spelled in their occurrence order or against it; a context alias holds its
/// variable `V` beside the argument variables strictness mints, spelled `S` (after the minted
/// names), `K0` (one of them) or `A` (before them). Each is written with no cell or inside the
/// main cell. The heating and cooling rules of an alpha-variant must be alpha-variants of the
/// base's, so the freezer's argument order must not depend on the names.
fn frozen_contexts() -> Vec<Case> {
    let mut cases = Vec::new();
    for (cell, open, close) in [("bare", "", ""), ("cell", "<k> ", " ... </k>")] {
        for (order, variables) in [("XY", "X, Y"), ("YX", "Y, X")] {
            let module = "GZ";
            cases.push(
                Case::inline(
                    format!("frozen/written-{cell}-{order}"),
                    module,
                    format!(
                        "module {module}\n  imports INT\n  imports BOOL\n  syntax Exp ::= Int | f(Exp, Int, Int)\n  syntax KResult ::= Int\n  configuration <k> $PGM:Exp </k>\n  context {open}f(HOLE, {variables}){close}\n  rule <k> f(I:Int, J, L) => I +Int J *Int 10 +Int L *Int 100 ... </k>\nendmodule\n"
                    ),
                )
                .programs("Exp", &["f(f(1, 2, 3), 4, 5)"]),
            );
        }
        for strictness in ["strict", "seqstrict"] {
            for variable in ["S", "K0", "A"] {
                let module = "GW";
                let mut case = Case::inline(
                    format!("frozen/alias-{cell}-{strictness}-{variable}"),
                    module,
                    format!(
                        "module {module}\n  imports INT\n  imports BOOL\n  syntax Exp ::= Int | \"(\" Exp \")\" [bracket] | Exp \"+\" Exp [{strictness}(c)] | wrap(Exp, Int)\n  syntax KResult ::= Int\n  configuration <k> $PGM:Exp </k>\n  context alias [c]: {open}wrap(HERE, {variable}:Int){close}\n  rule <k> I1:Int + I2:Int => I1 +Int I2 ... </k>\n  rule <k> wrap(I:Int, J:Int) => I +Int J ... </k>\nendmodule\n"
                    ),
                )
                .programs("Exp", &["wrap((1 + 2) + (3 + 4), 5)"]);
                case.depth = 40;
                cases.push(case);
            }
        }
    }
    cases
}

/// Search patterns, compiled against a definition with a macro whose right side holds a binder:
/// a pattern with an anonymous binder, with a named binder, and with the macro at a use site
/// that passes an anonymous or a named variable. Each hand-written twin (`search-*`) renames the
/// pattern only, and every strategy is applied to the base pattern of each twin and to a use of
/// the macro at the pattern's free variable (`<pattern>/<strategy>`).
fn search_patterns() -> Vec<Case> {
    let module = "GS";
    let twins = [
        (
            "search-anon-exists",
            "<k> go(X) </k> requires #Exists _ . {X #Equals _ +Int 1}",
            "<k> go(X) </k> requires #Exists _A . {X #Equals _B +Int 1}",
        ),
        (
            "search-anon-forall",
            "<k> go(X) </k> requires #Forall _ . (X =/=Int _)",
            "<k> go(X) </k> requires #Forall _A . (X =/=Int _B)",
        ),
        (
            "search-named-apart",
            "<k> go(X) </k> requires #Exists Y:Int . {X #Equals Y +Int 1}",
            "<k> go(X) </k> requires #Exists Z:Int . {X #Equals Z +Int 1}",
        ),
        (
            "search-named-capture",
            "<k> go(X) ~> done(W) </k> requires #Exists Y:Int . {X #Equals Y +Int 1}",
            "<k> go(X) ~> done(W) </k> requires #Exists W:Int . {X #Equals W +Int 1}",
        ),
        (
            "search-macro-anon",
            "<k> go(X) </k> requires m(_)",
            "<k> go(X) </k> requires m(_A)",
        ),
        (
            "search-macro-named-apart",
            "<k> go(X) </k> requires m(Z:Int)",
            "<k> go(X) </k> requires m(W:Int)",
        ),
        (
            "search-macro-named-capture",
            "<k> go(X) </k> requires m(Z:Int)",
            "<k> go(X) </k> requires m(Y:Int)",
        ),
    ];
    let mut case = Case::inline(
        "search/patterns",
        module,
        format!(
            "module {module}\n  imports INT\n  imports BOOL\n  syntax KItem ::= go(Int) | done(Int)\n  syntax Bool ::= m(Int) [macro]\n  rule m(N) => #Forall Y:Int . {{N =/=Int Y +Int Y #Equals true}}\n  rule <k> go(X) => done(X) ... </k>\nendmodule\n"
        ),
    );
    for (name, base, variant) in twins {
        case = case.search(name, base, variant);
    }
    for (name, base, _) in twins {
        case = case.pattern(name, base);
    }
    vec![
        case.pattern("macro-free", "<k> go(X) </k> requires m(X)"),
        search_shapes(),
    ]
}

/// The binder shapes of the `one`, `two` and `anon` families as search patterns over the left
/// side `goS(s(X))`: one binder (kind, relation to `X`, sort, in the `requires` or a function
/// argument), two binders (conjoined or nested; distinct, same or the left side's name), and
/// anonymous and `?` binders. Every strategy is applied to each (`<shape>/<strategy>`).
fn search_shapes() -> Case {
    let mut case = Case::inline(
        "search/shapes",
        "G",
        format!("module G\n{HEADER}  rule <k> goS(s(X)) => done(X) ... </k>\nendmodule\n"),
    );
    let pattern = |requires: &str| format!("<k> goS(s(X)) </k> requires {requires}");
    for kind in KINDS {
        for (relation, name) in [("fresh", "B"), ("lhs", "X"), ("minted", "K0")] {
            for (sort, formula) in [
                ("same", int_formula(kind, name)),
                ("other", bool_formula(kind, name)),
            ] {
                case = case
                    .pattern(
                        &format!("one-{}-{relation}-{sort}-requires", kind.tag()),
                        &pattern(&formula),
                    )
                    .pattern(
                        &format!("one-{}-{relation}-{sort}-argument", kind.tag()),
                        &pattern(&format!("h({formula})")),
                    );
            }
        }
    }
    for (first, second) in [
        (Quantifier::Exists, Quantifier::Exists),
        (Quantifier::Exists, Quantifier::Forall),
        (Quantifier::Forall, Quantifier::Exists),
    ] {
        for (names, a, b) in [
            ("distinct", "B", "C"),
            ("same", "B", "B"),
            ("lhs", "X", "X"),
        ] {
            case = case
                .pattern(
                    &format!("two-{}{}-{names}-conj", first.tag(), second.tag()),
                    &pattern(&format!(
                        "({}) #And ({})",
                        int_formula(first, a),
                        int_formula(second, b)
                    )),
                )
                .pattern(
                    &format!("two-{}{}-{names}-nested", first.tag(), second.tag()),
                    &pattern(&format!(
                        "{} {a}:Int . ({} {b}:Int . {{s({a}) #Equals s({b} +Int 0)}})",
                        first.text(),
                        second.text()
                    )),
                );
        }
    }
    case.pattern(
        "two-EE-distinct-conj-other-sort",
        &pattern(&format!(
            "({}) #And ({})",
            int_formula(Quantifier::Exists, "B"),
            bool_formula(Quantifier::Exists, "C")
        )),
    )
    .pattern(
        "anon-E-anon-binder",
        &pattern("#Exists _ . {X #Equals _ +Int 1}"),
    )
    .pattern("anon-F-anon-binder", &pattern("#Forall _ . (X =/=Int _)"))
    .pattern(
        "anon-E-named-binder-anon-body",
        &pattern("#Exists B:Int . {X #Equals _ +Int B}"),
    )
    .pattern(
        "existential-E-q-binder",
        &pattern("#Exists ?B:Int . {s(X) #Equals s(?B)}"),
    )
}

/// The realizable shapes of the `owise` cross product of `owise_binders.rs`, run at the
/// programs that test runs.
fn owise_cross_product() -> Vec<Case> {
    cross_product()
        .into_iter()
        .filter(|(_, dropped)| dropped.is_none())
        .map(|(shape, _)| {
            Case::inline(
                format!("owise-cross/{}", shape.name().replace('/', "-")),
                "P",
                source(&shape),
            )
            .syntax("P-SYNTAX")
            .programs("Pgm", &["go(1)", "go(2)", "go(4)"])
        })
        .collect()
}

/// Every generated case, in a fixed order.
pub fn cases() -> Vec<Case> {
    [
        single_binder(),
        two_binders(),
        three_binders(),
        macro_binders(),
        anonymous_binders(),
        context_aliases(),
        function_binders(),
        owise_binders(),
        local_function_binders(),
        source_twins(),
        marked_twins(),
        list_update_binders(),
        attribute_binders(),
        claim_binders(),
        rule_kinds(),
        connectives(),
        macro_attributes(),
        existential_binders(),
        hole_contexts(),
        copied_binders(),
        frozen_contexts(),
        search_patterns(),
        owise_cross_product(),
    ]
    .concat()
}
