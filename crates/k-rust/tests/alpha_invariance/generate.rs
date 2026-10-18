//! The generated grammar: small definitions whose sentences hold up to three binders, each
//! along the axes of a binding relation. Every generated definition goes through the full
//! compile path and `krun`, together with each alpha-variant the strategies of `rename.rs` give.
//!
//! The axes:
//! - the binder kind: `#Exists` or `#Forall`;
//! - the bound name's relation to the other names of the sentence: fresh, the left side's
//!   variable, another binder's name, a macro parameter, a context alias's variable, a function
//!   rule's variable, a name the compiler mints (`K0`), or an anonymous variable;
//! - the bound variable's sort: the sort of the related variable (`Int`), or another (`Bool`);
//! - the position: the `requires`, the `ensures`, an argument of a function in the condition, or
//!   the right side;
//! - the number of binders and how they are placed: one; two or three conjoined, nested, or split
//!   between `requires` and `ensures`;
//! - the sentence kind: a rewrite rule, an `anywhere` rule, a `simplification`, a function rule
//!   with an `owise` competitor, a macro rule (`macro`, `macro-rec`, `alias`), a context with
//!   `HOLE`, a context alias, or a claim (compiled `--for-proving`);
//! - the connective around the binder: none, `#Not`, `#Or`;
//! - the sigil of the bound variable: none, or `?` beside a free right-side `?` variable;
//! - the route: the parsed definition renamed and relinked (every strategy), source text written
//!   beside the base with a binder annotated or left to the parser's sort inference (`source`),
//!   or a search pattern compiled against the definition (`search`).
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

/// `#let` and `#fun` binders beside a quantifier.
fn local_function_binders() -> Vec<Case> {
    let mut cases = Vec::new();
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

/// A named binder in the `ensures` beside the right side's free `?Y`: a `?` binder named apart
/// (`?Z`), a binder without a sigil (`Z`), or a `?` binder named `?Y`, which shadows it.
fn existential_binders() -> Vec<Case> {
    let mut cases = Vec::new();
    for kind in KINDS {
        for (form, binder) in [("q-apart", "?Z"), ("plain-apart", "Z"), ("q-shadow", "?Y")] {
            let ensures = match kind {
                Quantifier::Exists => {
                    format!("#Exists {binder}:Int . {{?Y #Equals {binder} +Int X}}")
                }
                Quantifier::Forall => {
                    format!("#Forall {binder}:Int . {{?Y +Int {binder} #Equals {binder} +Int X}}")
                }
            };
            cases.push(case(
                format!("existential/{}-{form}", kind.tag()),
                "G",
                &format!("  rule [p]: <k> go(X) => done(?Y) ... </k> ensures {ensures}\n"),
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

/// Search patterns, compiled against a definition with a macro whose right side holds a binder:
/// a pattern with an anonymous binder, with a named binder, and with the macro at a use site
/// that passes an anonymous or a named variable. Each variant renames the pattern only.
fn search_patterns() -> Vec<Case> {
    let module = "GS";
    vec![
        Case::inline(
            "search/patterns",
            module,
            format!(
                "module {module}\n  imports INT\n  imports BOOL\n  syntax KItem ::= go(Int) | done(Int)\n  syntax Bool ::= m(Int) [macro]\n  rule m(N) => #Forall Y:Int . {{N =/=Int Y +Int Y #Equals true}}\n  rule <k> go(X) => done(X) ... </k>\nendmodule\n"
            ),
        )
        .search(
            "search-anon-exists",
            "<k> go(X) </k> requires #Exists _ . {X #Equals _ +Int 1}",
            "<k> go(X) </k> requires #Exists _A . {X #Equals _B +Int 1}",
        )
        .search(
            "search-anon-forall",
            "<k> go(X) </k> requires #Forall _ . (X =/=Int _)",
            "<k> go(X) </k> requires #Forall _A . (X =/=Int _B)",
        )
        .search(
            "search-named-apart",
            "<k> go(X) </k> requires #Exists Y:Int . {X #Equals Y +Int 1}",
            "<k> go(X) </k> requires #Exists Z:Int . {X #Equals Z +Int 1}",
        )
        .search(
            "search-named-capture",
            "<k> go(X) ~> done(W) </k> requires #Exists Y:Int . {X #Equals Y +Int 1}",
            "<k> go(X) ~> done(W) </k> requires #Exists W:Int . {X #Equals W +Int 1}",
        )
        .search(
            "search-macro-anon",
            "<k> go(X) </k> requires m(_)",
            "<k> go(X) </k> requires m(_A)",
        )
        .search(
            "search-macro-named-apart",
            "<k> go(X) </k> requires m(Z:Int)",
            "<k> go(X) </k> requires m(W:Int)",
        )
        .search(
            "search-macro-named-capture",
            "<k> go(X) </k> requires m(Z:Int)",
            "<k> go(X) </k> requires m(Y:Int)",
        ),
    ]
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
        claim_binders(),
        rule_kinds(),
        connectives(),
        macro_attributes(),
        existential_binders(),
        hole_contexts(),
        search_patterns(),
        owise_cross_product(),
    ]
    .concat()
}
