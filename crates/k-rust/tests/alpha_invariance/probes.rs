//! The defect probes: one definition per known binding defect, and the alpha-variant spelling of
//! each that compiles correctly, so a strategy that maps one onto the other exposes the defect.

use super::harness::Case;

const HEADER: &str = "  imports INT\n  imports BOOL\n";

fn probe(name: &str, module: &str, body: &str, programs: &[&str]) -> Case {
    Case::inline(
        name,
        module,
        format!("module {module}\n{HEADER}{body}endmodule\n"),
    )
    .programs("K", programs)
}

const GO: &str = "  syntax KItem ::= go(Int) | done(Int)\n";

/// Every probe, in a fixed order.
pub fn probes() -> Vec<Case> {
    let mut cases = vec![
        // FU-26: `#Forall _ . (X =/=Int _)` binds nothing, so it holds at every X; the converter
        // reads the binder as binding every anonymous variable of its body.
        probe(
            "fu26-forall-anonymous",
            "FU26",
            &format!(
                "{GO}  rule [p]: <k> go(X) => done(X) ... </k> requires #Forall _ . (X =/=Int _)\n"
            ),
            &["go(1)"],
        ),
        probe(
            "fu26-exists-anonymous",
            "FU26E",
            &format!(
                "{GO}  rule [q]: <k> go(X) => done(X +Int 1) ... </k> requires (#Exists _:Int . (X ==Int _ +Int 1)) #And {{X >Int 100 #Equals true}}\n"
            ),
            &["go(1)", "go(101)"],
        ),
        // D2 (FU-33): existential lifting reads `?` variables through binders.
        probe(
            "d2-ensures-exists-anonymous",
            "D2",
            &format!(
                "{GO}  rule [r]: <k> done(X) => go(X) ... </k> ensures #Exists ?_ . (X ==Int ?_)\n"
            ),
            &["done(1)"],
        ),
        // D1 (FU-32): a macro binder captures the use site's anonymous variable.
        probe(
            "d1-macro-binder-anonymous-use",
            "MAC",
            &format!(
                "{GO}  syntax Bool ::= m(Int) [macro]\n  rule m(N) => #Forall Y:Int . {{N =/=Int Y +Int Y #Equals true}}\n  rule [p]: <k> go(X) => done(X) ... </k> requires m(_)\n"
            ),
            &["go(1)"],
        ),
        probe(
            "d1-macro-binder-named-use",
            "MAC2",
            &format!(
                "{GO}  syntax Bool ::= m(Int) [macro]\n  rule m(N) => #Forall Y:Int . {{N =/=Int Y +Int Y #Equals true}}\n  rule [p]: <k> go(X) => done(X) ... </k> requires m(Z:Int)\n"
            ),
            &["go(1)"],
        ),
        // D3 (FU-34): the definition check treats a binder as binding its name sentence-wide.
        probe(
            "d3-rhs-variable-under-ensures-binder",
            "RHSB",
            &format!(
                "{GO}  rule [p]: <k> go(_) => done(Y) ... </k> ensures #Exists Y:Int . {{Y #Equals 1}}\n"
            ),
            &["go(3)"],
        ),
        probe(
            "d3-rhs-variable-unbound",
            "RHSC",
            &format!("{GO}  rule [p]: <k> go(_) => done(Y) ... </k>\n"),
            &["go(3)"],
        ),
        // D4 (FU-35): a macro binder shadows a macro parameter.
        probe(
            "d4-macro-binder-shadows-parameter",
            "MACSH2",
            &format!(
                "{GO}  syntax Bool ::= m(Int, Int) [macro]\n  rule m(N, M) => #Exists M:Int . ({{N #Equals M}} #And {{M #Equals 0}})\n  rule [p]: <k> go(X) => done(X) ... </k> requires m(X, X)\n"
            ),
            &["go(3)", "go(0)"],
        ),
        probe(
            "d4-macro-binder-shadows-parameter-literal",
            "MACSH",
            &format!(
                "{GO}  syntax Bool ::= m(Int, Int) [macro]\n  rule m(N, M) => #Exists M:Int . {{N #Equals M}}\n  rule [p]: <k> go(X) => done(X) ... </k> requires m(X, 5)\n"
            ),
            &["go(3)"],
        ),
        // D5 (FU-36): `minimize term construction` replaces a subterm under a binder that rebinds
        // one of its variables.
        probe(
            "d5-binder-shadows-lhs-variable",
            "MINB",
            "  syntax Wrap ::= s(Int)\n  syntax KItem ::= go(Wrap) | done(Int)\n  rule [p]: <k> go(s(X)) => done(X) ... </k> requires #Exists X:Int . {s(X) #Equals s(2)}\n",
            &["go(s(3))"],
        ),
        probe(
            "d5-binder-apart-from-lhs-variable",
            "MINB2",
            "  syntax Wrap ::= s(Int)\n  syntax KItem ::= go(Wrap) | done(Int)\n  rule [p]: <k> go(s(X)) => done(X) ... </k> requires #Exists Z:Int . {s(Z) #Equals s(2)}\n",
            &["go(s(3))"],
        ),
        // Shadowing that every pass scopes correctly.
        probe(
            "binder-shadows-lhs-variable-same-sort",
            "SHSAME",
            &format!(
                "{GO}  rule [p]: <k> go(Y) => done(Y) ... </k> requires #Exists Y:Int . {{Y #Equals 5}}\n"
            ),
            &["go(3)"],
        ),
        probe(
            "lambda-shadows-lhs-variable",
            "LAM",
            &format!("{GO}  rule [p]: <k> go(X) => done(#fun(X => X +Int 1)(5) +Int X) ... </k>\n"),
            &["go(100)"],
        ),
        probe(
            "let-shadows-lhs-variable",
            "LET",
            &format!("{GO}  rule [p]: <k> go(X) => done(#let X = 5 #in (X +Int 1)) ... </k>\n"),
            &["go(3)"],
        ),
        probe(
            "condition-exists-anonymous",
            "EXANON",
            &format!(
                "{GO}  rule [p]: <k> go(X) => done(X) ... </k> requires #Exists _ . {{X #Equals _ +Int 1}}\n"
            ),
            &["go(3)"],
        ),
        probe(
            "condition-exists-named",
            "EXNAMED",
            &format!(
                "{GO}  rule [p]: <k> go(X) => done(X) ... </k> requires #Exists W:Int . {{X #Equals Z:Int +Int 1}}\n"
            ),
            &["go(3)"],
        ),
    ];
    // D6 (FU-37): a context alias's `K0` merges with the strictness variable `K0`.
    for (name, module, variable) in [
        ("d6-context-alias-variable-k0", "CTXK0", "K0"),
        ("d6-context-alias-variable-s", "CTXS", "S"),
    ] {
        let mut case = Case::inline(
            name,
            module,
            format!(
                "module {module}\n{HEADER}  syntax Exp ::= Int | \"(\" Exp \")\" [bracket] | Exp \"+\" Exp [seqstrict(c)]\n  syntax KResult ::= Int\n  configuration <k> $PGM:Exp </k> <s> 0 </s>\n  context alias [c]: <k> HERE ... </k> <s> {variable} </s>\n  rule <k> I1:Int + I2:Int => I1 +Int I2 ... </k>\nendmodule\n"
            ),
        )
        .programs("Exp", &["1 + (2 + 3)"]);
        case.depth = 40;
        cases.push(case);
    }
    cases.extend(owise_seeds());
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

/// The owise renaming of MLP/6: the seed shapes of its fix-3 review, each a function with
/// `owise` whose competitors or `owise` rule hold binders.
fn owise_seeds() -> Vec<Case> {
    [
        // A bound name that clashes with a name minted when an earlier competitor's binder is
        // renamed apart (`Y` to `Y0`).
        (
            "owise-mint-clash-condition",
            "  rule [p]: f(g(X:Int, _)) => 1 requires #Exists Y:Int . {X #Equals Y *Int 2}\n  rule [q]: f(g(X:Int, _)) => 2 requires #Exists Y0:Bool . {Y0 #Equals X >Int 3}\n  rule [o]: f(Y:Pair) => 0 [owise]\n",
        ),
        (
            "owise-mint-clash-argument",
            "  rule [p]: f(g(X:Int, _)) => 1 requires #Exists Y:Int . {X #Equals Y *Int 2}\n  rule [q]: f(#Exists Y0:Int . g(Y0, 7)) => 2\n  rule [o]: f(Y:Pair) => 0 [owise]\n",
        ),
        // Partial clashes: only some of a competitor's bound names are taken.
        (
            "owise-partial-anonymous-and-named",
            "  rule [q]: f(g(X:Int, _)) => 1 requires (#Exists _:Int . {X #Equals _ *Int 2}) #And (#Exists Y:Int . {Y #Equals X})\n  rule [o]: f(Y:Pair) => 0 [owise]\n",
        ),
        (
            "owise-partial-nested",
            "  rule [p]: f(g(X:Int, _)) => 1 requires #Exists Y:Int . {X #Equals Y *Int 2}\n  rule [q]: f(g(X:Int, _)) => 1 requires #Exists Y:Int . #Exists Y0:Int . ({X #Equals Y} #And {Y0 #Equals Y} #And {true #Equals Y0 <Int 3})\n  rule [o]: f(Y:Pair) => 0 [owise]\n",
        ),
        (
            "owise-partial-nested-three",
            "  rule [p]: f(g(X:Int, _)) => 1 requires #Exists Y:Int . {X #Equals Y *Int 2}\n  rule [q]: f(g(X:Int, _)) => 1 requires #Exists Y:Int . #Exists Y0:Int . #Exists Y1:Int . ({X #Equals Y} #And {Y0 #Equals Y} #And {Y1 #Equals Y0} #And {true #Equals Y1 <Int 3})\n  rule [o]: f(g(Y:Int, _)) => 0 [owise]\n",
        ),
        (
            "owise-partial-anonymous",
            "  rule [p]: f(g(X:Int, _)) => 1 requires #Exists Y:Int . {X #Equals Y *Int 2}\n  rule [q]: f(g(X:Int, _)) => 1 requires (#Exists _:Int . {X #Equals _ *Int 2}) #And (#Exists _:Int . {X #Equals _ *Int 3})\n  rule [o]: f(g(_, _)) => 0 [owise]\n",
        ),
        // `owise` rules whose own names come from a quantifier in their condition.
        (
            "owise-rule-binder-requires",
            "  rule [q]: f(g(X:Int, _)) => 1 requires #Exists Y:Int . {X #Equals Y *Int 2}\n  rule [o]: f(P:Pair) => 0 requires #Exists Y:Bool . {Y #Equals true} [owise]\n",
        ),
        (
            "owise-rule-binder-ensures",
            "  rule [q]: f(g(X:Int, _)) => 1 requires #Exists Y:Int . {X #Equals Y *Int 2}\n  rule [o]: f(P:Pair) => 0 ensures #Exists Y:Bool . {Y #Equals true} [owise]\n",
        ),
        // An anonymous binder's own sort annotation.
        (
            "owise-rule-anonymous-binder-sort",
            "  rule [p]: f(g(X:Int, _)) => 1 requires #Exists Y:Int . {X #Equals Y *Int 2}\n  rule [q]: f(g(X:Int, _)) => 1 requires #Exists _:Int . {X #Equals _ *Int 2}\n  rule [o]: f(P:Pair) => 0 requires #Exists _:Bool . {_ #Equals true} [owise]\n",
        ),
    ]
    .into_iter()
    .map(|(name, rules)| {
        Case::inline(name, "P", format!("{OWISE_HEADER}{rules}endmodule\n"))
            .syntax("P-SYNTAX")
            .programs("Pgm", &["go(4)", "go(3)", "go(1)"])
    })
    .collect()
}
