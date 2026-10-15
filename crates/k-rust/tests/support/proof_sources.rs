//! Definitions whose proofs are checked both through `krust kprove` (`cli.rs`: verdict lines and
//! exit status) and in-process (`proof_semantics.rs`: the prover's result on the KORE krust
//! compiles from them).
//!
//! Test binaries include this file with `#[path = "support/proof_sources.rs"] mod proof_sources;`.

/// `app` on values is an `anywhere` overload of `app` on expressions, rewritten to the constructor
/// `c` only for a positive first argument. The claim's symbolic step on `app(N, 0)` applies the
/// priority-10 rule where `N <=Int 0`, and its remainder `N >Int 0` simplifies `app(N, 0)` to
/// `c(N)`, which only the priority-50 `c` rule rewrites. `$NEXT` places the overloaded item at
/// the `<k>` head (empty) or after a `mark()` head.
pub const ANYWHERE_OVERLOAD_REMAINDER: &str = r#"
module OVL-SYNTAX
  imports INT-SYNTAX
  syntax Val ::= Int | c(Int) | app(Val, Val) [overload(app)]
  syntax Exp ::= Val | app(Exp, Exp) [overload(app)]
  syntax KItem ::= done(Int) | mark()
endmodule

module OVL
  imports OVL-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Exp </k> <n> 0 </n>
  rule app(X:Int, _:Int):Val => c(X) requires X >Int 0 [anywhere]
  rule <k> $NEXT _:Val => done(0) ... </k> <n> X </n> requires X <=Int 0 [priority(10)]
  rule <k> $NEXT c(X) => done(X) ... </k>
endmodule

module OVL-SPEC
  imports OVL
  claim <k> $NEXT app(N:Int, 0):Val => done(?_M) </k> <n> N </n>
endmodule
"#;

/// A trusted lemma or rule records a condition over X, either a kept unifier equation or
/// the definedness of a discarded partial argument, before the collection solver binds X
/// from a set element. The application covers only instances where the condition holds of
/// the bound value. Both lemmas are true; both main claims are false at A = 0. The rule's
/// condition is c(B, A) = f(A).
pub const LATER_BINDING_KEPT: &str = r#"
module LEMMAKEPT
  imports INT
  imports SET
  syntax Elem ::= a(Int) | b(Int)
  syntax KItem ::= go(Set) | run(Int, Set) | done(Int)
  configuration <k> $PGM:K </k>
  rule <k> go(S) => run(5, S) ... </k>
  rule <k> run(N, SetItem(a(X)) _S) => done(X) ... </k> requires N ==Int X +Int 1
endmodule
module LEMMAKEPT-SPEC
  imports LEMMAKEPT
  claim [lemma]: <k> run(X +Int 1, SetItem(a(X)) SetItem(b(_Y))) => done(X) ... </k> [trusted]
  claim [main]: <k> go(SetItem(a(A)) SetItem(b(_B))) => done(A) ... </k>
endmodule
"#;

pub const LATER_BINDING_RECOVERED: &str = r#"
module LEMMADEF
  imports INT
  imports SET
  syntax Elem ::= a(Int) | b(Int)
  syntax KItem ::= go(Set) | run(Int, Set) | done(Int)
  syntax Int ::= h(Int) [function, total]
  configuration <k> $PGM:K </k>
  rule h(_) => 7
  rule <k> go(S) => run(7, S) ... </k>
  rule <k> run(7, SetItem(a(X)) _S) => done(X) ... </k> requires X =/=Int 0
endmodule
module LEMMADEF-SPEC
  imports LEMMADEF
  claim [lemma]: <k> run(h(10 /Int X), SetItem(a(X)) SetItem(b(_Y))) => done(X) ... </k> [trusted]
  claim [main]: <k> go(SetItem(a(A)) SetItem(b(_B))) => done(A) ... </k>
endmodule
"#;

pub const LATER_BINDING_RULE: &str = r#"
module RULESOLVED
  imports INT
  imports SET
  syntax Elem ::= a(Int) | b(Int)
  syntax Foo ::= c(Int, Int) | f(Int) [function, total]
  syntax KItem ::= go(Int, Set) | foo(Int, Foo, Set) | bar(Int) | done()
  configuration <k> $PGM:K </k>
  rule <k> go(A, S) => foo(A, f(A), S) ... </k>
  rule <k> foo(Y, c(X, Y), SetItem(a(X)) SetItem(b(_Z))) => bar(X) ... </k>
endmodule
module RULESOLVED-SPEC
  imports RULESOLVED
  claim [main]: <k> go(A, SetItem(a(B)) SetItem(b(C))) => done() ... </k>
endmodule
"#;

/// A condition over `10 /Int A`, written directly (`PLAIN`) or through the lambda a `#let`
/// generates (`LET`).
pub const LET_PARTIAL_CONDITION: &str = r#"
module LETDIV-SYNTAX
  imports INT-SYNTAX
  syntax Op ::= half(Int) [symbol(half)]
  syntax Prog ::= "halt" [symbol(halt)] | seq(Op, Prog) [symbol(seq)]
endmodule

module LETDIV
  imports LETDIV-SYNTAX
  imports INT
  configuration <k> .K </k>
  rule [half]: seq(half(A), P) => P requires $CONDITION
endmodule

module LETDIV-SPEC
  imports LETDIV
  claim [symbolic]: <k> seq(half(_X:Int), halt) => halt </k>
  claim [ground]: <k> seq(half(0), halt) => halt </k>
endmodule
"#;

/// Rules whose result is undefined on part of the instances they apply to: a false `ensures`
/// that the step cannot decide (`apart`, `cover`, `low`), one that always has a witness
/// (`fresh`), a refuted one beside a sibling with a disjoint `requires` (`pickpos`), and one
/// before an unconditional sibling (`skipbot`). `cover` and `skip` declare the rule with the
/// undefined instances first, so a one-path step tries it before the sibling that covers them;
/// `low`'s other rule is `owise`, of lower priority, and so blocked where `lowbot` applies.
pub const UNDEFINED_STEP: &str = r#"
module UNDEF-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= "halt" [symbol(halt)]
                | "done" [symbol(done)]
                | "fresh" [symbol(fresh)]
                | apart(Int, Int) [symbol(apart)]
                | cover(Int, Int) [symbol(cover)]
                | val(Int) [symbol(val)]
                | pick(Int) [symbol(pick)]
                | "skip" [symbol(skip)]
                | low(Int, Int) [symbol(low)]
endmodule

module UNDEF
  imports UNDEF-SYNTAX
  imports BASIC-K
  imports INT
  configuration <k> $PGM:Prog </k>
  rule [apart]:   <k> apart(A, B) => halt </k> ensures A =/=Int B
  rule [cover]:   <k> cover(A, B) => halt </k> ensures A =/=Int B
  rule [coverok]: <k> cover(A, B) => halt </k> requires A ==Int B
  rule [fresh]:   <k> fresh => val(?X:Int) </k> ensures ?X >Int 0
  rule [pickpos]: <k> pick(I) => halt </k> requires I >Int 0 ensures false
  rule [pickneg]: <k> pick(I) => done </k> requires I <=Int 0
  rule [skipbot]: <k> skip => halt </k> ensures false
  rule [skipok]:  <k> skip => done </k>
  rule [lowbot]:  <k> low(A, B) => halt </k> ensures A =/=Int B
  rule [lowow]:   <k> low(_, _) => halt </k> [owise]
endmodule

module UNDEF-SPEC
  imports UNDEF
  claim [sym]:       <k> apart(_X, _Y) => halt </k>
  claim [gnd]:       <k> apart(0, 0) => halt </k>
  claim [sym-one]:   <k> apart(X, Y) => halt </k> requires X >=Int Y [one-path]
  claim [defined]:   <k> apart(X, Y) => halt </k> requires X =/=Int Y
  claim [cover]:     <k> cover(_X, _Y) => halt </k>
  claim [fresh]:     <k> fresh => val(?Y:Int) </k> ensures ?Y >Int 0
  claim [fresh-one]: <k> fresh => val(?Y:Int) </k> ensures ?Y >=Int 1 [one-path]
  claim [pick]:      <k> pick(_I) => done </k>
  claim [cover-one]: <k> cover(_X, _Y) => halt </k> [one-path]
  claim [skip-one]:  <k> skip => done </k> [one-path]
  claim [skip]:      <k> skip => done </k>
  claim [pick-one]:  <k> pick(_I) => done </k> [one-path]
  claim [low-one]:   <k> low(_X, _Y) => halt </k> [one-path]
  claim [low]:       <k> low(_X, _Y) => halt </k>
endmodule
"#;

pub const NEGATIVE_POWER: &str = r#"
module NEGPOW
  imports INT
  imports BOOL
  configuration <k> $PGM:Pgm </k>
  syntax Pgm ::= gm(Int)
  syntax KItem ::= "yes" | "no"
  rule <k> gm(B) => yes </k> requires 3 ^%Int B 7 ==Int 0
  rule <k> gm(_) => no </k> [owise]
endmodule
module NEGPOW-SPEC
  imports NEGPOW
  claim [negative]: <k> gm(B) => yes </k> requires B <Int 0
  claim [minus-one]: <k> gm(B) => no </k> requires B ==Int -1
endmodule
"#;

/// Claims whose own constraints hold a partial term, `X /Int Y`, undefined where `Y` is 0. The
/// only rule, `pos(X, Y) => yes(X /Int Y) requires X /Int Y >Int 0`, does not apply where `Y` is
/// 0, so `pos(X, 0)` is a stuck configuration. A K `requires b` means `b = true`, which is
/// `\bottom` where a term of `b` is undefined, so under a negation it holds there; an ML equality
/// of two terms holds where both denote the same element or both denote nothing. By claim:
/// - `cpos` and `cposctl` exclude `Y = 0`, and every other instance reaches `yes`: proven;
/// - `cneg` holds on no instance: proven;
/// - `cnoteq`, `cnegml` and `cmeq` hold exactly at `Y = 0`, where `pos(X, 0)` is stuck: not
///   proven;
/// - `crhs`'s destination equality fails where exactly one of `Y` and `Z` is 0, and `crhsatom`'s
///   atom is undefined at `Y = 0`: not proven;
/// - `cens`'s negated destination equality holds at `Y = 0`, and `cdiv`'s destination equality
///   has the defined value `?R` on one side where `Y` is not 0: proven.
pub const DEFPROBE: &str = r#"
module DEFPROBE-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Res ::= yes(Int) [symbol(yes)]
               | done() [symbol(done)]
               | pos(Int, Int) [symbol(pos)]
               | w3(Int, Int, Int) [symbol(w3)]
  syntax Int ::= imp() [function, total, impure, symbol(imp)]
endmodule

module DEFPROBE
  imports DEFPROBE-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  imports K-EQUAL
  configuration <k> $PGM:Res </k>

  rule [pos]: pos(X, Y) => yes(X /Int Y) requires X /Int Y >Int 0
endmodule
"#;

/// The claims of [`DEFPROBE`] whose constraints have a definedness-explicit form; see
/// [`DEFPROBE`] for each one's answer.
pub const DEFPROBE_SPEC: &str = r#"
module DEFPROBE-SPEC
  imports DEFPROBE

  claim [cpos]: <k> pos(X, Y) => yes(?_) </k> requires notBool (X /Int Y <=Int 0)
  claim [cposctl]: <k> pos(X, Y) => yes(?_) </k> requires X /Int Y >Int 0
  claim [cneg]: <k> pos(X, Y) => done() </k> requires notBool (X /Int Y >Int 5) andBool notBool (X /Int Y <=Int 5)
  claim [cnoteq]: <k> pos(X, Y) => done() </k> requires #Not({ X /Int Y *Int 0 #Equals 0 })
  claim [cnegml]: <k> pos(X, Y) => done() </k>
    requires #Not({ true #Equals X /Int Y >Int 5 }) #And #Not({ true #Equals X /Int Y <=Int 5 })
  claim [cmeq]: <k> pos(X, Y) => done() </k> requires { X /Int Y #Equals X /Int Y +Int 1 }
  claim [crhs]: <k> w3(X, Y, Z) => w3(X, Y, Z) </k> ensures { X /Int Y *Int 0 #Equals X /Int Z *Int 0 }
  claim [crhsatom]: <k> w3(X, Y, Z) => w3(X, Y, Z) </k> ensures X /Int Y ==Int X /Int Y
  claim [cens]: <k> w3(X, Y, Z) => w3(X, Y, Z) </k> requires Y ==Int 0
    ensures #Not({ X /Int Y *Int 0 #Equals 0 })
  claim [cdiv]: <k> w3(X, Y, Z) => w3(X, Y, Z) </k> requires #Not({ Y #Equals 0 })
    ensures { ?R #Equals X /Int Y }
endmodule
"#;

/// A claim of [`DEFPROBE`] whose constraint has no definedness-explicit form, beside one that
/// has.
pub const DEFPROBE_REFUSED_SPEC: &str = r#"
module DEFPROBE-REFUSED-SPEC
  imports DEFPROBE

  // The definedness of `1 /Int imp()`, which the `#if` evaluates only where `X` is not 0,
  // depends on the impure `imp()`, so the claim's constraint has no definedness-explicit form.
  claim [crefused]: <k> pos(X, Y) => done() </k>
    requires #if X ==Int 0 #then true #else 1 /Int imp() >Int 0 #fi
  claim [cposctl]: <k> pos(X, Y) => yes(?_) </k> requires X /Int Y >Int 0
endmodule
"#;
