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
