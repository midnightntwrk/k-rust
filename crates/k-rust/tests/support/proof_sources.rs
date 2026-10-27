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

/// Three claims over [`DEFPROBE`]'s `w3`, written in KORE, each with an `\equals` that reads a
/// term as a predicate, which K source never emits: `HAND.eqtop`'s destination
/// `\equals(Y ==Int Y, \top{Bool})` and `HAND.lhseqtop`'s left-hand side are `\bottom` (`Bool` has
/// two elements), and `HAND.andterm`'s destination `\equals(\and{Bool}(Y ==Int 0, Z ==Int 0),
/// false)` is false where its operands differ. Read as written, the first two would be decided as
/// the `\iff` of a term and `\top` and the third as a conjunction of predicates, neither of which
/// is their meaning, so each is refused. The sentences go in a module that imports
/// `DEFPROBE-SPEC`, or in that module itself.
pub const TERM_READ_AS_PREDICATE_CLAIMS: &str = r#"
  claim{} \implies{SortGeneratedTopCell{}}(
      \and{SortGeneratedTopCell{}}(\top{SortGeneratedTopCell{}}(), Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortRes{}, SortKItem{}}(Lblw3{}(VarX:SortInt{}, VarY:SortInt{}, VarZ:SortInt{})), dotk{}())), Lbl'-LT-'generatedCounter'-GT-'{}(Var'Unds'Gen0:SortInt{}))),
      weakAlwaysFinally{SortGeneratedTopCell{}}(\exists{SortGeneratedTopCell{}}(Var'QuesUnds'Gen1:SortInt{}, \and{SortGeneratedTopCell{}}(Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortRes{}, SortKItem{}}(Lblw3{}(VarX:SortInt{}, VarY:SortInt{}, VarZ:SortInt{})), dotk{}())), Lbl'-LT-'generatedCounter'-GT-'{}(Var'QuesUnds'Gen1:SortInt{})), \equals{SortBool{}, SortGeneratedTopCell{}}(Lbl'UndsEqlsEqls'Int'Unds'{}(VarY:SortInt{}, VarY:SortInt{}), \top{SortBool{}}())))))
    [UNIQUE'Unds'ID{}("hand-eqtop"), label{}("HAND.eqtop")]
  claim{} \implies{SortGeneratedTopCell{}}(
      \and{SortGeneratedTopCell{}}(\equals{SortBool{}, SortGeneratedTopCell{}}(Lbl'Unds'andBool'Unds'{}(Lbl'UndsEqlsSlshEqls'Int'Unds'{}(VarY:SortInt{}, \dv{SortInt{}}("0")), Lbl'UndsEqlsEqls'Int'Unds'{}(VarZ:SortInt{}, \dv{SortInt{}}("0"))), \dv{SortBool{}}("true")), Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortRes{}, SortKItem{}}(Lblw3{}(VarX:SortInt{}, VarY:SortInt{}, VarZ:SortInt{})), dotk{}())), Lbl'-LT-'generatedCounter'-GT-'{}(Var'Unds'Gen0:SortInt{}))),
      weakAlwaysFinally{SortGeneratedTopCell{}}(\exists{SortGeneratedTopCell{}}(Var'QuesUnds'Gen1:SortInt{}, \and{SortGeneratedTopCell{}}(Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortRes{}, SortKItem{}}(Lblw3{}(VarX:SortInt{}, VarY:SortInt{}, VarZ:SortInt{})), dotk{}())), Lbl'-LT-'generatedCounter'-GT-'{}(Var'QuesUnds'Gen1:SortInt{})), \equals{SortBool{}, SortGeneratedTopCell{}}(\and{SortBool{}}(Lbl'UndsEqlsEqls'Int'Unds'{}(VarY:SortInt{}, \dv{SortInt{}}("0")), Lbl'UndsEqlsEqls'Int'Unds'{}(VarZ:SortInt{}, \dv{SortInt{}}("0"))), \dv{SortBool{}}("false"))))))
    [UNIQUE'Unds'ID{}("hand-andterm"), label{}("HAND.andterm")]
  claim{} \implies{SortGeneratedTopCell{}}(
      \and{SortGeneratedTopCell{}}(\equals{SortBool{}, SortGeneratedTopCell{}}(Lbl'UndsEqlsEqls'Int'Unds'{}(VarY:SortInt{}, VarY:SortInt{}), \top{SortBool{}}()), Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortRes{}, SortKItem{}}(Lblw3{}(VarX:SortInt{}, VarY:SortInt{}, VarZ:SortInt{})), dotk{}())), Lbl'-LT-'generatedCounter'-GT-'{}(Var'Unds'Gen0:SortInt{}))),
      weakAlwaysFinally{SortGeneratedTopCell{}}(\exists{SortGeneratedTopCell{}}(Var'QuesUnds'Gen1:SortInt{}, \and{SortGeneratedTopCell{}}(Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortRes{}, SortKItem{}}(Lblw3{}(VarX:SortInt{}, VarY:SortInt{}, VarZ:SortInt{})), dotk{}())), Lbl'-LT-'generatedCounter'-GT-'{}(Var'QuesUnds'Gen1:SortInt{})), \bottom{SortGeneratedTopCell{}}()))))
    [UNIQUE'Unds'ID{}("hand-lhseqtop"), label{}("HAND.lhseqtop")]
"#;

/// Definition conditions compare partial terms by their matching-logic denotations.
/// The positive equality below holds exactly at a zero divisor; its negation holds exactly
/// at a nonzero divisor. The initial commands themselves are defined in either region.
pub const PARTIAL_EQUALITY_CONDITIONS: &str = r#"
module PARTIAL-CONDITIONS
  imports INT
  imports BOOL
  imports K-EQUAL
  syntax Cmd ::= positive(Int, Int) | negative(Int, Int) | objectBool(Int, Int)
               | ensured(Int, Int) | negativeEnsured(Int, Int) | "hit"
  syntax Int ::= selected(Int, Int) [function, total]
  rule selected(X:Int, D:Int) => 7 requires {X /Int D #Equals (X /Int D) +Int 1}
  rule selected(X:Int, D:Int) => 9 requires #Not({X /Int D #Equals (X /Int D) +Int 1})
  rule <k> positive(X:Int, D:Int) => hit </k>
    requires {X /Int D #Equals (X /Int D) +Int 1}
  rule <k> negative(X:Int, D:Int) => hit </k>
    requires #Not({X /Int D #Equals (X /Int D) +Int 1})
  rule <k> objectBool(X:Int, D:Int) => hit </k>
    requires X /Int D ==Int (X /Int D) +Int 1
  rule <k> ensured(X:Int, D:Int) => hit </k>
    ensures {X /Int D #Equals (X /Int D) +Int 1}
  rule <k> negativeEnsured(X:Int, D:Int) => hit </k>
    ensures #Not({X /Int D #Equals (X /Int D) +Int 1})
  configuration <T> <k> $PGM:K </k> <v> .K </v> </T>
endmodule
module PARTIAL-CONDITIONS-SPEC
  imports PARTIAL-CONDITIONS
  claim [positive-zero]: <k> positive(1, 0) => hit </k>
  claim [negative-zero]: <k> negative(1, 0) => hit </k>
  claim [positive-nonzero]: <k> positive(1, 1) => hit </k>
  claim [negative-nonzero]: <k> negative(1, 1) => hit </k>
  claim [symbolic-zero]: <k> positive(X:Int, D:Int) => hit </k> requires D ==Int 0
  claim [symbolic-negative-zero]: <k> negative(X:Int, D:Int) => hit </k> requires D ==Int 0
  claim [symbolic-negative-nonzero]: <k> negative(X:Int, D:Int) => hit </k> requires D =/=Int 0
  claim [object-bool-zero]: <k> objectBool(1, 0) => hit </k>
  claim [ensured-zero]: <k> ensured(1, 0) => hit </k>
  claim [negative-ensured-zero]: <k> negativeEnsured(1, 0) => hit </k>
  claim [ensured-nonzero]: <k> ensured(1, 1) => hit </k>
  claim [negative-ensured-nonzero]: <k> negativeEnsured(1, 1) => hit </k>
  claim [equation-zero]: <k> .K </k> <v> selected(X:Int, D:Int) => 7 </v> requires D ==Int 0
  claim [equation-nonzero]: <k> .K </k> <v> selected(X:Int, D:Int) => 9 </v> requires D =/=Int 0
endmodule
"#;

/// Literal rows and guarded rows describe the same value on established input regions.
/// Unknown matches, rejected attributes and recursive guards must not select a value.
pub const LITERAL_EQUATION_CONDITIONS: &str = r#"
module LITERAL-CONDITIONS
  imports INT
  imports BOOL
  syntax Int ::= bitValue(Bool) [function, total]
               | guardedBit(Bool) [function, total]
               | code(Int, Bool, Int) [function, total]
               | preferred(Bool) [function, total]
               | concreteRow(Int, Bool) [function, total]
               | symbolicRow(Int, Bool) [function, total]
               | circularRow(Int, Bool) [function, total]
  rule bitValue(true) => 1
  rule bitValue(false) => 0
  rule guardedBit(B:Bool) => 1 requires B
  rule guardedBit(B:Bool) => 0 requires notBool B
  rule code(7, true, X:Int) => X +Int 1 requires X >Int 0
  rule preferred(true) => 1 [priority(40)]
  rule preferred(B:Bool) => 2 [owise]
  rule concreteRow(X:Int, true) => X +Int 1 [concrete]
  rule symbolicRow(X:Int, true) => X +Int 1 [symbolic]
  rule circularRow(X:Int, true) => 1 requires circularRow(X, true) ==Int 1
  configuration <T> <k> $PGM:K </k> <v> .K </v> </T>
endmodule
module LITERAL-CONDITIONS-SPEC
  imports LITERAL-CONDITIONS
  claim [true-row]: <k> .K </k> <v> bitValue(B:Bool) => 1 </v> requires B
  claim [false-row]: <k> .K </k> <v> bitValue(B:Bool) => 0 </v> requires notBool B
  claim [wrong-row]: <k> .K </k> <v> bitValue(B:Bool) => 1 </v> requires notBool B
  claim [unknown-row]: <k> .K </k> <v> bitValue(B:Bool) => 1 </v>
  claim [arithmetic-row]: <k> .K </k> <v> bitValue(X:Int <Int 256) => 1 </v>
    requires 0 <=Int X andBool X <Int 256
  claim [guarded-control]: <k> .K </k> <v> guardedBit(X:Int <Int 256) => 1 </v>
    requires 0 <=Int X andBool X <Int 256
  claim [several-literals]: <k> .K </k> <v> code(N:Int, B:Bool, X:Int) => X +Int 1 </v>
    requires N ==Int 7 andBool B andBool X >Int 0
  claim [unknown-guard]: <k> .K </k> <v> code(N:Int, B:Bool, X:Int) => X +Int 1 </v>
    requires N ==Int 7 andBool B
  claim [refuted-literal]: <k> .K </k> <v> code(N:Int, B:Bool, X:Int) => X +Int 1 </v>
    requires N ==Int 8 andBool B andBool X >Int 0
  claim [preferred-held]: <k> .K </k> <v> preferred(B:Bool) => 1 </v> requires B
  claim [preferred-refuted]: <k> .K </k> <v> preferred(B:Bool) => 2 </v> requires notBool B
  claim [preferred-unknown]: <k> .K </k> <v> preferred(B:Bool) => 2 </v>
  claim [concrete-rejected]: <k> .K </k> <v> concreteRow(X:Int, B:Bool) => X +Int 1 </v> requires B
  claim [symbolic-rejected]: <k> .K </k> <v> symbolicRow(3, B:Bool) => 4 </v> requires B
  claim [recursive-guard]: <k> .K </k> <v> circularRow(X:Int, B:Bool) => 1 </v> requires B
  claim [partial-operand]: <k> .K </k> <v> bitValue((1 /Int X:Int) <Int 256) => 1 </v> requires X >Int 1
endmodule
"#;

/// Independent scalar identities stay available through opaque total functions and map writes.
/// No function-behavior, map-extensionality or injection-injectivity axiom is supplied.
pub const CONTEXTUAL_SCALAR_EQUALITIES: &str = r#"
module CONTEXTUAL-EQUALITY
  imports INT
  imports BOOL
  imports MAP
  syntax Int ::= opaque(Int) [function, total]
               | opaquePartial(Int) [function]
               | named(Int) [function, total, smtlib(contextualNamed)]
  configuration <T> <k> $PGM:K </k> <v> .K </v> <m> .Map </m> </T>
endmodule
module CONTEXTUAL-EQUALITY-SPEC
  imports CONTEXTUAL-EQUALITY
  claim [opaque]: <k> .K </k> <v> opaque(X:Int >>Int 8) => opaque(X /Int 256) </v>
    requires 0 <=Int X andBool X <Int 65536
  claim [named]: <k> .K </k> <v> named(X:Int >>Int 8) => named(X /Int 256) </v>
    requires 0 <=Int X andBool X <Int 65536
  claim [map-write]: <k> .K </k> <m> M:Map [0 <- X:Int >>Int 8] => M [0 <- X /Int 256] </m>
    requires 0 <=Int X andBool X <Int 65536
  claim [map-chain]: <k> .K </k>
    <m> M:Map [0 <- X:Int >>Int 8] [1 <- X %Int 256]
       => M [0 <- X /Int 256] [1 <- X -Int (X /Int 256) *Int 256] </m>
    requires 0 <=Int X andBool X <Int 65536
  claim [wrong-value]: <k> .K </k> <m> M:Map [0 <- X:Int >>Int 8] => M [0 <- 1] </m>
    requires 0 <=Int X andBool X <Int 256
  claim [wrong-frame]: <k> .K </k> <m> M:Map [0 <- X:Int >>Int 8] => .Map [0 <- X /Int 256] </m>
    requires 0 <=Int X andBool X <Int 65536
  claim [different-heads]: <k> .K </k> <v> opaque(X:Int) => named(X) </v>
  claim [opaque-partial]: <k> .K </k> <v> opaquePartial(X:Int >>Int 8) => opaquePartial(X /Int 256) </v>
    requires 0 <=Int X andBool X <Int 65536
  claim [overwritten-not-injective]: <k> .K </k>
    <m> M:Map [0 <- X:Int] [0 <- 7] => M [0 <- X +Int 1] [0 <- 7] </m>
  claim [overwrite-does-not-equate-values]: <k> .K </k> <v> X:Int ~> Y:Int </v>
    <m> M:Map [0 <- X] [0 <- 7] => M [0 <- Y] [0 <- 7] </m>
    ensures X ==Int Y
  claim [overwrite-retains-definedness]: <k> .K </k> <v> X:Int </v>
    <m> M:Map [0 <- 7] => M [0 <- opaquePartial(X)] [0 <- 7] </m>
  claim [xor-retains-definedness]: <k> .K </k> <v> X:Int ~> 0 => X ~> (opaquePartial(X) xorInt opaquePartial(X)) </v>
  claim [negative-truncation]: <k> .K </k> <v> opaque(X:Int >>Int 8) => opaque(X /Int 256) </v>
    requires -256 <Int X andBool X <Int 0
endmodule
"#;

/// The current target is a proof obligation, not an execution cutpoint. Weak circular
/// proofs can close an infinite cycle, while finite terminal violations remain false.
pub const WEAK_CLAIM_CONTINUATION: &str = r#"
module WEAK-CONTINUATION
  imports INT
  imports BOOL
  syntax KItem ::= tick() | count(Int) | spin() | done(Int)
  configuration <k> $PGM:K </k> <n> 0 </n>
  rule <k> tick() </k> <n> 0 => 1 </n>
  rule <k> count(0) => done(0) ... </k>
  rule <k> count(N:Int) => count(N -Int 1) ... </k> requires N >Int 0
  rule <k> spin() => spin() ... </k>
endmodule
module WEAK-CONTINUATION-SPEC
  imports WEAK-CONTINUATION
  claim [later-target]: <k> tick() </k> <n> 0 => ?M:Int </n> ensures ?M ==Int 1
  claim [partially-covered]: <k> tick() </k> <n> N:Int => ?M:Int </n>
    requires 0 <=Int N andBool N <=Int 1 ensures ?M ==Int 1
  claim [terminal-false]: <k> tick() </k> <n> 0 => ?M:Int </n> ensures ?M ==Int 2
  claim [countdown]: <k> count(N:Int) => done(0) </k> requires N >=Int 0
  claim [finite-countdown]: <k> count(3) => done(0) </k>
  claim [cycle]: <k> spin() => done(0) </k>
  claim [false-at-terminal]: <k> done(0) => done(1) </k>
endmodule
"#;
