// The specification of kink-flow's narrowing tests (tests/mutation.rs, tests/search.rs): the
// equations and lemmas a mutation replaces by an instance of itself, beside the constructs the
// instance test fails closed on (a function in the substitution, a macro, a variable written
// without its sort, a `concrete` lemma, a wildcard met by anything but itself) and a rewrite
// rule, which a narrowing does not weaken.
module NARROW-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  imports BASIC-K
  syntax Nat ::= "zero" [symbol(zero)] | s(Nat) [symbol(s)]
  syntax Val ::= v(Int) [symbol(v)]
  syntax Prog ::= run(Nat) [symbol(run)]
  syntax Nat ::= plus(Nat, Nat) [function, total, symbol(plus)]
  syntax Val ::= q(Int, Int) [function, symbol(q)]
  syntax Val ::= g(Nat) [function, symbol(g)]
  syntax Val ::= k(KItem) [function, symbol(k)]
  syntax Val ::= t(Int) [function, symbol(t)]
  syntax Int ::= twice(Int) [macro, symbol(twice)]
  syntax Val ::= f(Int) [function, symbol(f)]
  syntax Int ::= w(Int) [function, total, symbol(w)]
  syntax Val ::= h(KItem) [function, symbol(h)]
  syntax Val ::= hp(KItem, Nat) [function, symbol(hp)]
  syntax Val ::= hn(KItem) [function, symbol(hn)]
  syntax Int ::= hz(KItem) [function, total, symbol(hz)]
endmodule

module NARROW
  imports NARROW-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Prog </k>
  rule [run]: <k> run(N:Nat) => plus(N:Nat, zero) </k>
  rule [plus-zero]: plus(zero, N:Nat) => N:Nat
  rule [plus-succ]: plus(s(M:Nat), N:Nat) => s(plus(M:Nat, N:Nat))
  rule [q-def]: q(I:Int, J:Int) => v(I:Int +Int J:Int) requires I:Int >Int 0
  rule [g-succ]: g(s(N:Nat)) => v(1)
  rule [g-else]: g(N:Nat) => v(0) [owise]
  rule [k-def]: k(X:KItem) => v(0)
  rule [twice-def]: twice(I) => I *Int 2
  rule [t-def]: t(I:Int) => v(twice(I:Int))
  rule [f-def]: f(I) => v(I) requires I >Int 0
  rule [w-def]: w(I) => I +Int 1
  rule [w-zero]: w(I:Int) +Int 0 => w(I:Int) [simplification]
  rule [w-one]: w(I:Int) *Int 1 => w(I:Int) [simplification, concrete(I)]
  rule [h-nat]: h(_:Nat) => v(1)
  rule [h-bool]: h(_:Bool) => v(2)
  rule [hp-def]: hp(_:Nat, N:Nat) => v(0)
  rule [hn-def]: hn(_X:Nat) => v(1)
  rule [hz-nat]: hz(_:Nat) >=Int 0 => true [simplification]
endmodule
