// Trusted claims and their support (kink-patch ClaimSupport).
// f's equations mention d, so f's claims rest on d's equations; g stands apart.
// inc is partial. step and go carry preserves-definedness; lemma mentions f, glemma only g.
module CLAIMS-SYNTAX
  imports INT-SYNTAX
  syntax Nat ::= "z" [symbol(z)] | s(Nat) [symbol(s)]
  syntax Prog ::= "halt" [symbol(halt)]
                | step(Nat, Prog) [symbol(step)]
                | go(Int, Prog) [symbol(go)]
endmodule

module CLAIMS
  imports CLAIMS-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  configuration <k> .K </k>

  syntax Int ::= f(Nat) [function, total, symbol(f)]
  rule [f-z]: f(z) => 10 /Int d()
  rule [f-s]: f(s(_)) => 20 /Int d()
  syntax Int ::= d() [function, total, symbol(d)]
  rule [d]: d() => 1
  syntax Int ::= g(Int) [function, total, symbol(g)]
  rule [g]: g(X) => X +Int 1
  syntax Int ::= inc(Int) [function, symbol(inc)]
  rule [inc]: inc(X) => X +Int 1

  rule [lemma]: f(X) +Int 0 => f(X) [simplification]
  rule [glemma]: g(X) +Int 0 => g(X) [simplification]

  rule [step]: step(N, P) => P requires f(N) ==Int f(N) [preserves-definedness]
  rule [go]:   go(I, P) => P requires g(I) >Int 0 [preserves-definedness]
endmodule
