// Campaign regression: a mutant of d() can falsify the inherited total claim on f.
module SYMPARTIAL-SYNTAX
  imports INT-SYNTAX
  syntax Nat ::= "z" [symbol(z)] | s(Nat) [symbol(s)]
  syntax Address ::= addr(Int) [symbol(addr)]
  syntax Op ::= write(Address, Int) [symbol(write)]
              | load(Address, Int) [symbol(load)]
              | half(Nat) [symbol(half)]
  syntax Prog ::= "halt" [symbol(halt)]
                | seq(Op, Prog) [symbol(seq)]
endmodule

module SYMPARTIAL
  imports SYMPARTIAL-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  configuration <k> .K </k>

  syntax Int ::= f(Nat) [function, total, symbol(f)]
  rule f(z) => 10 /Int d()
  rule f(s(_)) => 20 /Int d()
  syntax Int ::= d() [function, total, symbol(d)]
  rule [d]: d() => 1

  rule [write]: seq(write(addr(A), V), P) => P
  rule [load]:  seq(load(addr(A), V), P) => P
  rule [half]:  seq(half(A), P) => P requires f(A) ==Int f(A) andBool d() ==Int 0
endmodule
