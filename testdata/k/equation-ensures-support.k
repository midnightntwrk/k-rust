module EQSUPPORT-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= "halt" [symbol(halt)] | step(Int) [symbol(step)]
endmodule

module EQSUPPORT
  imports EQSUPPORT-SYNTAX
  imports BASIC-K
  imports INT
  imports BOOL
  configuration <k> .K </k>

  syntax Int ::= f(Int) [function, symbol(f)]
  rule [f]: f(I) => 1 ensures d(I) >Int 0
  syntax Int ::= d(Int) [function, symbol(d)]
  rule [d]: d(I) => 1
  syntax Int ::= g(Int) [function, symbol(g)]
  rule [g]: g(I) => 1

  rule [step]: step(I) => halt ensures I >Int 0
endmodule
