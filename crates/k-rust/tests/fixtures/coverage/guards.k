// The guard shapes of `guard_outcomes.rs`: complementary rewrite rules over a short-circuit
// conjunction, and a function with a conditional equation, a conditional `owise` equation and an
// unconditional one.
module GUARDS-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Pgm ::= go(Int, Int) [symbol(go)]
               | call(Int)    [symbol(call)]
endmodule

module GUARDS
  imports GUARDS-SYNTAX
  imports INT
  imports BOOL
  syntax KItem ::= done(Int) | other(Int)
  syntax Int ::= sign(Int) [function, symbol(sign)]
  rule [positive]: sign(X) => 1 requires X >Int 0
  rule [rest]: sign(X) => 0 requires X >=Int -100 [owise]
  rule [far]: sign(_) => -1 [owise]

  configuration <T> <k> $PGM:Pgm </k> </T>

  rule [both]: <k> go(X, Y) => done(X) ... </k> requires X ==Int 0 andThenBool Y ==Int 0
  rule [notboth]: <k> go(X, Y) => other(X) ... </k> requires notBool (X ==Int 0 andThenBool Y ==Int 0)
  rule [callsign]: <k> call(X) => done(sign(X)) ... </k>
endmodule
