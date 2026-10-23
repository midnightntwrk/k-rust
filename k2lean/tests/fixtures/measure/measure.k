requires "domains.md"

module MEASURE-SYNTAX
  imports INT-SYNTAX
  syntax Fork ::= "A" | "B" | "C"
  syntax Pgm ::= run(Int)
endmodule

module MEASURE
  imports MEASURE-SYNTAX
  imports INT
  imports BOOL
  configuration <T> <k> $PGM:Pgm </k> </T>

  // counting down past a failed earlier equation (`owise` after `requires N <=Int 0`): the
  // measure comes from the negated guard
  syntax Int ::= sumTo(Int) [function, symbol(sumTo)]
  rule sumTo(N) => 0 requires N <=Int 0
  rule sumTo(N) => N +Int sumTo(N -Int 1) [owise]

  // a chain of constructors, each falling back to the previous one: a rank of `Fork`
  syntax Int ::= fee(Fork) [function, total, symbol(fee)]
  rule fee(A) => 1
  rule fee(B) => fee(A) +Int 1
  rule fee(C) => fee(B) *Int 2

  // no measure: the rewriting diverges at 6 and 7 (6 => 7 => 6), so the termination file makes
  // it the least fixed point of its equations (`none` there)
  syntax Int ::= norm(Int) [function, symbol(norm)]
  rule norm(N) => norm(N +Int 1) requires N ==Int 6
  rule norm(N) => norm(N -Int 1) requires N ==Int 7
  rule norm(N) => N requires N =/=Int 6 andBool N =/=Int 7

  rule <k> run(N) => sumTo(N) +Int fee(C) +Int norm(N) </k>
endmodule
