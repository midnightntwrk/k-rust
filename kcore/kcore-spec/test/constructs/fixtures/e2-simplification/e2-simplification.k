module E2-SIMPLIFICATION
  imports INT
  imports BOOL
  syntax Int ::= f(Int) [function, symbol(f)] | g(Int, Int) [function, comm, symbol(g)]
               | sl(Int) [function, smtlib(sl), symbol(sl)]
  rule f(X) => X
  rule g(X, Y) => X +Int Y
  rule sl(X) => X
  rule [s-label]: f(f(X)) => f(X) [simplification]
  rule f(X) +Int 0 => f(X) [simplification(10)]
  rule f(X) +Int 1 => X +Int 1 [simplification(50)]
  rule f(X) +Int 2 => X +Int 2 [simplification(200)]
  rule f(X) +Int 3 => X +Int 3 [simplification(300)]
  rule f(X) *Int 0 => 0 [simplification, concrete]
  rule f(X) *Int 1 => f(X) [simplification, symbolic]
  rule f(X) *Int Y => Y *Int f(X) [simplification, concrete(Y), symbolic(X)]
  rule g(X, Y) => g(Y, X) [simplification, comm]
  rule f(X) -Int 0 => f(X) [simplification, preserves-definedness]
  rule sl(X) >=Int 0 => true [simplification, smt-lemma]
  rule f(X) -Int 1 => X [simplification, non-executable]
  rule f(g(X, Y)) => g(X, Y) [simplification, syntactic(1)]
endmodule
