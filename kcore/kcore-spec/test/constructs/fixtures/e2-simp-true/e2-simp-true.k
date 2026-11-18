module E2-SIMP-TRUE
  imports INT
  syntax Int ::= f(Int) [function, symbol(f)]
               | sl(Int) [function, smtlib(sl), symbol(sl)]
  rule f(X) => X
  rule sl(X) => X
  rule f(f(X)) => f(X) [simplification, non-executable]
  rule sl(sl(X)) => sl(X) [simplification, smt-lemma]
endmodule
