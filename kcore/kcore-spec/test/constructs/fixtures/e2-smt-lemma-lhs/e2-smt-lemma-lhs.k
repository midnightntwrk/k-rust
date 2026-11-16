module E2-SMT-LEMMA-LHS
  imports INT
  imports BOOL
  syntax Int ::= sl(Int) [function, smtlib(sl), symbol(sl)]
  rule sl(X) => X
  rule sl(X) >=Int 0 => true [smt-lemma]
endmodule
