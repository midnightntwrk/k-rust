module E2-SMT-LEMMA
  imports INT
  syntax Int ::= sl(Int) [function, smtlib(sl), symbol(sl)]
  rule sl(X) => X [smt-lemma]
endmodule
