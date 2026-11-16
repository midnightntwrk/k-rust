module E2-SYM-CONCRETE
  imports INT
  syntax Int ::= fc(Int) [function, concrete, symbol(fc)] | fs(Int) [function, symbolic, symbol(fs)]
  rule fc(X) => X
  rule fs(X) => X
endmodule
