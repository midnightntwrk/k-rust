module C3-SYM-ATTR-BASE
  imports INT
  syntax Int ::= fc(Int) [function, symbol(fc)] | fs(Int) [function, symbol(fs)]
  rule fc(X) => X
  rule fs(X) => X
endmodule
