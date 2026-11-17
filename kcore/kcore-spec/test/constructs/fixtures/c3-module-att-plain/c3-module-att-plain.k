module C3-MODULE-ATT-PLAIN
  imports E2-CONC
  imports E2-SYMB
  imports E2-HASK
endmodule
module E2-CONC
  imports INT
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X
endmodule
module E2-SYMB
  imports INT
  syntax Int ::= g(Int) [function, symbol(g)]
  rule g(X) => X
endmodule
module E2-HASK
  imports INT
  syntax Int ::= h(Int) [function, symbol(h)]
  rule h(X) => X
endmodule
