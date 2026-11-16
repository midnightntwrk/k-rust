module E2-MODULE-ATT
  imports E2-CONC
  imports E2-SYMB
  imports E2-HASK
endmodule
module E2-CONC [concrete]
  imports INT
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X
endmodule
module E2-SYMB [symbolic]
  imports INT
  syntax Int ::= g(Int) [function, symbol(g)]
  rule g(X) => X
endmodule
module E2-HASK [haskell]
  imports INT
  syntax Int ::= h(Int) [function, symbol(h)]
  rule h(X) => X
endmodule
