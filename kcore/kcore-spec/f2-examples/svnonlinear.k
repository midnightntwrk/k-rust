module E3-SETVAR-NONLINEAR
  syntax Exp ::= a() [symbol(a)] | b() [symbol(b)] | r() [symbol(r)]
  syntax Exp ::= f(Exp, Exp) [function, symbol(f)]
  rule f(@S, @S) => r()
endmodule
