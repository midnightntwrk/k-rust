module E3-SETVAR-NONLINEAR-RHS
  syntax Exp ::= a() [symbol(a)] | b() [symbol(b)]
  syntax Exp ::= f(Exp, Exp) [function, symbol(f)]
  rule f(@S, @S) => @S
endmodule
