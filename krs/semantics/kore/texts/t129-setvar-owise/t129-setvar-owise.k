module T129-SETVAR-OWISE
  syntax Exp ::= a() [symbol(a)] | b() [symbol(b)] | one() [symbol(one)] | two() [symbol(two)]
  syntax Exp ::= f(Exp, Exp) [function, symbol(f)]
  rule f(@S, @S) => one()
  rule f(_, _) => two() [owise]
endmodule
