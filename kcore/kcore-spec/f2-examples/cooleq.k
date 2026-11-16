module E2-COOL-EQ
  imports INT
  syntax KResult ::= Int
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X [cool]
  rule f(f(X)) => f(X) [simplification, cool]
endmodule
