module T16-MATCH-INJ
  imports INT
  syntax A ::= a(Int) [symbol(a)]
  syntax B ::= A | b(Int) [symbol(b)]
  syntax C ::= B
  syntax Int ::= f(C) [function, symbol(f)]
               | g(C) [function, symbol(g)]
  rule f(_:A) => 1
  rule f(b(_)) => 2
  rule g(_:B) => 3
endmodule
