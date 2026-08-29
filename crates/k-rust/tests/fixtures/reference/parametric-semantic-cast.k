module PARAMETRIC-SEMANTIC-CAST
  syntax A ::= "a" [symbol(a)]
  syntax B ::= "b" [symbol(b)]
  syntax C ::= A | B
  syntax D ::= A | B
  syntax {S} S ::= "pair(" S "," S ")" [symbol(pair)]

  rule pair(a,b):C => pair(a,b):C
endmodule
