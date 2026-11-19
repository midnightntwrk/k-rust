module E6-ITE-K
  imports INT
  imports K-EQUAL
  syntax KItem ::= "go" [symbol(go)]
  syntax KItem ::= "a" [symbol(a)]
  syntax KItem ::= "b" [symbol(b)]
  rule <k> go => #if 1 <Int 2 #then a ~> b #else .K #fi </k>
endmodule
