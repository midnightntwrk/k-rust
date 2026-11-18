module E6-ITE-INT
  imports STRING
  imports INT
  imports K-EQUAL
  syntax KItem ::= "go" [symbol(go)]
  syntax KItem ::= res(Int) [symbol(res)]
  rule <k> go => res(#if 1 <Int 2 #then 3 #else 4 #fi) </k>
endmodule
