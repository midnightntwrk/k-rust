module FE14-SYNTAX
  syntax #Layout ::= r"[ab]"
  syntax Start ::= List{Item,","} [symbol(items)]
  syntax Item ::= "x" [symbol(item)]
  syntax Other ::= "ab" [symbol(other)]
endmodule

module FE14
  imports FE14-SYNTAX
  configuration <k> $PGM:Start </k>
endmodule
