module LAYOUT-TOKEN-COMPETITION-SYNTAX
  syntax #Layout ::= r"[ab]"
  syntax Start ::= List{Item,","} [symbol(items)]
  syntax Item ::= "x" [symbol(item)]
  syntax Other ::= "ab" [symbol(other)]
endmodule

module LAYOUT-TOKEN-COMPETITION
  imports LAYOUT-TOKEN-COMPETITION-SYNTAX
  configuration <k> $PGM:Start </k>
endmodule
