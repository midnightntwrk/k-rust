module LAYOUT-TOKEN-COMPETITION-SYNTAX
  syntax #Layout ::= r"ab"
  syntax Start ::= "a" [symbol(token)]
endmodule

module LAYOUT-TOKEN-COMPETITION
  imports LAYOUT-TOKEN-COMPETITION-SYNTAX
  configuration <k> $PGM:Start </k>
endmodule
