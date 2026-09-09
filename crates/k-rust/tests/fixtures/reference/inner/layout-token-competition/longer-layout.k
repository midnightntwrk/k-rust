module FE14-SYNTAX
  syntax #Layout ::= r"ab"
  syntax Start ::= "a" [symbol(token)]
endmodule

module FE14
  imports FE14-SYNTAX
  configuration <k> $PGM:Start </k>
endmodule
