module FE14-SYNTAX
  syntax #Layout ::= r"a"
  syntax Start ::= "ab" [symbol(token)]
endmodule

module FE14
  imports FE14-SYNTAX
  configuration <k> $PGM:Start </k>
endmodule
