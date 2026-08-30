module MACRO-RUNTIME
  imports INT

  syntax Input ::= Int | "twice" "(" Int ")" [macro]
  rule twice(I) => I +Int I

  configuration <k> $PGM:Input </k>
endmodule
