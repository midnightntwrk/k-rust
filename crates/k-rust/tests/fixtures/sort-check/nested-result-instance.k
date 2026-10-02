// A definition the sort checks reject, because it has nested parametric sorts: the declaration
// `MInt{MInt{B}}` and the production result `MInt{MInt{W}}` apply `MInt` to an argument that has
// arguments itself.
module NESTED-RESULT-INSTANCE-SYNTAX
  imports SORT-BOOL
  syntax A
  syntax B
  syntax MInt{A}
  syntax MInt{B}
  syntax MInt{B} ::= MInt{A}
  syntax MInt{MInt{B}}
  syntax {W} MInt{MInt{W}} ::= "mkn" [symbol(mkn)]
  syntax Start ::= "start" [symbol(start)]
endmodule

module NESTED-RESULT-INSTANCE
  imports NESTED-RESULT-INSTANCE-SYNTAX
  imports BASIC-K
  imports INT-SYNTAX
  configuration <k> .K </k>

  rule [holder]: start => .K
endmodule
