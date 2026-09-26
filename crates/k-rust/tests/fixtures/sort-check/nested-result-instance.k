// A parameter nested two levels inside the result. `MInt{MInt{B}}` is the one declared instance
// of `MInt{MInt{W}}`; `MInt{A}` is below `MInt{B}`, but `MInt{MInt{A}}` is not declared.
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
