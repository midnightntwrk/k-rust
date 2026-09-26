// Parametric productions whose parameter occurs only in the result, or is the result. The
// parameter values `A` and `B` are unrelated, but the instance `MInt{A}` is declared below
// `MInt{B}`; `MInt{C}` and `MInt{D}` are incomparable instances.
module RESULT-INSTANCE-SYNTAX
  imports SORT-BOOL
  syntax A
  syntax B
  syntax C
  syntax D
  syntax MInt{A} ::= "ka" [symbol(ka)]
  syntax MInt{B} ::= "kb" [symbol(kb)]
  syntax MInt{C}
  syntax MInt{D}
  syntax MInt{B} ::= MInt{A}
  syntax Wide ::= MInt{B}
  syntax Narrow ::= MInt{A}
  syntax Pair ::= MInt{C} | MInt{D}
  syntax {W} MInt{W} ::= "mk" [symbol(mk)]
  syntax {W, V} MInt{V} ::= mk2(MInt{W}) [symbol(mk2)]
  syntax {T} T ::= inner(MInt{T}) [symbol(inner)]
  syntax {S} S ::= wrap(S) [symbol(wrap)]
  syntax Start ::= "start" [symbol(start)]
endmodule

module RESULT-INSTANCE
  imports RESULT-INSTANCE-SYNTAX
  imports BASIC-K
  imports INT-SYNTAX
  configuration <k> .K </k>

  rule [holder]: start => .K
endmodule
