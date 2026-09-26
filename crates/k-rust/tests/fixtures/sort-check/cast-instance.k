// A parametric production whose instances have different results, so a cast on an application
// decides which instance fits. `MInt{B}` and `MInt{C}` are incomparable instances above the
// argument sort `A`; only `MInt{B}` is below `Wide`, and both are below `Both`.
module CAST-INSTANCE-SYNTAX
  imports SORT-BOOL
  syntax Low ::= "low" [symbol(low)]
  syntax A ::= "a" [symbol(a)] | Low
  syntax B ::= A
  syntax C ::= A
  syntax T ::= "t" [symbol(t)]
  syntax R ::= A | T
  syntax MInt{A}
  syntax MInt{B}
  syntax MInt{C}
  syntax Wide ::= MInt{B}
  syntax Both ::= MInt{B} | MInt{C}
  syntax {S} S ::= id(S) [symbol(id)]
  syntax {S} MInt{S} ::= wrap(S) [symbol(wrap)]
  syntax Start ::= start(A) [symbol(start)]
endmodule

module CAST-INSTANCE
  imports CAST-INSTANCE-SYNTAX
  imports BASIC-K
  imports INT-SYNTAX
  configuration <k> .K </k>

  rule [holder]: start(Z:A) => .K
endmodule
