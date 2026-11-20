// #Floor of a disjunction of the two Bool values on a rule's left side (rule floor-bool-or-lhs):
// the operand may hold every element of Bool, where the #Floor is all of Bool, not empty.
module E3-ML-RULE-LHS-FLOOR-OR
  imports BOOL
  syntax Exp ::= b(Bool) [symbol(b)] | "done" [symbol(done)]
  rule [floor-bool-or-lhs]: <k> b(#Floor(true #Or false)) => done ... </k>
endmodule
