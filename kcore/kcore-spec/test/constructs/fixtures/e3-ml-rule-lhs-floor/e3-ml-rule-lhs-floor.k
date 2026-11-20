// #Floor of a term over Bool on a rule's left side, in a term position (rule floor-bool-lhs).
module E3-ML-RULE-LHS-FLOOR
  imports BOOL
  syntax Exp ::= b(Bool) [symbol(b)] | "done" [symbol(done)]
  rule [floor-bool-lhs]: <k> b(#Floor(_:Bool)) => done ... </k>
endmodule
