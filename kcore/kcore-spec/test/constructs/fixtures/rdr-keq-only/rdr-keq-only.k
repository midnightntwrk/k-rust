// A text that imports K-EQUAL-SYNTAX (which declares _==K_) and not the module holding its
// sentence ((K1 ==K K2) = true) = (K1 = K2); a rule's requires is a conjunction #And.
module RDR-KEQ-ONLY
  imports K-EQUAL-SYNTAX
  imports BOOL-SYNTAX
  syntax Cmd ::= go(Bool) [symbol(go)] | "done" [symbol(done)]
  configuration <k> $PGM:Cmd </k>
  rule <k> go(B) => done </k> requires B #And true
endmodule
