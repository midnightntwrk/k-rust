// A text that imports K-EQUAL-SYNTAX (which declares _==K_) and not the module holding its
// sentence ((K1 ==K K2) = true) = (K1 = K2); an equation's requires is a conjunction #And.
module RDR-KEQ-ONLY-EQN
  imports K-EQUAL-SYNTAX
  imports BOOL-SYNTAX
  syntax Bool ::= f(Bool) [function, symbol(f)]
  rule f(B) => true requires B #And true
endmodule
