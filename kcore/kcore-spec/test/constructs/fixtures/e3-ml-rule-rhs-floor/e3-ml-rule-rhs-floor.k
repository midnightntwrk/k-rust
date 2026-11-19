// #Floor on a rule's right side, in a term position: of a term over Int (rule floor-int) and of a
// term over Bool (rule floor-bool).
module E3-ML-RULE-RHS-FLOOR
  imports INT
  imports BOOL
  syntax Exp ::= go(Int) [symbol(go)] | b(Bool) [symbol(b)]
  rule [floor-int]:  <k> go(X) => go(#Floor(X)) ... </k>
  rule [floor-bool]: <k> b(B) => b(#Floor(B)) ... </k>
endmodule
