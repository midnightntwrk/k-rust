// A clause whose closed `requires` holds an Int variable the arguments do not bind, as F1-DECISION
// 7.3's title: no value satisfies `1 ==Int 2 *Int H`, and Int being unconfined the text does not say
// that no element does. The clause is read; its `CondDecided` is owed and open
// (test/B1bClauses.lean).
module OPENH
  imports INT
  syntax Int ::= f() [function, symbol(f)]
  rule f() => 0 requires 1 ==Int 2 *Int H [unboundVariables(H)]
  syntax KItem ::= "go" [symbol(go)]
  rule <k> go => f() </k>
endmodule
