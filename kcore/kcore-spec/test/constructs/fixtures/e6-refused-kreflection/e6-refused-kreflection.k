// The sort-parametric hooked function #unparseKORE of K-REFLECTION (domains.md) applied once, at
// the instance Int, in a rule labelled with the hook's name. K-IO is imported because K-REFLECTION
// declares a production of K-IO's sort IOError.
module E6-REFUSED-KREFLECTION
  imports K-REFLECTION
  imports K-IO
  imports INT
  syntax KItem ::= go(Int) [symbol(go)]
  rule [kreflection-printKORE]: <k> go(1) ~> X:Int => #unparseKORE(X) ... </k>
endmodule
