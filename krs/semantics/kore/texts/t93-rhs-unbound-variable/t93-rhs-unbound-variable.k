// A rewrite rule whose right side holds a variable that its left side does not bind and that is
// not written as an existential (?Y).
module T93-RHS-UNBOUND-VARIABLE
  imports INT
  syntax Exp ::= a(Int) | b(Int)
  rule <k> a(X) => b(Y) ... </k> requires X >Int 0
endmodule
