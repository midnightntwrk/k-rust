// The attribute anywhere on a rule of constructors.
module T221-ANYWHERE-RULE-REJECTED
  imports INT
  syntax Exp ::= a(Int) [symbol(a)] | b(Int) [symbol(b)]
  rule a(X) => b(X) [anywhere]
endmodule
