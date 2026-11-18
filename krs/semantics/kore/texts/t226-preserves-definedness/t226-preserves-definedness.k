// The attribute preserves-definedness on a rewrite rule.
module T226-PRESERVES-DEFINEDNESS
  imports INT
  syntax Exp ::= Int | b(Int) [symbol(b)] | c(Int) [symbol(c)]
  rule <k> c(X) => b(X) ... </k> [preserves-definedness]
endmodule
