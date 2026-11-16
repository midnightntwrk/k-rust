module E3-FUN-NOREWRITE
  imports INT
  syntax Exp ::= a(Int) [symbol(a)] | c(Int) [symbol(c)]
  rule <k> c(X) => #fun(a(_))(a(X)) ... </k>
endmodule
