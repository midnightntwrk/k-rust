module E7-CONSTFOLD
  imports INT
  imports STRING
  syntax Exp ::= a() [symbol(a)] | b(Int) [symbol(b)] | c(String) [symbol(c)]
  rule <k> a() => b(1 +Int 2 *Int 3) ... </k>
  rule <k> b(X) => c("x" +String "y") ... </k> requires X >Int 2 +Int 2
endmodule
