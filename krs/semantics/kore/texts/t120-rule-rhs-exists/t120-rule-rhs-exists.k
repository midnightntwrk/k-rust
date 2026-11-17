module T120-RULE-RHS-EXISTS
  imports INT
  syntax Exp ::= a(Int) [symbol(a)] | d(Int) [symbol(d)]
  rule <k> a(X) => d(?Y:Int) ... </k> ensures ?Y >Int X
endmodule
