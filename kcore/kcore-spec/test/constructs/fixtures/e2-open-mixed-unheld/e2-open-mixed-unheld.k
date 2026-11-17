module E2-OPEN-MIXED-UNHELD
  syntax A ::= "x" [symbol(x)] | "y" [symbol(y)]
  syntax B ::= A "&" A [comm, symbol(and)]
  syntax KItem ::= c(B) [symbol(c)] | d(A) [symbol(d)] | e() [symbol(e)] | g(A) [symbol(g)]
  rule <k> c(_:B) #Or e() => d(x) ... </k>
  rule <k> g(#Exists Z:B. x) => d(y) ... </k>
endmodule
