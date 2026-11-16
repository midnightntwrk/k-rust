module E3-ML-LHS-VALUE-SORT
  imports INT
  syntax Val ::= v() [symbol(v)]
  syntax Exp ::= a() [symbol(a)] | b() [symbol(b)] | c(Exp) [symbol(c)] | d() [symbol(d)] | e(Val) [symbol(e)]
               | p(Int) [symbol(p)] | q(Int) [symbol(q)]
  rule <k> c(#Exists Y:Val. a()) => b() ... </k>
  rule <k> e(_:Val) #Or d() => b() ... </k>
  rule <k> p(_:Int) #Or q(_:Int) => b() ... </k>
endmodule
