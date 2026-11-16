module E3-ML-LHS-MIXED-SORT
  syntax Empty
  syntax Val ::= v() [symbol(v)]
  syntax Exp ::= b() [symbol(b)] | e(Val) [symbol(e)] | f(Empty) [symbol(f)]
  rule <k> e(_:Val) #Or f(_:Empty) => b() ... </k>
endmodule
