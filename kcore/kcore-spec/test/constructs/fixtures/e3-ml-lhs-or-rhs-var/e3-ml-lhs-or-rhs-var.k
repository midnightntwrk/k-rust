module E3-ML-LHS-OR-RHS-VAR
  syntax Val ::= v() [symbol(v)]
  syntax Exp ::= d() [symbol(d)] | e(Val) [symbol(e)] | r(Val) [symbol(r)]
  rule <k> e(X:Val) #Or d() => r(X) ... </k>
endmodule
