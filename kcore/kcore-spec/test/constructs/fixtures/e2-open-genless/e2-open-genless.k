module E2-OPEN-GENLESS
  imports BOOL
  syntax Empty
  syntax S ::= mk(Empty) [symbol(mk)] | k() [symbol(k)]
  syntax Exp ::= a() [symbol(a)] | b() [symbol(b)] | c() [symbol(c)]
  syntax Bool ::= isMk(S) [function, total, symbol(isMk)]
  rule isMk(mk(_)) => true
  rule isMk(k()) => false
  rule <k> a() => b() ... </k> requires isMk(X:S) [unboundVariables(X)]
  rule <k> a() => c() ... </k> [owise]
endmodule
