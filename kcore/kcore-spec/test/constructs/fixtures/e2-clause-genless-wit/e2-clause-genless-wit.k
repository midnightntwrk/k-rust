module E2-CLAUSE-GENLESS-WIT
  imports INT
  imports BOOL
  syntax Empty
  syntax S ::= "a" [symbol(a)] | c(Empty) [symbol(c)] | "d" [symbol(d)]
  syntax Bool ::= isC(S) [function, total, symbol(isC)]
  rule isC(c(_)) => true
  rule isC(d) => true
  rule isC(_) => false [owise]
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(_) => 1 requires isC(H:S) [unboundVariables(H)]
  rule f(_) => 0 [owise]
  syntax KItem ::= "go" [symbol(go)]
  rule <k> go => f(0) </k>
endmodule
