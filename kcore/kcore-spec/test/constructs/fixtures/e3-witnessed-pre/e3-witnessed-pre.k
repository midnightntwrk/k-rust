module E3-WITNESSED-PRE
  imports INT
  imports BOOL
  syntax Empty
  syntax S ::= "a" [symbol(a)] | c(Empty) [symbol(c)] | "d" [symbol(d)]
  syntax Bool ::= isC(S) [function, total, symbol(isC)]
  rule isC(c(_)) => true
  rule isC(d) => true
  rule isC(a) => false
  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(_) => 1 requires isC(H:S #And d) [unboundVariables(H)]
  syntax KItem ::= "go" [symbol(go)]
  rule <k> go => f(0) </k>
endmodule
