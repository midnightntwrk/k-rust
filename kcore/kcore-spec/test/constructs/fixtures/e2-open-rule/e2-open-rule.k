module E2-OPEN-RULE
  imports BOOL
  imports K-EQUAL
  syntax Exp ::= "x" [symbol(x)] | "y" [symbol(y)] | Exp "&" Exp [comm, symbol(and)]
  syntax KItem ::= "go" [symbol(go)]
  syntax Bool ::= same(Exp, Exp) [function, symbol(same)]
  rule same(A, B) => A ==K B
  rule <k> go => x & y </k>
endmodule
