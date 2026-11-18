// Matching-logic connectives at a term position of a rule's side: #Top and #Or on a right side, #Not and #Implies under a constructor on a left side.
module T233-RULE-CONN-CUT
  syntax Exp ::= a() [symbol(a)] | b() [symbol(b)] | c(Exp) [symbol(c)] | e(Exp) [symbol(e)]
  syntax Exp ::= "go" [symbol(go)] | "go2" [symbol(go2)] | "done" [symbol(done)]
  rule <k> go => #Top ... </k>
  rule <k> go2 => a() #Or b() ... </k>
  rule <k> c(#Not(a())) => done ... </k>
  rule <k> e(a() #Implies b()) => done ... </k>
endmodule
