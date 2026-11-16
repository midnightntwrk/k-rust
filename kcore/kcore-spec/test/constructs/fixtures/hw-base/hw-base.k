// The base of the hand-written H-shape fixtures (hw-h1-*, hw-h8, hw-h12-*): constructors a, b, run,
// done, functions f, g, w (w with no equation), get over MAP, and a rule [go].
module HW-BASE-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  imports MAP
  syntax Exp ::= a(Int) [symbol(a)] | b(Int) [symbol(b)]
  syntax Exp ::= f(Int) [function, symbol(f)]
  syntax Int ::= g(Int) [function, symbol(g)] | w() [function, symbol(w)]
  syntax Int ::= get(Map) [function, symbol(get)]
  syntax Cmd ::= run(Int) [symbol(run)] | done(Int) [symbol(done)]
endmodule

module HW-BASE
  imports HW-BASE-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Cmd </k>
  rule f(X) => a(X)
  rule g(0) => 0
  rule get(M) => {M[1]}:>Int
  rule [go]: <k> run(N) => done(g(N)) </k>
endmodule
