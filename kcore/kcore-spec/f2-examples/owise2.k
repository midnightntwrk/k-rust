// Two `[owise]` equations of one function. Each `[owise]` premise negates the two other
// equations (not the other `[owise]` equation): both are clauses of priority 200, unordered
// between themselves, after the two others. They overlap at f(1, 1) and agree there.
module OWISE2-SYNTAX
  imports INT-SYNTAX
  syntax Int ::= f(Int, Int) [function, symbol(f)]
  syntax Cmd ::= run(Int, Int) [symbol(run)] | done(Int) [symbol(done)]
endmodule

module OWISE2
  imports OWISE2-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Cmd </k>
  rule f(0, _) => 0
  rule f(_, 0) => 1
  rule f(1, Y) => Y [owise]
  rule f(X, 1) => X [owise]
  rule [go]: <k> run(X, Y) => done(f(X, Y)) </k>
endmodule
