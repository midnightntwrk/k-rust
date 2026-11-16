// A library parameter symbol applied only in a function equation's `ensures`: `randInt` (INT's
// `INT.rand`, which no hook of the registry interprets) in `f(X) => X ensures randInt(X) >=Int 0`.
module ENSPARAM-SYNTAX
  imports INT-SYNTAX
  syntax Int ::= f(Int) [function, symbol(f)]
  syntax Cmd ::= run(Int) [symbol(run)] | done(Int) [symbol(done)]
endmodule

module ENSPARAM
  imports ENSPARAM-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Cmd </k>
  rule f(X) => X ensures randInt(X) >=Int 0
  rule [go]: <k> run(N) => done(f(N)) </k>
endmodule
