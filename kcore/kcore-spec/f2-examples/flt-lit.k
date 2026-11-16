// `flt.k` with a Float literal in a rule's right side. KCore represents no Float value, so the
// reader refuses the literal with a reason of its own (`floatLiteral`).
module FLT-LIT-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  imports FLOAT-SYNTAX
  syntax Val ::= fv(Float, Int) [symbol(fv)]
  syntax Cmd ::= zero() [symbol(zero)] | check(Val) [symbol(check)] | done(Bool) [symbol(done)]
endmodule

module FLT-LIT
  imports FLT-LIT-SYNTAX
  imports INT
  imports BOOL
  imports FLOAT
  configuration <k> $PGM:Cmd </k>
  rule [zero]: <k> zero() => check(fv(0.0, 1)) </k>
  rule [check]: <k> check(fv(F, _)) => done(isNaN(F)) </k>
endmodule
