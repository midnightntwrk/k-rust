// K's FLOAT module imported: kompile writes its 44 sentences (38 hooked symbols, 3 other function
// symbols and their 3 equations) with the K installation's domains.md as `Source`. The library
// holds FLOAT-SYNTAX (the sort Float) and not FLOAT; the reader recognises FLOAT's sentences by
// content and reads them as the definition's own: its hooked symbols as parameters (`isNaN`,
// declared total, among the parameters the statements' interpretations are total on; `<Float`
// not), `isInfinite` as a total function with its equation. Float is a constructor's argument
// sort; no Float literal is written.
module FLT-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  imports FLOAT-SYNTAX
  syntax Val ::= fv(Float, Int) [symbol(fv)]
  syntax Cmd ::= check(Val) [symbol(check)] | done(Bool) [symbol(done)]
endmodule

module FLT
  imports FLT-SYNTAX
  imports INT
  imports BOOL
  imports FLOAT
  configuration <k> $PGM:Cmd </k>
  rule [check]: <k> check(fv(F, _)) => done(isNaN(F) orBool isInfinite(F)) </k>
endmodule
