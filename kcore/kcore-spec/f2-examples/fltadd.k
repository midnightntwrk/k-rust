// FLOAT imported as a library module: a Float literal in a rule, Float below a sort of the
// definition (`Number ::= Int | Float`, as wasm's `Number`), and an addition whose result the
// kernel computes (IEEE 754 binary64, nearest ties to even).
module FLTADD-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  imports FLOAT-SYNTAX
  syntax Number ::= Int | Float
  syntax Cmd ::= add(Number, Number) [symbol(add)] | done(Number) [symbol(done)] | inc(Float) [symbol(inc)]
endmodule

module FLTADD
  imports FLTADD-SYNTAX
  imports INT
  imports BOOL
  imports FLOAT
  configuration <k> $PGM:Cmd </k>
  rule [add]: <k> add(X:Float, Y:Float) => done(X +Float Y) </k>
  rule [inc]: <k> inc(X) => add(X, 0.5) </k>
endmodule
