// FLOAT, STRING, BYTES and SET imported, for test/LibProbe.lean's probe of the library's sentences
// over Float, String and Bytes values (a Float value of a format with a field of 1 among them).
// A rule applies `isInfinite` (FLOAT's function with one equation), `substrString`, `Int2Bytes` and
// `<=Set`; no Float literal is written.
module SILENTFLT-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  imports FLOAT-SYNTAX
  imports STRING-SYNTAX
  imports BYTES-SYNTAX
  imports SET
  syntax Val ::= fv(Float, String, Set) [symbol(fv)]
  syntax Cmd ::= check(Val) [symbol(check)] | done(Bool, String, Bytes, Bool) [symbol(done)]
endmodule

module SILENTFLT
  imports SILENTFLT-SYNTAX
  imports INT
  imports BOOL
  imports FLOAT
  imports STRING
  imports BYTES
  configuration <k> $PGM:Cmd </k>
  rule [check]: <k> check(fv(F, S, X)) => done(isInfinite(F), substrString(S, 0, 1), Int2Bytes(1, 0, BE), X <=Set X) </k>
endmodule
