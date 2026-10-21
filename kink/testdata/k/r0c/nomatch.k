// Re-pin R0c-fix-3: the R0c-fix-2 review's probe review-probe2/nomatch.k, kept as written. Its
// guard edits fpos 0 -> -5 and fneg 0 -> 5 make fpos and fneg both apply to -1 (or 1) with
// different values, so the mutant has no model and is refused as inconsistent-mutant.
module NOMATCH-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= go(Int) [symbol(go)] | chk(Int) [symbol(chk)] | val(Int) [symbol(val)] | yes() [symbol(yes)]
  syntax Int ::= f(Int) [function, total, symbol(f)]
endmodule
module NOMATCH
  imports NOMATCH-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Prog </k>
  rule [fpos]: f(I) => 1 requires I >=Int 0
  rule [fneg]: f(I) => 2 requires I <Int 0
  rule [go]: <k> go(I) => val(f(I)) </k>
  rule [chk]: <k> chk(I) => yes() </k> requires f(I) >Int 0
endmodule
