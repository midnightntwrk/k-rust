// Re-pin R0c-fix-3: drop-owise and the mutant consistency check. Dropping `owise` from fother
// puts f(_) => 2 in f(0) => 1's priority group, where both apply to 0 with different values: the
// mutant has no model and is refused. Dropping it from gother puts g(_) => 1 beside g(0) => 1,
// which agree on 0: the pair joins and the mutant runs.
module OWISE-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= go(Int) [symbol(go)] | val(Int) [symbol(val)]
  syntax Int ::= f(Int) [function, total, symbol(f)]
               | g(Int) [function, total, symbol(g)]
endmodule
module OWISE
  imports OWISE-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Prog </k>
  rule [fzero]: f(0) => 1
  rule [fother]: f(_) => 2 [owise]
  rule [gzero]: g(0) => 1
  rule [gother]: g(_) => 1 [owise]
  rule [go]: <k> go(I) => val(f(I) +Int g(I)) </k>
endmodule
