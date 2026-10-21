// Re-pin R0c-fix-4 (R0c-fix-3 review critical 2, the reviewer's cfgf.k): nomatch.k with f's
// equations written with configuration context, [[ F ]] C, which k-rust loads as #withConfig(F, C)
// and compiles to equations of f.
module CFGF-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= go(Int) [symbol(go)] | chk(Int) [symbol(chk)] | val(Int) [symbol(val)] | yes() [symbol(yes)]
  syntax Int ::= f(Int) [function, total, symbol(f)]
endmodule
module CFGF
  imports CFGF-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Prog </k>
  rule [fpos]: [[ f(I) => 1 ]] <k> _ </k> requires I >=Int 0
  rule [fneg]: [[ f(I) => 2 ]] <k> _ </k> requires I <Int 0
  rule [go]: <k> go(I) => val(f(I)) </k>
  rule [chk]: <k> chk(I) => yes() </k> requires f(I) >Int 0
endmodule
