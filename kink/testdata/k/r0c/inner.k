// Re-pin R0c-fix-4 (R0c-fix-3 review minor 4): an inner pair of two declared functions would need
// a function symbol below the root of an equation's left-hand side (f(g(X)), where g's equation
// applies). k-rust refuses such a definition when it compiles it, so in a definition without an
// equation head (the regime where k-rust's check classifies no pair unless kink adds its probe
// head) every inner pair is a precondition row k-rust reports in either regime.
module INNER-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= go(Int) [symbol(go)] | val(Int) [symbol(val)]
  syntax Int ::= f(Int) [function, symbol(f)]
               | g(Int) [function, symbol(g)]
endmodule
module INNER
  imports INNER-SYNTAX
  imports INT
  configuration <k> $PGM:Prog </k>
  rule [fg]: f(g(X)) => X
  rule [g]: g(X) => X +Int 1
  rule [go]: <k> go(I) => val(f(g(I))) </k>
endmodule
