// Baseline of the initializer pair (FZ-ENGINE-R4, final review S1). The configuration's <x> cell
// is initialized by the function `f` of the program: `go(N)` gives `N`. No rule rewrites
// `go(N)`, so every run stops at once, with `N` in <x>.

module INIT-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= go(Int)  [symbol(go)]
endmodule

module INIT
  imports INIT-SYNTAX
  imports INT

  syntax Int ::= f(Pgm)  [function, symbol(f)]

  configuration <k> $PGM:Pgm </k>
                <x> f($PGM) </x>

  rule f(go(N)) => N
endmodule
