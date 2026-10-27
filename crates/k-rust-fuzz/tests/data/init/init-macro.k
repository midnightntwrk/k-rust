// A mutant of the initializer pair (FZ-ENGINE-R4 fix round, D43(2)) whose grammar reads the
// program `go(0)` otherwise: it declares the keyword `0` of the sort `Zero` and the production
// `go(Zero)`, so the hole value 0 does not read back as the `Int` 0 on the mutant alone. The
// input is valid for the baseline, and the mutant refuses it before any run; the other values
// read back on both.

module INIT-SYNTAX
  imports INT-SYNTAX

  syntax Zero ::= "0"
  syntax Pgm ::= go(Int)  [symbol(go)]
               | go(Zero)  [symbol(goZero)]
endmodule

module INIT
  imports INIT-SYNTAX
  imports INT

  syntax Int ::= f(Pgm)  [function, symbol(f)]

  configuration <k> $PGM:Pgm </k>
                <x> f($PGM) </x>

  rule f(go(N)) => N
endmodule
