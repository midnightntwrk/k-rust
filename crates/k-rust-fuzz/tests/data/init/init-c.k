// A mutant of the initializer pair (FZ-ENGINE-R4, final review N1) that declares a constructor
// the baseline lacks, `done`, and rewrites `go(N)` to it. Its end `<k> done(N) </k>` is data in
// the mutant and names a symbol the baseline does not declare, so it is none of the baseline's
// ends: an added end.

module INIT-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= go(Int)  [symbol(go)]
               | done(Int)  [symbol(done)]
endmodule

module INIT
  imports INIT-SYNTAX
  imports INT

  syntax Int ::= f(Pgm)  [function, symbol(f)]

  configuration <k> $PGM:Pgm </k>
                <x> f($PGM) </x>

  rule f(go(N)) => N
  rule f(done(N)) => N

  rule <k> go(N) => done(N) </k>
endmodule
