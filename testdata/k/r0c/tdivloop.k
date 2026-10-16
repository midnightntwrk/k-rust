// Re-pin R0c-fix-1 deliverable 1 (R0c review 1 major 1, the reviewer's probe): on both(0) the
// mutant tdeq 1 -> 0 takes an undefined step that contradicts td's total claim and spins until
// the time bound; tdiv(1) distinguishes it from the baseline.
module TDIVLOOP-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= tdiv(Int) [symbol(tdiv)]
                | both(Int) [symbol(both)]
                | spin(Int, Int) [symbol(spin)]
                | val(Int) [symbol(val)]
                | done(Int) [symbol(done)]
  syntax Int ::= td(Int) [function, total, symbol(td)]
endmodule
module TDIVLOOP
  imports TDIVLOOP-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Prog </k>
  rule [tdeq]: td(I) => 10 /Int (I +Int 1)
  rule [tdiv]: <k> tdiv(I) => val(td(I)) </k>
  rule [botha]: <k> both(I) => tdiv(I) </k>
  rule [bothb]: <k> both(I) => spin(td(I +Int 1), 0) </k>
  rule [spin]: <k> spin(10, N) => spin(10, N +Int 1) </k>
  rule [stop]: <k> spin(5, N) => done(N) </k>
endmodule
