// Re-pin R0c-fix-1 deliverable 1: tdivloop.k with tdeq's 1 replaced by 0 (the campaign's
// mutant), compiled on its own so that a test can read the timed-out run's leaves.
module TDIVLOOPM-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= tdiv(Int) [symbol(tdiv)]
                | both(Int) [symbol(both)]
                | spin(Int, Int) [symbol(spin)]
                | val(Int) [symbol(val)]
                | done(Int) [symbol(done)]
  syntax Int ::= td(Int) [function, total, symbol(td)]
endmodule
module TDIVLOOPM
  imports TDIVLOOPM-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Prog </k>
  rule [tdeq]: td(I) => 10 /Int (I +Int 0)
  rule [tdiv]: <k> tdiv(I) => val(td(I)) </k>
  rule [botha]: <k> both(I) => tdiv(I) </k>
  rule [bothb]: <k> both(I) => spin(td(I +Int 1), 0) </k>
  rule [spin]: <k> spin(10, N) => spin(10, N +Int 1) </k>
  rule [stop]: <k> spin(5, N) => done(N) </k>
endmodule
