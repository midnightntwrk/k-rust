// Re-pin lane 1 (L1-1): a countdown whose work grows with its argument, for the work budget.
// count(N) takes N steps to done(7). The mutations the kink-campaign tests make: the step's 1
// becomes -1 (the count never ends where the baseline does), stop's 7 becomes 8 (the same work,
// another result), and the guard's 0 becomes -2 (two more steps, and another final state).
module WORKLOOP-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= count(Int) [symbol(count)]
                | done(Int) [symbol(done)]
endmodule
module WORKLOOP
  imports WORKLOOP-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Prog </k>
  rule [step]: <k> count(N) => count(N -Int 1) </k> requires N >Int 0
  rule [stop]: <k> count(0) => done(7) </k>
endmodule
