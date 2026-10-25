// Re-pin L1-1-fix-1 (L1-1 review 1, minors 1 and 4): two paths converge on one final
// configuration. a(N) has two successors b(N) and c(N); both step to m(N) at depth 2, which
// steps to crash(N /Int 1) at depth 3. A path set has two equal final leaves, a state set one.
// With a classifier that reads `crash` as a crash, the single-crash rule of the campaign runner
// reads that multiplicity (kink-campaign tests/state_set_routes.rs).
module CONV-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= a(Int) [symbol(a)]
                | b(Int) [symbol(b)]
                | c(Int) [symbol(c)]
                | m(Int) [symbol(m)]
                | crash(Int) [symbol(crash)]
endmodule
module CONV
  imports CONV-SYNTAX
  imports INT
  configuration <k> $PGM:Prog </k>
  rule [ab]: <k> a(N) => b(N) </k>
  rule [ac]: <k> a(N) => c(N) </k>
  rule [bm]: <k> b(N) => m(N) </k>
  rule [cm]: <k> c(N) => m(N) </k>
  rule [mc]: <k> m(N) => crash(N /Int 1) </k>
endmodule
