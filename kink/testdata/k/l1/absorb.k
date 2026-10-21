// Re-pin L1-1-fix-1 (L1-1 review 1, minor 3): an earlier stuck leaf absorbs a later depth-bound
// leaf of the same configuration. s(N) -> a(N +Int 1); a(K) has successors b(K) and c(K);
// b(K) -> d(K) (stuck at depth 3); c(K) -> e(K) -> d(K) (depth 4). Under max_depth 4 the
// second path is depth-bound at d(K): the path set is incomplete, the state set is {d(K)},
// complete (kink-campaign tests/state_set_routes.rs).
module ABSORB-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= s(Int) [symbol(s)]
                | a(Int) [symbol(a)]
                | b(Int) [symbol(b)]
                | c(Int) [symbol(c)]
                | e(Int) [symbol(e)]
                | d(Int) [symbol(d)]
endmodule
module ABSORB
  imports ABSORB-SYNTAX
  imports INT
  configuration <k> $PGM:Prog </k>
  rule [start]: <k> s(N) => a(N +Int 1) </k>
  rule [ab]: <k> a(K) => b(K) </k>
  rule [ac]: <k> a(K) => c(K) </k>
  rule [bd]: <k> b(K) => d(K) </k>
  rule [ce]: <k> c(K) => e(K) </k>
  rule [ed]: <k> e(K) => d(K) </k>
endmodule
