// Re-pin L1-1-fix-1 (L1-1 review 1, minor 2): conv.k with `mc` dividing by 0, the definition the
// mutant `mc: 1 -> 0` of conv.k compiles to. Both converging paths end in an undefined step at
// depth 2: one Trivial leaf in a state set, two in a path set (kink-campaign
// tests/state_set_routes.rs, route 2).
module CONVZ-SYNTAX
  imports INT-SYNTAX
  syntax Prog ::= a(Int) [symbol(a)]
                | b(Int) [symbol(b)]
                | c(Int) [symbol(c)]
                | m(Int) [symbol(m)]
                | crash(Int) [symbol(crash)]
endmodule
module CONVZ
  imports CONVZ-SYNTAX
  imports INT
  configuration <k> $PGM:Prog </k>
  rule [ab]: <k> a(N) => b(N) </k>
  rule [ac]: <k> a(N) => c(N) </k>
  rule [bm]: <k> b(N) => m(N) </k>
  rule [cm]: <k> c(N) => m(N) </k>
  rule [mc]: <k> m(N) => crash(N /Int 0) </k>
endmodule
