// A definition with two genuine overlaps, for the gate's determinism checks (k2lean/tests/gate.sh,
// library `ovl`): `go(N)` with 0 < N < 10 rewrites by two rules to different configurations
// (listed in `overlaps` and witnessed), `set(N)` with N >= 100 by two rules to the same one
// (joinable, so not listed), and the other pairs of rules never apply at once.
// `look(A, B)` reads the table cell: both of its rules apply where the table binds `B` to
// `wrap(A)` and `A` to the same value (a witness has to choose the table's bindings).

module OVERLAP-SYNTAX
  imports INT-SYNTAX
  syntax Cmd ::= "go" "(" Int ")"  [symbol(go)]
               | "set" "(" Int ")" [symbol(set)]
               | "look" "(" Ty "," Ty ")" [symbol(look)]
  syntax Ty ::= ty(Int) [symbol(ty)]
  syntax Info ::= "void" [symbol(void)]
                | wrap(Ty) [symbol(wrap)]
endmodule

module OVERLAP
  imports OVERLAP-SYNTAX
  imports INT
  imports MAP
  imports K-EQUAL

  configuration <k> $PGM:Cmd </k> <out> 0 </out> <tab> .Map </tab>

  syntax Info ::= info(Map, Ty) [function, total, symbol(info)]
  rule info(M, T) => {M[T] orDefault void}:>Info

  rule <k> go(N) => .K ... </k> <out> _ => N </out> requires N >Int 0
  rule <k> go(N) => .K ... </k> <out> _ => 0 -Int N </out> requires N <Int 10

  rule <k> set(N) => .K ... </k> <out> _ => N </out> requires N >=Int 100
  rule <k> set(N) => .K ... </k> <out> _ => N </out> requires N >=Int 50
  rule <k> set(N) => .K ... </k> <out> _ => 1 </out> requires N <Int 50

  rule <k> look(A, B) => .K ... </k> <out> _ => 1 </out> <tab> M </tab> requires info(M, A) ==K info(M, B)
  rule <k> look(A, B) => .K ... </k> <out> _ => 2 </out> <tab> M </tab> requires info(M, B) ==K wrap(A)
endmodule
