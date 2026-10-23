// `two-sum-spec` of imp-sum-spec.k with one auxiliary claim per loop.
// kimp's `while` leaves a `{}` on the continuation at every iteration
// (`while(C) S => if (C) { S while(C) S }`, `{ S } => S ~> { }`), so after one iteration of the
// first loop the <k> cell is `while … ~> { } ~> while … ~> K`, which matches neither
// `two-sum-spec` nor `sum-spec`. Each auxiliary claim is its own loop's invariant: the loop
// followed by an arbitrary continuation (`...`), the other two variables unchanged.
requires "imp-verification.k"

module IMP-TWO-SUM-AUX-SPEC
  imports IMP-VERIFICATION

  claim [loop-n]:
      <k> while (!($n <= 0)) { $s1 = $s1 + $n; $n = $n + -1; } => .K ... </k>
    <env>
        $n |-> (N:Int => 0)
        $m |-> M:Int
        $s1 |-> (S1:Int => S1 +Int ((N +Int 1) *Int N /Int 2))
        $s2 |-> S2:Int
    </env>
  requires N >=Int 0

  claim [loop-m]:
      <k> while (!($m <= 0)) { $s2 = $s2 + $m; $m = $m + -1; } => .K ... </k>
    <env>
        $n |-> N:Int
        $m |-> (M:Int => 0)
        $s1 |-> S1:Int
        $s2 |-> (S2:Int => S2 +Int ((M +Int 1) *Int M /Int 2))
    </env>
  requires M >=Int 0

  claim [two-sum-spec]:
      <k>
        while (!($n <= 0)) { $s1 = $s1 + $n; $n = $n + -1; }
        while (!($m <= 0)) { $s2 = $s2 + $m; $m = $m + -1; }
      => .K ... </k>
    <env>
        $n |-> (N:Int => 0)
        $m |-> (M:Int => 0)
        $s1 |-> (S1:Int => S1 +Int ((N +Int 1) *Int N /Int 2))
        $s2 |-> (S2:Int => S2 +Int ((M +Int 1) *Int M /Int 2))
    </env>
  requires N >=Int 0
   andBool M >=Int 0
endmodule
