// Claims that hold only on stores whose values are `Value`s, the kind 1 invariant `envOk` of
// demos/k/kimp-inv/imp-inv.k. `V` is any `KItem`: kimp's variable lookup reads it, and if it is not a
// value (say the expression `1 + 2`) the program evaluates it, so `$y` ends up holding `3`, not `V`.
// `copy-loop` copies `$x` into `$y` on every iteration, so `$y` must hold `V` at the loop head (its
// circularity). Over every configuration both claims are false; `k2lean claims --assume-invariant Invariant`
// states them for the configurations that satisfy the invariant, where they hold.
requires "imp-inv.k"
requires "imp-verification.k"

module IMP-INV-VERIFICATION
  imports IMP-INV
  imports IMP-VERIFICATION
endmodule

module IMP-INV-SPEC
  imports IMP-INV-VERIFICATION

  claim [copy]: <k> $y = $x ; => .K ... </k>
                <env> $x |-> V $y |-> (_ => V) </env>

  claim [copy-loop]: <k> while (0 < $n) { $y = $x ; $n = $n - 1 ; } => .K ... </k>
                     <env> $x |-> V $y |-> V $n |-> (N => 0) </env>
    requires 0 <=Int N
endmodule
