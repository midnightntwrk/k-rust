// imp-semantics/examples/specs/imp-ifs-spec.k with `isUInt64(X)` written out as
// `0 <=Int X andBool X <Int 2^64`. `isUInt64` has no production in K 7.1.337's builtins or in
// kimp, so the original file does not parse.
requires "imp-verification.k"

module IMP-IFS-UINT64-SPEC
  imports IMP-VERIFICATION

  claim [assignment]:
      <k>
        $n = N;
      =>
        .K
      ...
      </k>
    <env>
        $n |-> (_ => ?N')
    </env>
    ensures ?N' ==Int N

  claim [branching-if]:
      <k>
        $n = N:Int;
        $m = M:Int;
        if ($n == $m) { $k = 1; } else { $k = 0; }
      =>
        .K
      ...
      </k>
    <env>
        $n |-> (_:Int => ?_:Int)
        $m |-> (_:Int => ?_:Int)
        $k |-> (_:Int => ?K:Int)
    </env>
    requires 0 <=Int N andBool N <Int 18446744073709551616
     andBool 0 <=Int M andBool M <Int 18446744073709551616
    ensures ?K ==Int 1 orBool ?K ==Int 0

endmodule