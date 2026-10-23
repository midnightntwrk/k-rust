// How an undefined step counts. `5 / 0` rewrites by `X / Y => X /Int Y` to `5 /Int 0`, which
// is \bottom: the configuration has no successor. All-path reachability then holds only if the
// configuration itself satisfies the target.
requires "imp-verification.k"

module IMP-DIV0-SPEC
  imports IMP-VERIFICATION

  // false: `5 / 0` has no successor and is not `7`
  claim [div0-seven]: <k> 5 / 0 => 7 ... </k>

  // false for the same reason
  claim [div0-any-int]: <k> 5 / 0 => ?_:Int ... </k>

  // true in zero steps
  claim [div0-self]: <k> 5 / 0 => 5 / 0 ... </k>
endmodule
