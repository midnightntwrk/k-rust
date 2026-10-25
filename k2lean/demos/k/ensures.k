// A definition whose rules have `ensures` clauses, for the gate (k2lean/tests/gate.sh, library
// `ens`; k2lean/docs/design.md, §2, "Rules"). A rule `l => r requires c ensures e` applies where
// `l` matches and `c` holds, and steps there only where `e` is `true`:
// - `assume(B)` steps to `.K` when `B` is true, and has no successor when it is false;
// - `half(N)` steps when `N /Int 2 >Int 0`, and has no successor at `N <Int 2`;
// - `inv(N)` constrains by a partial function: at `N == 0` the ensures is undefined, so the rule
//   applies without a successor;
// - `chk(N)` has an `owise` rule, which steps only where the first rule does not apply: at
//   `chk(N)` with `N <=Int 0` the first rule applies (its ensures is false), so neither steps;
// - `pick(N)`'s two rules are apart by their ensures only (no `N` makes both true);
// - `both(N)`'s two rules overlap exactly where both ensures hold (`0 < N < 10`, witnessed).

module ENSURES-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Cmd ::= "assume" "(" Bool ")" [symbol(assume)]
               | "half" "(" Int ")"    [symbol(half)]
               | "inv" "(" Int ")"     [symbol(inv)]
               | "chk" "(" Int ")"     [symbol(chk)]
               | "pick" "(" Int ")"    [symbol(pick)]
               | "both" "(" Int ")"    [symbol(both)]
endmodule

module ENSURES
  imports ENSURES-SYNTAX
  imports INT
  imports BOOL

  configuration <k> $PGM:Cmd </k> <out> 0 </out>

  rule <k> assume(B) => .K ... </k> ensures B

  rule <k> half(N) => .K ... </k> <out> _ => N /Int 2 </out> requires N >=Int 0 ensures N /Int 2 >Int 0

  rule <k> inv(N) => .K ... </k> <out> _ => 1 </out> ensures 100 /Int N >Int 1

  rule <k> chk(N) => .K ... </k> <out> _ => N </out> ensures N >Int 0
  rule <k> chk(_) => .K ... </k> <out> _ => 0 </out> [owise]

  rule <k> pick(N) => .K ... </k> <out> _ => 1 </out> ensures N >Int 0
  rule <k> pick(N) => .K ... </k> <out> _ => 2 </out> ensures N <Int 0

  rule <k> both(N) => .K ... </k> <out> _ => 1 </out> ensures N >Int 0
  rule <k> both(N) => .K ... </k> <out> _ => 2 </out> ensures N <Int 10
endmodule
