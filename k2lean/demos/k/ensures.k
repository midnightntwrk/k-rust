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
// A function equation's `ensures` (k2lean/docs/design.md, §2, "Functions"): `f(ps) = r ∧ ⌈e⌉`,
// so where `e` is false the value is undefined, and no later equation applies, since this one's
// left-hand side and requires matched:
// - `enc(N)` is `N +Int 1` for `0 <= N <= 100`, undefined for `N > 100` (not the `owise` value),
//   and `0` for `N < 0` (the first equation's requires fails, so the `owise` one applies).

module ENSURES-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Cmd ::= "assume" "(" Bool ")" [symbol(assume)]
               | "half" "(" Int ")"    [symbol(half)]
               | "inv" "(" Int ")"     [symbol(inv)]
               | "chk" "(" Int ")"     [symbol(chk)]
               | "pick" "(" Int ")"    [symbol(pick)]
               | "both" "(" Int ")"    [symbol(both)]
               | "encode" "(" Int ")"  [symbol(encode)]
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

  syntax Int ::= enc(Int) [function, symbol(enc)]
  rule enc(N) => N +Int 1 requires N >=Int 0 ensures N <=Int 100
  rule enc(_) => 0 [owise]

  rule <k> encode(N) => .K ... </k> <out> _ => enc(N) </out>
endmodule
