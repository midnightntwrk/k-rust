// Rule targets and their modes.
//
// - `div`: its right-hand side `A /Int B` is undefined when B is 0, so `div(A, 0)` is an
//   undefined step (a `trivial` halt): the rule is in coverage `applied` (covered) and in no
//   clean leaf's trace (not fired).
// - `check-hit`: its guard `A ==Int 42` fails on every other input, so `check(A)` reaches the
//   condition (coverage `matched`) and ends through `check-miss`.
// - `twin-a` and `twin-b` are equal rules under two labels: one compiled identity shared by two
//   catalog entries (`shared_identity`). `dormant` is `non-executable`. `double` is a function
//   equation. A rule target naming any of these is refused.

module RULES-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= div(Int, Int)   [symbol(div)]
               | check(Int)      [symbol(check)]
               | twice(Int)      [symbol(twice)]
               | "twin"          [symbol(twin)]
endmodule

module RULES
  imports RULES-SYNTAX
  imports INT
  imports BOOL

  syntax Int ::= double(Int)  [function, total, symbol(double)]

  configuration <k> $PGM:Pgm </k>
                <out> 0 </out>

  rule [double]:     double(I) => I *Int 2

  rule [div]:        <k> div(A, B) => .K ... </k> <out> _ => A /Int B </out>
  rule [check-hit]:  <k> check(A) => .K ... </k> <out> _ => 1 </out> requires A ==Int 42
  rule [check-miss]: <k> check(_) => .K ... </k> <out> _ => 0 </out> [owise]
  rule [twice]:      <k> twice(A) => .K ... </k> <out> _ => double(A) </out>
  rule [twin-a]:     <k> twin => .K ... </k> <out> _ => 2 </out>
  rule [twin-b]:     <k> twin => .K ... </k> <out> _ => 2 </out>
  rule [dormant]:    <k> twin => .K ... </k> <out> _ => 3 </out> [non-executable]
endmodule
