// Reasons that name the hook their fact names (UNNAMED-HOOK).
//
// `pick(N)` has two rules of one priority. `plain` ends with 0 in <out>. `steer` writes `f(N)`,
// whose equation `fa` requires `(1 <<Int N) >Int 0` and `fb` requires `N >Int 0`. For N of
// 33554432 or more the shift is left unevaluated as an unsupported hook (`INT.shl`), `fb`
// applies, and the path ends with 2 and nothing on its leaf but the run's `unsupportedHooks`
// record (as STEER's `big.pgm`). Unlike STEER's, both equations give 2, so their overlap joins,
// the definition has data, and every end is data. One path follows `plain` and ends cleanly; the
// program's run of every path records the hook and nothing else.

module HOOKNAME-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= pick(Int)  [symbol(pick)]
endmodule

module HOOKNAME
  imports HOOKNAME-SYNTAX
  imports INT
  imports BOOL

  configuration <k> $PGM:Pgm </k>
                <out> 0 </out>

  syntax Int ::= f(Int)  [function, symbol(f)]
  rule [fa]: f(N) => 2 requires (1 <<Int N) >Int 0
  rule [fb]: f(N) => 2 requires N >Int 0

  rule [plain]: <k> pick(_) => .K ... </k> <out> _ => 0 </out>
  rule [steer]: <k> pick(N) => .K ... </k> <out> _ => f(N) </out>
endmodule
