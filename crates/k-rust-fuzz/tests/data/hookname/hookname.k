// Reasons that name the hook their fact names (UNNAMED-HOOK).
//
// `pick(N)` has two rules of one priority. `plain` ends with 0 in <out>. `steer` writes `f(N)`,
// whose equation `fa` requires `(1 <<Int N) >Int 0` and `fb` requires `N >Int 0`. For N of
// 33554432 or more the shift is left unevaluated as an unsupported hook (`INT.shl`), `fb`
// applies, and the path ends with 2 and nothing on its leaf but the run's `unsupportedHooks`
// record (as STEER's `big.pgm`). Unlike STEER's, both equations give 2, so their overlap joins,
// the definition has data, and every end is data. One path follows `plain` and ends cleanly; the
// program's run of every path records the hook and nothing else.
//
// `exp(N)` has two rules of one priority: `calm` ends with N in <out>, `exp` leaves
// `r(expFloat(...))`, an application of `FLOAT.exp`, which k-rust does not evaluate, so that path
// halts `unsupported-hook` with the hook in its cause. One path follows `calm`.
//
// `which(N)` reads an implementation-chosen value of a different hook by the sign of N: the order
// of a two-key map's keys (`MAP.keys_list`) for N > 0, of a two-element set's elements
// (`SET.set2list`) otherwise. Both end with 2 in <out>, marked.

module HOOKNAME-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= pick(Int)  [symbol(pick)]
               | exp(Int)   [symbol(exp)]
               | which(Int) [symbol(which)]
endmodule

module HOOKNAME
  imports HOOKNAME-SYNTAX
  imports INT
  imports BOOL
  imports FLOAT
  imports MAP
  imports SET
  imports LIST
  imports COLLECTIONS

  configuration <k> $PGM:Pgm </k>
                <out> 0 </out>

  syntax Int ::= f(Int)  [function, symbol(f)]
  rule [fa]: f(N) => 2 requires (1 <<Int N) >Int 0
  rule [fb]: f(N) => 2 requires N >Int 0

  rule [plain]: <k> pick(_) => .K ... </k> <out> _ => 0 </out>
  rule [steer]: <k> pick(N) => .K ... </k> <out> _ => f(N) </out>

  syntax KItem ::= r(Float)  [symbol(r)]
  rule [calm]: <k> exp(N) => .K ... </k> <out> _ => N </out>
  rule [exp]:  <k> exp(N) => r(expFloat(Int2Float(N, 53, 11))) ... </k>

  rule [which-map]: <k> which(N) => .K ... </k>
                    <out> _ => size(keys_list((N |-> 0) [ N +Int 1 <- 1 ])) </out>
    requires N >Int 0
  rule [which-set]: <k> which(N) => .K ... </k>
                    <out> _ => size(Set2List(SetItem(N) SetItem(N +Int 1))) </out>
    requires N <=Int 0
endmodule
