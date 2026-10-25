// Mutant of mac.k that edits only the macro rule: `inc(N)` expands to `val(N +Int 2)`, so
// `inc(3)` ends with `<out> 5`. Its definition.kore equals the baseline's; only macros.kore
// differs. Every input is a kill, on both backend routes.

module MAC-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= inc(Int)  [macro, symbol(inc)]
               | val(Int)  [symbol(val)]
endmodule

module MAC
  imports MAC-SYNTAX
  imports INT

  configuration <k> $PGM:Pgm </k>
                <out> 0 </out>

  rule inc(I) => val(I +Int 2)
  rule [out]: <k> val(I) => .K ... </k> <out> _ => I </out>
endmodule
