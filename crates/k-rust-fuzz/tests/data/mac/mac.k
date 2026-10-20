// Baseline of the macro-only pair (phase-1 review B1). `inc(N)` is a macro: assembling a
// program expands it to `val(N +Int 1)` before execution, so `inc(3)` ends with `<out> 4`.
// The macro rule is emitted into macros.kore, not definition.kore.

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

  rule inc(I) => val(I +Int 1)
  rule [out]: <k> val(I) => .K ... </k> <out> _ => I </out>
endmodule
