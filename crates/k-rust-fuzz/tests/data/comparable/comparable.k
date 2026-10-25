// Comparable ends (P7-ADDENDUM section 4, FZ-COMPARABLE-A and -Q).
//
// `start(N)` has two rules of one priority: `finish` ends with N in <out>, `loop` enters
// `spin(N)`, which counts up forever without repeating a configuration. One path through
// `finish` ends cleanly, but the program's all-paths run never completes.
//
// `g` is total, with the one equation `g(0) => 1`. `stay(N)` ends with `g(N)` in <out>: `stay(0)`
// ends with the value 1, and for every other N with an irreducible application of a function,
// ceil-free and with no diagnostic, so a clean leaf for the fuzz, but not data (`is_data`):
// `g(3)` may equal another term in another theory of `g`, so the end cannot be compared by its
// term (P3; INT9 review S3).
//
// The definition's full critical-pair check reports nothing, so its data ends are data. The
// programs whose ends carry diagnostics are in `cond.k`, whose check reports a finding.

module COMPARABLE-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= start(Int)  [symbol(start)]
               | stay(Int)   [symbol(stay)]
endmodule

module COMPARABLE
  imports COMPARABLE-SYNTAX
  imports INT

  syntax Int   ::= g(Int)     [function, total, symbol(g)]
  syntax KItem ::= spin(Int)  [symbol(spin)]

  configuration <k> $PGM:Pgm </k>
                <out> 0 </out>

  rule [g-zero]: g(0) => 1

  rule [finish]: <k> start(N) => .K ... </k> <out> _ => N </out>
  rule [loop]:   <k> start(N) => spin(N) ... </k>
  rule [spin]:   <k> spin(N) => spin(N +Int 1) ... </k>
  rule [stay]:   <k> stay(N) => .K ... </k> <out> _ => g(N) </out>
endmodule
