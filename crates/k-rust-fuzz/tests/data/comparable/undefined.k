// Undefined steps for the comparable judgement (kink27 FUZZ-UNDEF-P3; kink-flow's
// `fuzz_parity` (d) runs the same definition).
//
// `go(N)` writes `g(N)` to <log> and `hgo(N)` writes `h(N)`, then `step(N)` writes `N /Int 0` to
// <out>: an undefined step from every input, taken from a configuration whose <log> holds an
// application no equation reduces. `g` is total, `h` is not.
// - `go(1)` takes its undefined step from a ground configuration without a path condition that
//   exists (`g` is total), though `g(1)` is no value: an undefined step is no end and its term is
//   never compared, and the definition has data (its full critical-pair check reports nothing),
//   so the run is comparable with the empty set of ends.
// - `hgo(1)` builds the partial `h(1)`, whose definedness k-rust records in the path condition, so
//   its undefined steps are taken from states that are not decided.

module UX-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= go(Int) [symbol(go)] | hgo(Int) [symbol(hgo)]
endmodule

module UX
  imports UX-SYNTAX
  imports INT
  syntax Int   ::= g(Int) [function, total, symbol(g)]
                 | h(Int) [function, symbol(h)]
  syntax KItem ::= step(Int) [symbol(step)]
  configuration <k> $PGM:Pgm </k> <log> 0 </log> <out> 0 </out>
  rule [g-zero]: g(0) => 1
  rule [h-zero]: h(0) => 1
  rule [go]:   <k> go(N) => step(N) </k> <log> _ => g(N) </log>
  rule [hgo]:  <k> hgo(N) => step(N) </k> <log> _ => h(N) </log>
  rule [step]: <k> step(N) => .K </k> <log> _ => 0 </log> <out> _ => N /Int 0 </out>
endmodule
