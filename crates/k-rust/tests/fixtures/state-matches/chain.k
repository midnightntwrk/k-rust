// Chains of patterns (docs/compatibility.md, "Chains"): programs whose paths branch and meet.
//
// - `go(N)`: `gb` to `b(N)` or `gc` to `c(N)`; each sets `<out>` to N and goes on to `t(2)`, which
//   counts down to `t(0)` and ends. The `c` branch, met second, reaches `t(2)` at depth 2 equal
//   to the `b` branch's state there, so a run without a chain merges it.
// - `mark(N)`: `me` to `e(N)` or `mf` to `f(N)`, both then ending with `<out> N </out>` at depth
//   2; the step from `e(N)`, met first, reads an implementation-chosen value
//   (`size(keys_list(...))` of a two-key map, 2 in every listing order), the step from `f(N)`
//   reads nothing.
// - `loop(N)`: counts N down to 0, one state per value, then ends.

module CHAIN-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= go(Int)   [symbol(go)]
               | mark(Int) [symbol(mark)]
               | loop(Int) [symbol(loop)]
endmodule

module CHAIN
  imports CHAIN-SYNTAX
  imports INT
  imports MAP
  imports LIST
  imports BOOL

  syntax KItem ::= b(Int) [symbol(b)] | c(Int) [symbol(c)] | t(Int) [symbol(t)]
                 | e(Int) [symbol(e)] | f(Int) [symbol(f)]

  configuration <k> $PGM:Pgm </k>
                <out> 0 </out>

  rule [gb]: <k> go(N) => b(N) ... </k>
  rule [gc]: <k> go(N) => c(N) ... </k>
  rule [bt]: <k> b(N) => t(2) ... </k> <out> _ => N </out>
  rule [ct]: <k> c(N) => t(2) ... </k> <out> _ => N </out>
  rule [tick]: <k> t(K) => t(K -Int 1) ... </k> requires K >Int 0
  rule [tend]: <k> t(0) => .K ... </k>

  rule [me]: <k> mark(N) => e(N) ... </k>
  rule [mf]: <k> mark(N) => f(N) ... </k>
  rule [ed]: <k> e(N) => .K ... </k>
             <out> _ => N +Int size(keys_list((1 |-> 0) (2 |-> 0))) -Int 2 </out>
  rule [fd]: <k> f(N) => .K ... </k> <out> _ => N </out>

  rule [down]: <k> loop(N) => loop(N -Int 1) ... </k> requires N >Int 0
  rule [stop]: <k> loop(0) => .K ... </k>
endmodule
