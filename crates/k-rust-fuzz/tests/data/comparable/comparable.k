// Comparable ends (P7-ADDENDUM section 4, FZ-COMPARABLE-A and -Q).
//
// `start(N)` has two rules of one priority: `finish` ends with N in <out>, `loop` enters
// `spin(N)`, which counts up forever without repeating a configuration. One path through
// `finish` ends cleanly, but the program's all-paths run never completes.
//
// `f` is total, with the equations `f(0) => 1` and `f(X) => Y requires X =/=Int 0 andBool
// Y >Int X`, whose result variable `Y` its left-hand side does not bind. So `f(0)` is 1, and for
// every other X `f(X)` stays unevaluated, a total application (ceil-free), and the second
// equation's condition is reported undecided (`undecided-condition`, its result variable
// unbound). `cond(N)` ends with `f(N)` in <out>: a clean leaf for the fuzz, which carries that
// diagnostic unless N is 0.
//
// `both(N)` has two rules of one priority: `both-plain` ends with N, `both-cond` with `f(N)`.
// For N other than 0 the second leaf carries the diagnostic, the first does not when no work
// budget copies it there.

module COMPARABLE-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= start(Int)  [symbol(start)]
               | cond(Int)   [symbol(cond)]
               | both(Int)   [symbol(both)]
endmodule

module COMPARABLE
  imports COMPARABLE-SYNTAX
  imports INT
  imports BOOL

  syntax Int   ::= f(Int)     [function, total, symbol(f)]
  syntax KItem ::= spin(Int)  [symbol(spin)]

  configuration <k> $PGM:Pgm </k>
                <out> 0 </out>

  rule [f-zero]: f(0) => 1
  rule [f-some]: f(X) => Y requires X =/=Int 0 andBool Y >Int X [unboundVariables(Y)]

  rule [finish]:     <k> start(N) => .K ... </k> <out> _ => N </out>
  rule [loop]:       <k> start(N) => spin(N) ... </k>
  rule [spin]:       <k> spin(N) => spin(N +Int 1) ... </k>
  rule [cond]:       <k> cond(N) => .K ... </k> <out> _ => f(N) </out>
  rule [both-plain]: <k> both(N) => .K ... </k> <out> _ => N </out>
  rule [both-cond]:  <k> both(N) => .K ... </k> <out> _ => f(N) </out>
endmodule
