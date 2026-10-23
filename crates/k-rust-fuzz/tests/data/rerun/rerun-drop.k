// The re-run pair's mutant (INT7): RERUN without the rule `gb`, so `go(N)` has the ends `a(N)`
// and `c(N)`. Its one path reaches `a(N)`, inside the baseline's set; the baseline's data end
// `c(N)` is not among the one path's ends, so the one-path mode re-runs the mutant on all paths.
// The re-run's set lacks the baseline's `b(opaque(N))`, which is not data, so the case cannot be
// judged (`baseline-end-not-data`); judging the one path as if it were the whole set would
// remove `c(N)`, a false kill.

module RERUN-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= go(Int)  [symbol(go)]
endmodule

module RERUN
  imports RERUN-SYNTAX
  imports INT

  syntax KItem ::= a(Int) | b(Int) | c(Int)
  syntax Int ::= opaque(Int)  [function, total, symbol(opaque)]

  configuration <k> $PGM:Pgm </k>

  rule [ga]: <k> go(N) => a(N) ... </k>
  rule [gc]: <k> go(N) => c(N) ... </k>
endmodule
