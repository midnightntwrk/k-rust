// Rule-graph edges (FZ-G8, ARCHITECTURE.md 6.3).
//
// - `go` rewrites `start(N)` to `norm(N)`. `norm` is a production with an `anywhere` equation
//   (`normalize`), so `norm(N)` denotes `done(N)` and `finish` applies next, although `go`'s
//   right-hand side read as a left-hand side has the head `norm`, which `finish` does not match.
// - `call` rewrites `call(N)` to `mk(N)`, an application of a function of sort `Step`; its
//   equation gives `done(N)`, so `finish` applies next.
// - `other` consumes `other(N)`, of sort `Other`, which no term of sort `Step` denotes. Only
//   `stray` produces it.
// - `finish` rewrites the whole `<k>` cell to `.K`, so it enables no rule.

module GRAPH-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= start(Int)  [symbol(start)]
               | call(Int)   [symbol(call)]
               | stray(Int)  [symbol(stray)]
endmodule

module GRAPH
  imports GRAPH-SYNTAX
  imports INT

  syntax Step  ::= norm(Int)  [symbol(norm)]
                 | done(Int)  [symbol(done)]
                 | mk(Int)    [function, total, symbol(mk)]
  syntax Other ::= other(Int) [symbol(other)]

  configuration <k> $PGM:Pgm </k>
                <out> 0 </out>

  rule [go]:        <k> start(N) => norm(N) ... </k>
  rule [normalize]: norm(N) => done(N) [anywhere]
  rule [call]:      <k> call(N) => mk(N) ... </k>
  rule [mk]:        mk(N) => done(N)
  rule [finish]:    <k> done(N) => .K </k> <out> _ => N </out>
  rule [stray]:     <k> stray(N) => other(N) ... </k>
  rule [other]:     <k> other(N) => .K </k> <out> _ => 0 -Int N </out>
endmodule
