// FZ-UNSUPPORTED review N1: the <k> cell lies under a `?` cell that is absent from the initial
// configuration; the program lives in <code>. `start(N)` spawns a worker that adds N to <out>
// and is reaped; `bad(N)` has no rule, so the program is stuck in <code> having done nothing.
module QOPT-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= start(Int) [symbol(start)]
               | bad(Int)   [symbol(bad)]
               | "done"     [symbol(done)]
endmodule

module QOPT
  imports QOPT-SYNTAX
  imports INT
  syntax KItem ::= add(Int) [symbol(add)]
  configuration <code> $PGM:Pgm </code>
                <worker multiplicity="?"> <k> .K </k> </worker>
                <out> 0 </out>
  rule [start]: <code> start(N) => done </code> (.Bag => <worker> <k> add(N) </k> </worker>)
  rule [add]:   <k> add(N) => .K ... </k> <out> M => M +Int N </out>
  rule [reap]:  (<worker> <k> .K </k> </worker> => .Bag)
endmodule
