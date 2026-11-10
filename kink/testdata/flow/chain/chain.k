// Flow fixture: chain patterns. `go(N)` logs N, then takes one of two branches: `left`
// logs N + 1; `right` raises the alarm, then logs 2 * N. `count(N)` logs N, N - 1, ..., 1 on its
// one path, then is done.
module CHAIN-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= go(Int)    [symbol(go)]
               | count(Int) [symbol(count)]
endmodule

module CHAIN
  imports CHAIN-SYNTAX
  imports INT
  imports LIST
  imports BOOL
  syntax KItem ::= pick(Int) [symbol(pick)]
                 | ev(Int)   [symbol(ev)]
                 | "alarm"   [symbol(alarm)]
                 | "done"    [symbol(done)]
  configuration <k> $PGM:Pgm </k> <log> .List </log> <alarm> false </alarm>

  rule [go]:    <k> go(N) => ev(N) ~> pick(N) ... </k>
  rule [left]:  <k> pick(N) => ev(N +Int 1) ~> done ... </k>
  rule [right]: <k> pick(N) => alarm ~> ev(N *Int 2) ~> done ... </k>
  rule [log]:   <k> ev(V) => .K ... </k> <log> L => L ListItem(V) </log>
  rule [raise]: <k> alarm => .K ... </k> <alarm> _ => true </alarm>
  rule [tick]:  <k> count(N) => ev(N) ~> count(N -Int 1) ... </k> requires N >Int 0
  rule [last]:  <k> count(0) => done ... </k>
endmodule
