// Flow fixture: explanations of failed pattern answers (FB50-EXPLAIN). A program is a sequence
// of bus operations: `wb(A, V)` writes a byte (writeByte writes V at A, then pushLow writes V at
// A - 1), `wr(A, V)` writes V at A, `rd(A, V)` reads V from A, and `rq(C)` files the request C.
module EXPLAIN-SYNTAX
  imports INT-SYNTAX
  syntax Op ::= wb(Int, Int) [symbol(wb)]
              | wr(Int, Int) [symbol(wr)]
              | rd(Int, Int) [symbol(rd)]
              | rq(Int)      [symbol(rq)]
  syntax Pgm ::= Op
               | Op ";" Pgm  [symbol(seq)]
endmodule

module EXPLAIN
  imports EXPLAIN-SYNTAX
  imports INT
  imports LIST
  imports BOOL
  syntax KItem ::= writeByte(Int, Int) [symbol(writeByte)]
                 | pushLow(Int, Int)   [symbol(pushLow)]
                 | write(Int, Int)     [symbol(write)]
                 | read(Int, Int)      [symbol(read)]
                 | request(Int, Int)   [symbol(request)]
  configuration <k> $PGM:Pgm </k> <requests> .List </requests> <bus> .List </bus>

  rule [next]:      <k> O:Op ; P:Pgm => O ~> P ... </k>
  rule [byte]:      <k> wb(A, V) => writeByte(A, V) ~> pushLow(A, V) ... </k>
  rule [writeByte]: <k> writeByte(A, V) => .K ... </k> <bus> L => L ListItem(write(A, V)) </bus>
  rule [pushLow]:   <k> pushLow(A, V) => .K ... </k> <bus> L => L ListItem(write(A -Int 1, V)) </bus>
  rule [wr]:        <k> wr(A, V) => .K ... </k> <bus> L => L ListItem(write(A, V)) </bus>
  rule [rd]:        <k> rd(A, V) => .K ... </k> <bus> L => L ListItem(read(A, V)) </bus>
  rule [rq]:        <k> rq(C) => .K ... </k> <requests> R => R ListItem(request(C, 0)) </requests>
endmodule
