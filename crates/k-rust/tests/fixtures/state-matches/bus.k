// List scans in pattern matching (docs/compatibility.md, "Lists"): `log(N)` appends
// `write(1, 0)`, `write(49424, N)`, `write(2, 0)` and `read(49424, N)` to the `<bus>` list, one
// step each, so a pattern with an item between two list parts, or with two ordered items, is
// asked of closed lists of every length from 0 to 4.

module BUS-SYNTAX
  imports INT-SYNTAX

  syntax Pgm ::= log(Int) [symbol(log)]
endmodule

module BUS
  imports BUS-SYNTAX
  imports INT
  imports LIST

  syntax KItem ::= w(Int, Int) [symbol(w)] | r(Int, Int) [symbol(r)]
  syntax KItem ::= write(Int, Int) [symbol(write)] | read(Int, Int) [symbol(read)]

  configuration <k> $PGM:Pgm </k>
                <bus> .List </bus>

  rule [log]: <k> log(N) => w(1, 0) ~> w(49424, N) ~> w(2, 0) ~> r(49424, N) ... </k>
  rule [w]: <k> w(A, V) => .K ... </k> <bus> B => B ListItem(write(A, V)) </bus>
  rule [r]: <k> r(A, V) => .K ... </k> <bus> B => B ListItem(read(A, V)) </bus>
endmodule
