// A data hole at the head of `<k>` whose values have several own sorts (FZ-G8 review 2, R1).
//
// `Shape`, `Circle` and `Square` are declared as in VALUES. The configuration variable `$SHAPE`
// is the whole `<k>` cell; the assembler injects its value from the value's own sort (D19), so
// the anchor `circle(9)` sits under `inj{Circle, KItem}` and `square(4, true)` under
// `inj{Square, KItem}`. `round` consumes a circle and `boxed` a square.

module SHAPE-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX

  syntax Pgm ::= "run"  [symbol(run)]
endmodule

module SHAPE
  imports SHAPE-SYNTAX
  imports INT
  imports BOOL

  syntax Shape   ::= Circle | Square
  syntax Circle  ::= circle(Int)             [symbol(circle)]
  syntax Square  ::= square(Int, Bool)       [symbol(square)]

  configuration <k> $SHAPE:Shape </k>
                <prog> $PGM:Pgm </prog>
                <out> 0 </out>

  rule [round]: <k> circle(I) => .K </k> <out> _ => I </out>
  rule [boxed]: <k> square(I, _) => .K </k> <out> _ => 0 -Int I </out>
endmodule
