// Signed Int literals, plus a terminal `-1` that is its own production (FZ-INTGEN review S1):
// `print 7 + -1 ;` reads `-1` as `minusOne`, while `-2`, `-8` and `-200` read as integers.
module MINUSONE-SYNTAX
  imports INT-SYNTAX

  syntax Exp ::= Int
               | "-1"             [symbol(minusOne)]
               > Exp "+" Exp      [symbol(plus), left, strict]
  syntax Pgm ::= "print" Exp ";"  [symbol(print), strict]
endmodule

module MINUSONE
  imports MINUSONE-SYNTAX
  imports INT
  imports LIST
  imports BASIC-K

  syntax KResult ::= Int

  configuration <k> $PGM:Pgm </k>
                <out> .List </out>

  rule [m1]:    <k> -1 => 42 ... </k>
  rule [plus]:  <k> I1:Int + I2:Int => I1 +Int I2 ... </k>
  rule [print]: <k> print I:Int ; => .K ... </k> <out> ... .List => ListItem(I) </out>
endmodule
