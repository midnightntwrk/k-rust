// Unsigned Int literals and no unary minus at all: `print 7 + -1 ;` does not parse (FZ-INTGEN).
module NOMINUS-SYNTAX
  imports UNSIGNED-INT-SYNTAX

  syntax Exp ::= Int
               > Exp "+" Exp      [symbol(plus), left, strict]
  syntax Pgm ::= "print" Exp ";"  [symbol(print), strict]
endmodule

module NOMINUS
  imports NOMINUS-SYNTAX
  imports INT
  imports LIST
  imports BASIC-K

  syntax KResult ::= Int

  configuration <k> $PGM:Pgm </k>
                <out> .List </out>

  rule [plus]:  <k> I1:Int + I2:Int => I1 +Int I2 ... </k>
  rule [print]: <k> print I:Int ; => .K ... </k> <out> ... .List => ListItem(I) </out>
endmodule
