// A language whose integer literals are unsigned. The program grammar imports only
// UNSIGNED-INT-SYNTAX, so `-5` is not an Int token: it parses as the negation `neg(5)`.
// A hole value printed as `-5` therefore does not parse back to the domain value -5.

module UNSIGNED-SYNTAX
  imports UNSIGNED-INT-SYNTAX

  syntax Exp ::= Int
               | "-" Exp          [symbol(neg), strict]
               > Exp "+" Exp      [symbol(plus), left, strict]
               | "(" Exp ")"      [bracket]
  syntax Pgm ::= "print" Exp ";"  [symbol(print), strict]
endmodule

module UNSIGNED
  imports UNSIGNED-SYNTAX
  imports INT
  imports LIST
  imports BASIC-K

  syntax KResult ::= Int

  configuration <k> $PGM:Pgm </k>
                <out> .List </out>

  rule [neg]:   <k> - I:Int => 0 -Int I ... </k>
  rule [plus]:  <k> I1:Int + I2:Int => I1 +Int I2 ... </k>
  rule [print]: <k> print I:Int ; => .K ... </k> <out> ... .List => ListItem(I) </out>
endmodule
