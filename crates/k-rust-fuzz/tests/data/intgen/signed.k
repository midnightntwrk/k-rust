// UNSIGNED (`unsigned/unsigned.k`) with signed literals: `-5` is one token, the domain value
// -5. Its modules keep UNSIGNED's names, so that it is a mutant of UNSIGNED whose grammar reads
// negative literals, and UNSIGNED a mutant of it whose grammar does not (FZ-INTGEN).

module UNSIGNED-SYNTAX
  imports INT-SYNTAX

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
