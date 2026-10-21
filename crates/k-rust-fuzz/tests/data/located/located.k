// A program sort that records locations (FZ-02 review R1): every `Exp` a program denotes is
// wrapped in `#location(Exp, file, line, column, line, column)`. A hole value printed with
// another length than its anchor moves the columns of every later term on its line, and of the
// terms that contain it; nothing else about the configuration changes.

module LOCATED-SYNTAX
  imports INT-SYNTAX

  syntax Exp ::= Int
               | Exp "+" Exp       [left, symbol(plus)]
  syntax Exp [locations]
  syntax Pgm ::= "print" Exp ";"   [symbol(print)]
endmodule

module LOCATED
  imports LOCATED-SYNTAX
  imports INT
  imports K-LOCATIONS

  configuration <k> $PGM:Pgm </k>

  rule <k> print _ ; => .K </k>
endmodule
