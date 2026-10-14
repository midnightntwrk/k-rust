// Sorted collections and K sequences (krs-unparse unit-test oracle).
module SORTED-SYNTAX
  imports INT-SYNTAX
  imports ID-SYNTAX
  syntax Pgm ::= Id "=" Int ";" [symbol(assign)]
               | Pgm Pgm [symbol(seq), right, format(%1%n%2)]
endmodule

module SORTED
  imports SORTED-SYNTAX
  imports INT
  imports MAP
  imports SET
  imports ID
  configuration <k> $PGM:Pgm </k> <env> .Map </env> <seen> .Set </seen>
  rule <k> P1:Pgm P2:Pgm => P1 ~> P2 ...</k>
  rule <k> X:Id = I:Int ; => .K ...</k> <env> E => E [ X <- I ] </env> <seen> S => S SetItem(I) </seen>
endmodule
