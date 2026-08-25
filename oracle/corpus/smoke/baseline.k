module ORACLE-SMOKE-SYNTAX
  imports INT-SYNTAX

  syntax Exp ::= "zero"       [symbol(zero)]
               | "succ" "(" Exp ")" [symbol(succ)]
               | Exp "+" Exp  [symbol(add), function]
endmodule

module ORACLE-SMOKE
  imports ORACLE-SMOKE-SYNTAX
  imports INT

  configuration <k> $PGM:Exp </k>

  rule zero + Y:Exp => Y
  rule succ(X:Exp) + Y:Exp => succ(X + Y)
endmodule
