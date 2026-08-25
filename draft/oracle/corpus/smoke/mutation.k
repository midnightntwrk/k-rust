module ORACLE-SMOKE-SYNTAX
  imports INT-SYNTAX

  syntax Exp ::= "unit"       [symbol(unit)]
               | "succ" "(" Exp ")" [symbol(succ)]
               | Exp "+" Exp  [symbol(add), function]
endmodule

module ORACLE-SMOKE
  imports ORACLE-SMOKE-SYNTAX
  imports INT

  configuration <k> $PGM:Exp </k>

  rule unit + Y:Exp => unit
  rule succ(X:Exp) + Y:Exp => succ(X + Y)
endmodule
