module MAIN-SYNTAX
  imports BOOL
  imports ML-SYNTAX

  syntax Cell
  syntax Exp ::= "a" [symbol(a)]
               | "b" [symbol(b)]
               | "c" [symbol(c)]
               | "pair" "(" Exp "," Exp ")" [symbol(pair)]
               | "bodyMacro" [macro, symbol(bodyMacro)]
  syntax Bool ::= "predicate" "(" Exp ")" [function, symbol(predicate)]
                | "cellPredicate" "(" Cell ")" [function, symbol(cellPredicate)]
                | "requiresMacro" [function, macro, symbol(requiresMacro)]
                | "binderMacro" [function, macro, symbol(binderMacro)]
endmodule

module MAIN
  imports MAIN-SYNTAX

  configuration <top> <k> $PGM:Exp </k> </top>

  rule bodyMacro => X:Exp [unboundVariables(X)]
  rule requiresMacro => predicate(Y:Exp) [unboundVariables(Y)]
  rule binderMacro => #Exists _ . predicate(_) [unboundVariables(_)]
endmodule
