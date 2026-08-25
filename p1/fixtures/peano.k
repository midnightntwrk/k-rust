module P1-PEANO-SYNTAX
  syntax Exp ::= "zero"                    [symbol(zero)]
               | "succ" "(" Exp ")"       [symbol(succ)]
               | "plus" "(" Exp "," Exp ")" [symbol(plus), function]
               | "tick" "(" Exp ")"       [symbol(tick)]
endmodule

module P1-PEANO
  imports P1-PEANO-SYNTAX
  imports K-EQUAL

  configuration <k> $PGM:Exp </k>

  rule plus(zero, Y:Exp) => Y
    requires Y ==K Y
    ensures Y ==K Y
  rule plus(succ(X:Exp), Y:Exp) => succ(plus(X, Y))
  rule tick(X:Exp) => X
endmodule
