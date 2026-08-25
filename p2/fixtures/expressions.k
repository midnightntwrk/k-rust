module P2-EXPRESSIONS
  syntax Exp ::= "n"               [symbol(n)]
               | Exp "+" Exp       [symbol(plus), left]
               | Exp "*" Exp       [symbol(times), left]
  syntax priority times > plus

  configuration <k> $PGM:Exp </k>
endmodule
