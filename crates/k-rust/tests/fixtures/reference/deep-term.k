module DEEP-TERM
  syntax Term ::= "zero" [symbol(zero)]
                | "wrap" "(" Term ")" [symbol(wrap)]

  configuration <k> $PGM:Term </k>
endmodule
