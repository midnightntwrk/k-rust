module AMB-SYNTAX
  imports INT-SYNTAX
  syntax Exp ::= Int
               | Exp "+" Exp [left]
               | Exp "-" Exp [left]
endmodule
module AMB
  imports AMB-SYNTAX
  configuration <k> $PGM:Exp </k>
endmodule
