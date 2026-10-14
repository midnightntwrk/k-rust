// Bracket insertion by priority, associativity and capture (krs-unparse unit-test oracle).
module BRACKETS-SYNTAX
  imports INT-SYNTAX
  imports ID-SYNTAX
  syntax Exp ::= Int | Id
               | "(" Exp ")" [bracket]
               > Exp "^" Exp [symbol(pow), right]
               > left: Exp "*" Exp [symbol(mul)]
               > left: Exp "+" Exp [symbol(add)]
                     | Exp "-" Exp [symbol(sub)]
  syntax Exp ::= "let" Id "=" Exp "in" Exp [symbol(let)]
  syntax Tm ::= Int
              | "mk" [symbol(mk)]
              | Tm "&" Tm [symbol(tand), left]
              > Tm "|" Tm [symbol(tor), left]
  syntax Pgm ::= Exp ";" [symbol(stmt)]
               | "tm" Tm ";" [symbol(tmStmt)]
               | Pgm Pgm [symbol(pgms), right, format(%1%n%2)]
endmodule

module BRACKETS
  imports BRACKETS-SYNTAX
  imports INT
  configuration <k> $PGM:Pgm </k>
  rule <k> P1:Pgm P2:Pgm => P1 ~> P2 ...</k>
  rule <k> tm mk ; => tm (1 | 2) & 3 ; ...</k>
endmodule
