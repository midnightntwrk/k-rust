module SCAN-D-SYNTAX
  imports INT-SYNTAX
  imports BUILTIN-ID-TOKENS
  syntax Id ::= r"[A-Za-z_][A-Za-z_0-9]*" [prec(1), token]
              | #LowerId [token]
              | #UpperId [token]
  syntax Exp ::= Id | Int | Exp "+" Exp [symbol(plus), left]
endmodule
module SCAN-D
  imports SCAN-D-SYNTAX
  imports INT
  configuration <k> $PGM:Exp </k>
  rule X + 0 => X
endmodule
