module PRIORITY-ANONYMOUS-TAG
  imports INT
  syntax Exp ::= Int | Exp "+" Exp | Exp "*" Exp
  syntax priority _*_ > _+_
endmodule
