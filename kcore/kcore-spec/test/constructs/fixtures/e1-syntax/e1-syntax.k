module E1-SYNTAX
  imports INT
  syntax Exp ::= Int
               | "(" Exp ")"                [bracket]
               | neg(Exp, Int)              [symbol(neg)]
               > Exp "*" Exp                [left, symbol(mul)]
               > left:
                 Exp "+" Exp                [symbol(plus)]
               | Exp "-" Exp                [symbol(minus)]
               > right:
                 Exp "^" Exp                [symbol(pow)]
               > non-assoc:
                 Exp "==" Exp               [symbol(eq)]
  syntax Exps ::= List{Exp, ","}            [symbol(exps), terminator-symbol(.exps)]
  syntax NeExps ::= NeList{Exp, ";"}        [symbol(neexps)]
  syntax Name ::= r"[a-z][a-z0-9]*"         [token]
endmodule
