module OWISE-IGNORED-COMPETITORS
  imports BOOL

  syntax Exp ::= "a" [symbol(a)]
               | "b" [symbol(b)]
               | "choose(" Exp "," Exp ")" [function, symbol(choose)]
  syntax Bool ::= Exp "==" Exp [function, symbol(eq)]

  rule choose(X:Exp, _Y:Exp) => X [simplification, label(simplified)]
  rule choose(a, Y:Exp) => Y [label(choose-a)]
  rule choose(X:Exp, b) => X requires X == a [label(choose-b)]
  rule choose(b, Y:Exp) => Y [non-executable, label(never)]
  rule choose(X:Exp, Y:Exp) => X requires X == Y [owise, label(otherwise)]
endmodule
