module OWISE-COMPETITORS
  syntax Exp ::= "a" [symbol(a)]
               | "b" [symbol(b)]
               | "choose(" Exp ")" [function, symbol(choose)]

  rule choose(a) => a [label(choose-a)]
  rule choose(b) => b [label(choose-b)]
  rule choose(X:Exp) => X:Exp [owise, label(otherwise)]
endmodule
