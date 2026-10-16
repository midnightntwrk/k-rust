module NULL1
  imports INT
  syntax Opt ::= "" [klabel(none), symbol] | "q" [klabel(someq), symbol]
  syntax Exp ::= Int | Opt Exp Opt [klabel(wrap), symbol] | Exp "+" Exp [left, klabel(plus), symbol] | "(" Exp ")" [bracket]
  syntax KItem ::= e(Exp)
  rule e(q 1 + 2 q) => e(3)
  rule e(( 1 ) + q 2) => .K
endmodule
