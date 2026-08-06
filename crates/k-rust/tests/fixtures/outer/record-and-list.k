requires "domains.md"

module OUTER-CORPUS
  imports public INT

  syntax Program ::= Set | List
  syntax Pair ::= pair(left: Int, right: Int) [symbol(pair)]
  syntax Exp ::= Int
               > left: Exp "+" Exp [symbol(_+_)]
               | "(" Exp ")" [bracket]
  syntax Exps ::= List{Exp, ","} [symbol(_,_), terminator-symbol(.Exps)]
  syntax Ints ::= NeList{Int, ","}
  syntax Exp ::= Exp "or" Exp [klabel(_or_)]
  syntax priority _or_ > _+_

  rule [identity]: X + 0 => X [simplification]
endmodule
