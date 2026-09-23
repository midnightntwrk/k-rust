module PARAMETER-CHOICE-LOWERED
  imports INT
  syntax Item ::= Small
  syntax Small ::= small(Int)
  syntax Items ::= List{Item, ""}
  syntax KItem ::= run(Items)
  rule run((small(I) => small(I +Int 1)) _Rest)
endmodule
