module PARAMETER-CHOICE-PREFER
  imports INT
  syntax Item ::= Small
  syntax Small ::= small(Int)
  syntax Wrapped ::= f(Small) [prefer] | f(Item)
  syntax KItem ::= run(Wrapped)
  rule run(f(small(I) => small(I +Int 1)))
endmodule
