// Equal semantic Int children give #fun3 a unique admissible completion bound.
module PARAMETRIC-COMPLETION-LUB-CONTROL
  imports INT

  syntax Int ::= trigger() [function]
  rule trigger() => #fun(0 => 0)(0)
endmodule
