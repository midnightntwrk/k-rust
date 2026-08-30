module OWISE-FUNCTIONS
  imports INT

  syntax Int ::= "classify" "(" Int ")" [function]
  rule classify(0) => 1
  rule classify(_) => 2 [owise]
endmodule
