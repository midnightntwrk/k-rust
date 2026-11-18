// A function of the text under the label kompile gives a sort's projection, with no rule.
module RDR-PROJ-NORULE
  imports INT
  syntax Exp ::= a(Int) [symbol(a)] | pe(K) [function, symbol(project:Exp)]
endmodule
