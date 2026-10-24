// FZ-CONFLUENCE review A: `replace` (STRING.replace, no builtin step) gets a priority-10
// equation, so W(STRING.replaceAll) = replace(S, T, R, count(S, T)) is false here, and
// domains.md's replaceAll equation, whose rhs is W's, joins its hook pair although the builtin
// gives replaceAll("ab", "a", "c") = "cb" and the axioms give replace("ab", "a", "c", 1) = "ab".
// The theory equates "cb" with "ab". This side stores "cb".
module RP-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= go(Int)
endmodule
module RP
  imports RP-SYNTAX
  imports STRING
  imports INT
  rule replace(S, _, _, _) => S [priority(10)]
  configuration <k> $PGM:Pgm </k> <s> "" </s> <t> "" </t>
  rule <k> go(_) => .K </k> <s> _ => "cb" </s>
       <t> _ => replaceAll("ab", "a", "c") +String "|" +String replace("ab", "a", "c", 1) </t>
endmodule
