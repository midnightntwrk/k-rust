// KINK-SC-DEFINED (fz26 P7-SIMPLE-KINK design): the prelude equation of findChar applies #if with
// skippable operands over the partial findString and findChar, but each such application is also
// evaluated by an operand that runs whenever it is skipped (an #if condition or the other branch),
// so no short-circuit reading changes its value. Before KINK-SC-DEFINED findChar was flagged and so
// was every rule applying it. Since CF-01 the prelude's replace and replaceAll are not flagged
// either: replace's owise equation negates Count >Int 0 andBool findString(..) >=Int 0, an andBool
// tree over atoms, which both readings make true at the same arguments (false versus \bottom
// elsewhere, and both leave the owise equation). Before CF-01 they were, for the skippable
// findString application no other operand evaluates; no rule here applies them.
module SCSTR-SYNTAX
  imports INT-SYNTAX
  imports STRING-SYNTAX
  syntax Prog ::= fc(String) [symbol(fc)] | res(Int) [symbol(res)]
endmodule
module SCSTR
  imports SCSTR-SYNTAX
  imports INT
  imports STRING
  configuration <k> $PGM:Prog </k>
  rule [fc]: <k> fc(S) => res(findChar(S, "ab", 0)) </k>
endmodule
