module R3-G-05-ORDINARY-SYNTAX
  imports INT-SYNTAX
  imports STRING-SYNTAX
  imports LIST

  syntax Exp ::= Int
               | Exp "+" Exp [symbol(add), seqstrict]
               | "bump" [symbol(bump)]
               | "drop" [symbol(drop)]
  syntax KResult ::= Int
  syntax RuleOrigin ::= ruleOrigin(String, String, String, String, String)
  syntax TraceEvent ::= ruleApplied(RuleOrigin)
endmodule

module R3-G-05-ORDINARY
  imports R3-G-05-ORDINARY-SYNTAX
  imports INT
  imports LIST

  configuration
    <T>
      <k> $PGM:Exp </k>
      <state> 1 </state>
      <trace> .List </trace>
    </T>

  rule <k> bump => 0 ... </k>
       <state> I => I +Int 1 </state>
       <trace> TRACE => TRACE ListItem(ruleApplied(ruleOrigin(
         @@BUMP_ID@@, @@BUMP_LABEL@@, @@BUMP_MODULE@@, @@BUMP_SOURCE@@,
         @@BUMP_LOCATION@@))) </trace>
    requires I >=Int 0
    ensures I +Int 1 >Int 0
    [label(bump-state)]

  rule <k> drop => 0 ... </k>
       <state> I => I -Int 1 </state>
       <trace> TRACE => TRACE ListItem(ruleApplied(ruleOrigin(
         @@DROP_ID@@, @@DROP_LABEL@@, @@DROP_MODULE@@, @@DROP_SOURCE@@,
         @@DROP_LOCATION@@))) </trace>
    requires I >Int 0
    ensures I -Int 1 >=Int 0
    [label(drop-state)]

  rule I:Int + J:Int => I +Int J [label(add-values)]
endmodule
