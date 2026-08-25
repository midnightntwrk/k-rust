module R3-G-05-ALLOWLIST-SYNTAX
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

module R3-G-05-ALLOWLIST
  imports R3-G-05-ALLOWLIST-SYNTAX
  imports INT
  imports LIST

  configuration
    <T>
      <k> $PGM:Exp </k>
      <state> 1 </state>
    </T>

  rule <k> bump => 0 ... </k>
       <state> I => I +Int 1 </state>
    requires I >=Int 0
    ensures I +Int 1 >Int 0
    [label(bump-state)]

  rule <k> drop => 0 ... </k>
       <state> I => I -Int 1 </state>
    requires I >Int 0
    ensures I -Int 1 >=Int 0
    [label(drop-state)]

  rule I:Int + J:Int => I +Int J [label(add-values)]
endmodule
