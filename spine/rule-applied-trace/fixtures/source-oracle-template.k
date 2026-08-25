module R3-G-01-SOURCE-ORACLE-SYNTAX
  imports INT-SYNTAX
  imports STRING-SYNTAX
  imports LIST

  syntax Exp ::= Int
               | Exp "+" Exp     [symbol(add), seqstrict]
               | "read" "(" ")" [symbol(read), function]
               | "start"         [symbol(start)]
               | "bump"          [symbol(bump)]
               | "hold" "(" Exp ")" [symbol(hold)]
  syntax KResult ::= Int
  syntax RuleOrigin ::= ruleOrigin(String, String, String, String, String)
  syntax TraceEvent ::= ruleApplied(RuleOrigin)
endmodule

module R3-G-01-SOURCE-ORACLE
  imports R3-G-01-SOURCE-ORACLE-SYNTAX
  imports INT
  imports LIST

  configuration
    <T>
      <k> $PGM:Exp </k>
      <state> 1 </state>
      <trace> .List </trace>
    </T>

  rule [[ read() => I ]]
       <state> I </state>
    [label(read-state)]
  rule start => read() + bump [label(start-program)]
  rule <k> bump => 0 ... </k>
       <state> I => I +Int 1 </state>
       <trace> TRACE:List => TRACE ListItem(ruleApplied(ruleOrigin(
         @ID@, @LABEL@, @MODULE@, @SOURCE@, @LOCATION@))) </trace>
    requires I >=Int 0
    ensures I +Int 1 >Int 0
    [label(bump-state)]
  rule I:Int + J:Int => I +Int J [label(add-values)]
  rule hold(I:Int) => I [label(hold-value)]
  context [hold-context]: hold(HOLE)
endmodule
