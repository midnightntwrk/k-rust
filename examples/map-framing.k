module MAP-FRAMING
  imports INT
  imports MAP

  syntax Val ::= "a" | "b" | "c"

  configuration
    <T>
      <k> $PGM:Val </k>
      <store> a |-> 1 b |-> 2 c |-> 3 </store>
    </T>

  rule
    <k> V:Val </k>
    <store> ((V |-> _) => .Map) REST:Map </store>
endmodule
