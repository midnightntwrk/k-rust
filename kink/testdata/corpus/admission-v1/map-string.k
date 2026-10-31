module CS12-MAP-STRING
  imports BOOL
  imports MAP
  imports STRING
  imports INT
  configuration <k> $PGM:K </k> <store> "é" |-> 1 </store>
  rule true => false
endmodule
