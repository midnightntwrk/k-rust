module CS12-MAP
  imports BOOL
  imports MAP
  imports BYTES
  imports INT
  configuration <k> $PGM:K </k> <store> b"k" |-> 1 </store>
  rule true => false
endmodule
