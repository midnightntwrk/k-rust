module STREAMS
  imports BOOL
  imports BASIC-K
  imports LIST
  configuration <k> $PGM:K </k> <in stream="stdin"> .List </in>
  rule true => false
endmodule
