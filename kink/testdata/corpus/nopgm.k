// A definition without $PGM: its configuration variables are all bound by name.
module NOPGM
  imports BOOL
  imports INT
  imports BASIC-K
  configuration <k> $ENTRY:K </k> <n> $N:Int </n>
  rule true => false
endmodule
