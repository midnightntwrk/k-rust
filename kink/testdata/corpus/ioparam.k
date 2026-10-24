// KINK-CENSUS-RUNLIST (fz26): a definition without stream cells that declares its own String
// variable named $IO; kink's stream-mode refusal applies only to definitions with stream cells.
module IOPARAM
  imports BOOL
  imports STRING
  imports BASIC-K
  configuration <k> $PGM:K </k> <io> $IO:String </io>
  rule true => false
endmodule
