module MAP-BUILD
  imports INT
  imports MAP
  configuration <k> $PGM:Int </k> <m> .Map </m>
  rule <k> N:Int => N -Int 1 ... </k> <m> M => M[N <- N] </m> requires N >Int 0
  rule <k> 0 => 0 -Int size(M) ... </k> <m> M => .Map </m>
endmodule
