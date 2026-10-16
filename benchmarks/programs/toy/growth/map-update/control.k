module CTL
  imports INT
  configuration <k> $PGM:Int </k> <m> 0 </m>
  rule <k> N:Int => N -Int 1 ... </k> <m> M => M +Int 1 </m> requires N >Int 0
  rule <k> 0 => 0 -Int M ... </k> <m> M => 0 </m>
endmodule
