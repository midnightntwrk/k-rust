module MINI-PROOF
  syntax State ::= "start" | "middle" | "done" | "stuck"
  configuration <k> $PGM:State </k>
  rule <k> start => middle </k>
  rule <k> middle => done </k>
endmodule
