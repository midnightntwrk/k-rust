module TEST
  imports INT
  syntax Pgm ::= "start" [symbol(start)]
  configuration <k> $PGM:Pgm </k> <n> 0 </n>
  rule <k> start => .K </k> <n> N => N +Int 1 </n>
  rule <k> start ... </k> <n> _:Int => 7 </n> [priority(200)]
endmodule
