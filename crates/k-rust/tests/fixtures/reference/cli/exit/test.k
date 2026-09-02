module EXIT
  imports INT
  configuration <k> $PGM:Int </k> <exit exit=""> 0 </exit>
  rule <k> N:Int => .K </k> <exit> _ => N </exit>
endmodule
