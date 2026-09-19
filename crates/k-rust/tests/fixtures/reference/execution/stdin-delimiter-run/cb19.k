module CB19-SYNTAX
  imports DOMAINS-SYNTAX
  syntax Stmt ::= "read" ";" | Stmt Stmt [left]
endmodule
module CB19
  imports CB19-SYNTAX
  imports DOMAINS
  configuration <T> <k> $PGM:Stmt </k> <in stream="stdin"> .List </in> <out stream="stdout"> .List </out> </T>
  rule S1:Stmt S2:Stmt => S1 ~> S2
  rule <k> read; => .K ...</k> <in> ListItem(I:Int) => .List ...</in> <out>... .List => ListItem(I) </out>
endmodule
