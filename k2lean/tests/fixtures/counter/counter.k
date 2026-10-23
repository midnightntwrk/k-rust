requires "domains.md"

module COUNTER-SYNTAX
  imports INT-SYNTAX
  imports ID-SYNTAX
  syntax Stmt ::= Id "+=" Int ";" | "skip"
  syntax Pgm ::= List{Stmt, ""}
endmodule

module COUNTER
  imports COUNTER-SYNTAX
  imports INT
  imports MAP
  imports BOOL
  configuration <T> <k> $PGM:Pgm </k> <env> .Map </env> </T>

  syntax Int ::= get(Map, Id) [function, total]
  rule get(M, X) => {M[X]}:>Int requires X in_keys(M) andBool isInt(M[X])
  rule get(_, _) => 0 [owise]

  rule <k> S:Stmt Ss:Pgm => S ~> Ss ... </k>
  rule <k> .Pgm => .K ... </k>
  rule <k> X += I ; => .K ... </k> <env> M => M[X <- get(M, X) +Int I] </env> [label(incr)]
  rule <k> skip => .K ... </k> [priority(40)]
endmodule
