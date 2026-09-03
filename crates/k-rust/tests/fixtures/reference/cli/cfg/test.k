module CFG-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= Int | "done"
endmodule

module CFG
  imports CFG-SYNTAX
  imports INT
  syntax Int ::= two() [function]
  rule two() => 2
  configuration <k> $PGM:Pgm </k> <env> $ENV:Int </env>
  rule <k> P:Int => done </k> <env> E:Int => P +Int E </env>
endmodule
