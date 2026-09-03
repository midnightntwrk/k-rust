module ENV-SORT
  syntax Env
endmodule

module ENV-PARSER
  imports ENV-SORT
  syntax Env ::= "selected" [symbol(selectedEnv)]
endmodule

module PARSER-SYNTAX
  syntax Pgm ::= "go" [symbol(go)]
endmodule

module PARSER
  imports ENV-PARSER
  imports PARSER-SYNTAX
  syntax Env ::= "main" [symbol(mainEnv)]
  configuration <k> $PGM:Pgm </k> <env parser="ENV, ENV-PARSER"> $ENV:Env </env>
endmodule
