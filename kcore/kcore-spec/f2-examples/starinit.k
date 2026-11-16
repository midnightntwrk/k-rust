// Configuration variables in cells below a cell of multiplicity `*`: their initializers are
// functions outside the top cell tree, whose equations apply `project:Int` (a library sort's
// projection) and `project:Cmd` (a user sort's). The reader numbers both from those equations.
module STARINIT-SYNTAX
  imports INT-SYNTAX
  syntax Cmd ::= go() [symbol(go)] | done() [symbol(done)]
endmodule

module STARINIT
  imports STARINIT-SYNTAX
  imports INT
  configuration <top> <k> $PGM:Cmd </k>
                      <ts> <t multiplicity="*" type="Set"> <v> $V:Int </v> <p> $P:Cmd </p> </t> </ts>
                </top>
  rule [go]: <k> go() => done() </k>
endmodule
