// The symbols kompile generates for a configuration and for the sorts: the initializer initXCell
// of each cell, the projection project:S of each sort, and the getter of the generated counter.
// <v> and <p> hold configuration variables below a cell of multiplicity *; the one rule names none
// of the generated symbols.
module T231-GENERATED-SYMBOL-DEFINITION-SYNTAX
  imports INT-SYNTAX
  syntax Cmd ::= go() [symbol(go)] | done() [symbol(done)]
endmodule

module T231-GENERATED-SYMBOL-DEFINITION
  imports T231-GENERATED-SYMBOL-DEFINITION-SYNTAX
  imports INT
  configuration <top> <k> $PGM:Cmd </k>
                      <ts> <t multiplicity="*" type="Set"> <v> $V:Int </v> <p> $P:Cmd </p> </t> </ts>
                </top>
  rule [go]: <k> go() => done() </k>
endmodule
