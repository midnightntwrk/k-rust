// Flow fixture (F-16): a specification with a macro. kompile emits the macro rule to
// `macros_kore` as a bare sentence, which kink-native's `equivalent_compilation` cannot parse
// as a definition (corpus-scale residue CS-T08), so a mutant that compiles equal to the
// baseline is the runner's mutant-scope `Infrastructure` failure (status error) on every host.
module MACRO-SYNTAX
  imports INT-SYNTAX
  syntax Exp ::= Int
               | Exp "+" Exp [strict, symbol(plus)]
               | "seven" [symbol(seven)]
endmodule

module MACRO
  imports MACRO-SYNTAX
  imports INT
  configuration <k> $PGM:Exp </k>

  syntax KResult ::= Int
  syntax Int ::= limit() [macro]
  rule limit() => 7
  rule [seven]: seven => limit()
  rule [plus]: I1:Int + I2:Int => I1 +Int I2
endmodule
