// A definition without a configuration declaration: K gives it `kast.md`'s default
// configuration, `configuration <k> $PGM:K </k>` (module DEFAULT-CONFIGURATION). kompile declares
// the cell `<k>` with that file's `Source`; the reader reads it as the definition's configuration
// cell (`Parse.isDefaultConfig`).
module DEFCFG-SYNTAX
  imports INT-SYNTAX
  syntax KItem ::= inc(Int) [symbol(inc)] | val(Int) [symbol(val)]
endmodule

module DEFCFG
  imports DEFCFG-SYNTAX
  imports INT
  rule [inc]: inc(N) => val(N +Int 1)
endmodule
