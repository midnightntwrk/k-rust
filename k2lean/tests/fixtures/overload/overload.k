// Function equations over an overloaded list (k2lean/docs/design.md, section 2, "Overloads"):
// `Ids` is a subsort of `Exps` and the two `_,_` are overloaded, so a list of identifiers is the
// `Ids` term, which equals the `Exps` term `_,_(inj(X), inj(Xs))` by the overload axiom. An
// equation over `E, Es` therefore applies to it: `len(x, y)` is 2.
module OVERLOAD-SYNTAX
  imports DOMAINS-SYNTAX
  syntax Exp  ::= Int | Id
  syntax Ids  ::= List{Id,","}  [overload(exps)]
  syntax Exps ::= List{Exp,","} [overload(exps)]
  syntax Exps ::= Ids
  syntax Pgm  ::= run(Exps) [symbol(run)]
endmodule

module OVERLOAD
  imports OVERLOAD-SYNTAX
  imports DOMAINS
  configuration <k> $PGM:Pgm </k>

  // recursive, over the super list
  syntax Int ::= len(Exps) [function, total, symbol(len)]
  rule len(.Exps) => 0
  rule len(_E, Es) => 1 +Int len(Es)

  // not recursive, with an owise equation after the overloaded pattern
  syntax Int ::= hd(Exps) [function, total, symbol(hd)]
  rule hd(I:Int, _) => I
  rule hd(_:Id, _) => -1
  rule hd(_) => 0 [owise]

  rule <k> run(Es) => len(Es) ~> hd(Es) </k>
endmodule
