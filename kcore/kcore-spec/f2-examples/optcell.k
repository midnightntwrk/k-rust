// An optional cell (`multiplicity="?"`): the sort OneCell of the cell `<one>` has two constructors,
// the cell and the constant `.OneCell` kompile writes for its absence, and the text states their
// distinctness (`\not(\and(.OneCell, <one>(Y0)))`, `[constructor]`).
module OPTCELL
  imports INT
  syntax Exp ::= a() [symbol(a)]
  configuration <t> <k> $PGM:Exp </k> <one multiplicity="?"> 0 </one> <ec> 0 </ec> </t>
endmodule
