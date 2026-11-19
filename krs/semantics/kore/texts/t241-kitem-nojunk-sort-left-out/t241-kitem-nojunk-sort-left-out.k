// A text with two sorts that have no subsort production into KItem written in it: KBott, which
// SORT-KBOTT declares with no production (kast.md:68-71), and the token sort #Tok, whose values are
// domain values, taken by the constructor tok. K makes every declared sort other than K and KItem
// a subsort of KItem; this entry rules on what the text and its KItem no-junk sentence state of
// the two.
module T241-KITEM-NOJUNK-SORT-LEFT-OUT
  imports SORT-KBOTT
  syntax #Tok [token]
  syntax Exp ::= tok(#Tok) [symbol(tok)]
endmodule
