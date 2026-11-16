// Overloads that keep the result sort (`as` at Medium over `as` at Small, both of sort Large) and
// that keep the argument sort (`from` at Medium over `from` at Small, both of argument Small), as
// the corpus's overload-constructors, with Small inhabited (`one`). kompile also states the
// distinctness of `asMedium` and `asSmall`, which the overload `asMedium(inj{Small,Medium}(K)) =
// asSmall(K)` contradicts at every element of Small.
module OVLCONF-SYNTAX
  syntax Small ::= "one" [symbol(one)]
  syntax Medium ::= Small
  syntax Large ::= Medium
  syntax Small ::= narrow(Small) [symbol(narrow), overload(narrow)]
  syntax Medium ::= narrow(Medium) [symbol(wide), overload(narrow)]
  syntax Large ::= narrow(Large) [symbol(widest), overload(narrow)]
  syntax Large ::= as(Small) [symbol(asSmall), overload(as)]
  syntax Large ::= as(Medium) [symbol(asMedium), overload(as)]
  syntax Small ::= from(Small) [symbol(fromSmall), overload(from)]
  syntax Medium ::= from(Small) [symbol(fromMedium), overload(from)]
endmodule

module OVLCONF
  imports OVLCONF-SYNTAX
  configuration <k> $PGM:Large </k>
endmodule
