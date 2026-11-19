// A module importing RAT-KORE (rat.md:115) and RAT-SYMBOLIC (rat.md:103) and not RAT (rat.md:130):
// the declarations of RAT-SYNTAX and RAT-COMMON, RAT-KORE's two equations (rat.md:125, :127) and
// RAT-SYMBOLIC's lemma (rat.md:108-112), and none of RAT's equations. RAT-KORE imports RAT-COMMON
// privately, so the text imports RAT-COMMON to apply <_,_>Rat; its rule applies _==Rat_ to it.
// RAT-SYNTAX's Rat2Float (rat.md:78) has result sort Float and RAT-SYNTAX imports no module
// declaring it; FLOAT-SYNTAX (domains.md:1493, the sort's hook and its tokens) declares it. Without
// it the sort Float is declared plain, under a registry sort's name (Parse's registrySortName).
requires "rat.md"
module E6-MOD-RAT-KORE
  imports RAT-COMMON
  imports RAT-KORE
  imports RAT-SYMBOLIC
  imports FLOAT-SYNTAX
  syntax KItem ::= go(Rat, Int, Int) [symbol(go)]
  rule <k> go(R, I, J) => R ==Rat < I , J >Rat ... </k>
endmodule
