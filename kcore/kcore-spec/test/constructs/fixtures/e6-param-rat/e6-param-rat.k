// RAT's hooked function #Rat2Float (rat.md:226, hook FLOAT.rat2float), read as a parameter symbol
// of the definition's own (a builtin file's sentence about names no library text declares,
// Parse.isOwnBuiltin; no registry hook). RAT is a private module, so the text applies the
// function Rat2Float of RAT-SYNTAX, whose equations (rat.md:227-228) apply #Rat2Float, to
// variables; fixture.toml params records `kcore sem-fields`'s parameter lines.
requires "rat.md"
module E6-PARAM-RAT
  imports RAT
  imports INT
  imports FLOAT
  syntax KItem ::= go(Int, K, K, K) [symbol(go)]
  rule <k> go(1, X1:Rat, X2:Int, X3:Int) => Rat2Float(X1, X2, X3) ... </k>
endmodule
