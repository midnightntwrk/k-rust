// Extracted from K's regression-new/fun-llvm/fun-test.k at revision 4a46d1231473b599c699160132fd6e76a5c46406.
module FUN-INT-LIST-CONFIG
  imports INT
  imports MAP

  configuration
    <k> $PGM:KItem </k>
    <cell> .Map </cell>

  syntax IntList ::= List{Int, ""}

  syntax KItem ::= callFunIntListAndConfig()
  rule callFunIntListAndConfig() => funIntListAndConfig()

  syntax Int ::= funIntListAndConfig() [function]
  rule [[ funIntListAndConfig() => #fun(_V1 => 0)(.IntList) ]]
    <cell> _M </cell>
endmodule
