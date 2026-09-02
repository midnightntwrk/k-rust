// reference: k/result/bin/kast --definition k-anchor --module ANCHOR-SYNTAX --sort Bar --expression $'b\n'
module ANCHOR-SYNTAX
  syntax Foo ::= r"a$" [token]
  syntax Bar ::= r"^b" [token]
endmodule

module ANCHOR
  imports ANCHOR-SYNTAX
  configuration <k> $PGM:K </k>
endmodule
