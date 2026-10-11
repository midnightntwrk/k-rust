// The regex-anchor-local case of scripts/reference-differential.toml parses this definition with
// the pinned kast and with krust; docs/compatibility.md#token-regex-line-anchors records where
// they differ.
module ANCHOR-SYNTAX
  syntax Foo ::= r"a$" [token]
  syntax Bar ::= r"^b" [token]
endmodule

module ANCHOR
  imports ANCHOR-SYNTAX
  configuration <k> $PGM:K </k>
endmodule
