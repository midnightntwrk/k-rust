// Re-pin R0c deliverable 2 (R0b review 1 major 2, the reviewer's probe): `Base2String`'s letter
// case "is determined by the backend" (domains.md:1829-1831); k-rust evaluates it in lower case.
module BASE16-SYNTAX
  imports INT-SYNTAX
  imports STRING-SYNTAX
  syntax Prog ::= start(Int) [symbol(start)]
                | str(String) [symbol(str)]
endmodule
module BASE16
  imports BASE16-SYNTAX
  imports INT
  imports STRING
  configuration <k> $PGM:Prog </k>
  rule [start]: <k> start(I) => str(Base2String(I, 16)) </k>
endmodule
