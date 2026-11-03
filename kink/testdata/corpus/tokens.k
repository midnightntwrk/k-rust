// A token sort of the syntax module (Word) and one of the main module (Name) whose regex the
// scanner prefers for the same text: a variable's text is read with the syntax module's grammar
// first wherever it has the variable's sort.
module TOKENS-SYNTAX
  syntax Word ::= r"w[a-z]*" [token]
  syntax Pgm ::= "run" [symbol(run)]
endmodule

module TOKENS
  imports TOKENS-SYNTAX
  imports BASIC-K
  syntax Name ::= r"wor[a-z]*" [token, prec(2)]
  configuration <k> $PGM:Pgm </k> <w> $W:Word </w> <n> $N:Name </n>
endmodule
