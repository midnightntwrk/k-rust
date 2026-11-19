// Grammar sentences as mutation sites (kink-patch tests/grammar.rs, PJ-34): a lexical
// declaration, a float-like token, a line-anchored token, a priority block with associativity,
// a separate priority declaration, and literals. The main module imports INT, whose hooked and
// `concrete` equations make an edit of unknown effect unsupported (ClaimSupport).
module GRAMMAR-SYNTAX
  syntax lexical Digit = r"[0-9]"
  syntax Num ::= r"{Digit}+([.]{Digit}*)?" [token]
  syntax Tag ::= r"#[a-z]+$" [token]
  syntax Exp ::= Num
               | "(" Exp ")" [bracket]
               > Exp "*" Exp [left, symbol(mul)]
               > Exp "+" Exp [left, symbol(add)]
               | "neg" Exp [symbol(neg)]
  syntax priority mul > neg
  syntax Stmt ::= "print" Exp ";" [symbol(print)]
                | "tag" Tag [symbol(tag)]
  syntax Note
endmodule

module GRAMMAR
  imports GRAMMAR-SYNTAX
  imports BASIC-K
  imports INT
  configuration <k> $PGM:Stmt </k>

  rule [run]: print _E ; => .K
endmodule
