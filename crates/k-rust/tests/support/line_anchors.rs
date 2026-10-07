//! Definitions whose token regexes carry line anchors, and the programs their `Pgm` parsers must
//! accept and reject. Both the in-process parser and the exported Flex/Bison parser are checked
//! against the same tables, so the two scanners k-rust builds give the anchors one meaning.
//!
//! Test binaries include this file with `#[path = "support/line_anchors.rs"] mod line_anchors;`.

/// `^` requires a token to start at the start of the text or right after a newline, `$` requires
/// a newline right after the token (the newline is not part of it), and both apply to the whole
/// alternation.
pub const DEFINITION: &str = r#"
module ANCHOR-SYNTAX
  syntax Foo ::= r"a$" [token]
  syntax Bar ::= r"^b" [token]
  syntax Baz ::= r"^c$" [token]
  syntax Alt ::= r"^d|e$" [token]
  syntax Short ::= r"x(\\ny)?$" [token]
  syntax Pgm ::= Foo | Bar | Baz | Alt | Short "y"
endmodule

module ANCHOR
  imports ANCHOR-SYNTAX
  configuration <k> $PGM:Pgm </k>
endmodule
"#;

/// `(program, accepted)` for the start sort `Pgm` of [`DEFINITION`].
pub const PROGRAMS: [(&str, bool); 22] = [
    // `a$`: a newline must follow; where the token starts does not matter.
    ("a\n", true),
    (" a\n", true),
    ("a", false),
    ("a \n", false),
    // `^b`: the token must start a line; what follows does not matter.
    ("b", true),
    ("b\n", true),
    ("\nb", true),
    (" b", false),
    // `^c$`: both.
    ("c\n", true),
    ("\nc\n", true),
    ("c", false),
    (" c\n", false),
    // `^d|e$` is `^(d|e)$`: both anchors constrain both alternatives.
    ("d\n", true),
    ("e\n", true),
    ("d", false),
    ("e", false),
    (" d\n", false),
    (" e\n", false),
    // `x(\ny)?$`: the token is the longest body match that a newline follows. In `x\ny` that
    // is `x`, although the body also matches the longer `x\ny`, which no newline follows; in
    // `x\ny\n` it is `x\ny`, which leaves no `y` for `Pgm`.
    ("x\ny", true),
    ("x\ny\n", false),
    ("xy", false),
    ("x", false),
];

/// Anchored candidates competing with other lexemes. The longest-match rule compares token
/// lengths, and the newline `$` requires is not part of the token (K user manual, "`prec`
/// attribute": longer tokens win, and precedence orders tokens of equal length), so `$` decides
/// only whether a candidate exists, never which of two equal-length tokens wins.
pub const TIE_DEFINITION: &str = r##"
module TIE-SYNTAX
  syntax #Layout ::= r"[\\ \\n]" [token] | r"e$" [token] | r"g$" [token]
  syntax Foo ::= r"a$" [token]
  syntax Bar ::= r"[a-z]+" [token]
  syntax Hi ::= r"b$" [token, prec(1)]
  syntax Cee ::= r"c$" [token]
  syntax Dee ::= r"d$" [token, prec(5)]
  syntax Nl ::= r"[de][\\n]" [token]
  syntax Pgm ::= Foo ";" | Bar "?" | Hi "!" | Cee "#" | "c" "%" | Dee "@" | Nl "&" | "?" | "!"
endmodule

module TIE
  imports TIE-SYNTAX
  configuration <k> $PGM:Pgm </k>
endmodule
"##;

/// `(program, accepted)` for the start sort `Pgm` of [`TIE_DEFINITION`].
pub const TIE_PROGRAMS: [(&str, bool); 17] = [
    // `a$` and `[a-z]+`, both precedence 0, on `a\n`: equal-length tokens, so the scanner's
    // fixed lexeme order picks `Bar` both times; a longer token wins regardless.
    ("a\n?", true),
    ("a\n;", false),
    ("ab\n?", true),
    // `b$` has the higher precedence, so it wins the tie where a newline follows.
    ("b\n!", true),
    ("b\n?", false),
    ("b?", true),
    ("b!", false),
    // A literal outranks the regex `c$` on the equal-length token `c`.
    ("c\n%", true),
    ("c\n#", false),
    // `[de][\n]` takes the newline into its token, so it is longer than `d$`'s token and wins
    // although `d$` has the higher precedence.
    ("d\n&", true),
    ("d\n@", false),
    // Likewise it is longer than the anchored layout `e$`'s match; where no newline follows,
    // `e` is not layout and is scanned as `Bar`.
    ("e\n&", true),
    ("e\n?", false),
    ("e ?", true),
    // Layout wins a tie with a token: `g` before a newline is layout, elsewhere `Bar`.
    ("g\n!", true),
    ("g!", false),
    ("g?", true),
];

/// Programs of [`DEFINITION`] whose `a$` token ends at or around a multiple of 8 KiB, where a
/// file-reading scanner's buffered input ends; each is `Foo` and accepted.
pub fn programs_with_a_token_at_a_buffer_boundary() -> Vec<String> {
    [8189, 8190, 8191, 8192, 16382, 16383, 16384]
        .into_iter()
        .map(|padding| format!("{}a\n", " ".repeat(padding)))
        .collect()
}
