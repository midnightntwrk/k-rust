//! A definition whose token regexes carry line anchors, and the programs its `Pgm` parser must
//! accept and reject. Both the in-process parser and the exported Flex/Bison parser are checked
//! against the same table, so the two scanners k-rust builds give the anchors one meaning.
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
