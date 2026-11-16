/-
  Printer from the KORE AST to KORE text (new in the k-rust port; upstream had none).
  Released under MIT license as described in the file LICENSE.

  Every function is total and structurally recursive.
  The layout is one sentence per line with each pattern on that line;
  `parse (print d) = d` is what the round-trip test checks.
-/

import KoreParser.AST

set_option autoImplicit false

namespace Kore.Printer

/-! ## String literals -/

private def hexDigits (width n : Nat) : String :=
  let ds := Nat.toDigits 16 n
  String.ofList (List.replicate (width - ds.length) '0' ++ ds)

/-- The escaped form of one code point inside a string literal:
printable ASCII other than `"` and `\` as itself, the named escapes `\t \n \f \r \" \\`,
and otherwise the shortest of `\xhh`, `\uhhhh`, `\Uhhhhhhhh` that holds the code point. -/
def escapeChar (c : Char) : String :=
  match c with
  | '\t' => "\\t"
  | '\n' => "\\n"
  | '\x0c' => "\\f"
  | '\r' => "\\r"
  | '"' => "\\\""
  | '\\' => "\\\\"
  | c =>
    let n := c.toNat
    if 0x20 ≤ n ∧ n ≤ 0x7E then c.toString
    else if n ≤ 0xFF then "\\x" ++ hexDigits 2 n
    else if n ≤ 0xFFFF then "\\u" ++ hexDigits 4 n
    else "\\U" ++ hexDigits 8 n

def strLit (s : String) : String :=
  "\"" ++ String.join (s.toList.map escapeChar) ++ "\""

/-! ## Sorts, variables -/

mutual
  def sort : KSort → String
    | .var v => toString v
    | .ctor head args => toString head ++ "{" ++ sorts args ++ "}"
    termination_by structural s => s
  /-- Comma-separated sorts. -/
  def sorts : List KSort → String
    | [] => ""
    | s :: ss => sort s ++ sortsTail ss
    termination_by structural ss => ss
  def sortsTail : List KSort → String
    | [] => ""
    | s :: ss => ", " ++ sort s ++ sortsTail ss
    termination_by structural ss => ss
end

def sortVars (vs : List SortVar) : String :=
  "{" ++ ", ".intercalate (vs.map toString) ++ "}"

def evar (x : EVar) : String := toString x.var ++ ":" ++ sort x.sort

def svar (X : SVar) : String := "@" ++ toString X.var ++ ":" ++ sort X.sort

def varPattern : VarPattern → String
  | .evar x => evar x
  | .svar X => svar X

/-! ## Patterns -/

mutual
  def pattern : Pattern → String
    | .var v => varPattern v
    | .app h ss args => toString h ++ "{" ++ sorts ss ++ "}(" ++ patterns args ++ ")"
    | .string s => strLit s
    | .top s => "\\top{" ++ sort s ++ "}()"
    | .bottom s => "\\bottom{" ++ sort s ++ "}()"
    | .not s p => "\\not{" ++ sort s ++ "}(" ++ pattern p ++ ")"
    | .and s ps => "\\and{" ++ sort s ++ "}(" ++ patterns ps ++ ")"
    | .or s ps => "\\or{" ++ sort s ++ "}(" ++ patterns ps ++ ")"
    | .implies s p q => "\\implies{" ++ sort s ++ "}(" ++ pattern p ++ ", " ++ pattern q ++ ")"
    | .iff s p q => "\\iff{" ++ sort s ++ "}(" ++ pattern p ++ ", " ++ pattern q ++ ")"
    | .exist s x p => "\\exists{" ++ sort s ++ "}(" ++ evar x ++ ", " ++ pattern p ++ ")"
    | .forall s x p => "\\forall{" ++ sort s ++ "}(" ++ evar x ++ ", " ++ pattern p ++ ")"
    | .mu X p => "\\mu{}(" ++ svar X ++ ", " ++ pattern p ++ ")"
    | .nu X p => "\\nu{}(" ++ svar X ++ ", " ++ pattern p ++ ")"
    | .ceil s t p => "\\ceil{" ++ sort s ++ ", " ++ sort t ++ "}(" ++ pattern p ++ ")"
    | .floor s t p => "\\floor{" ++ sort s ++ ", " ++ sort t ++ "}(" ++ pattern p ++ ")"
    | .equals s t p q =>
      "\\equals{" ++ sort s ++ ", " ++ sort t ++ "}(" ++ pattern p ++ ", " ++ pattern q ++ ")"
    | .in s t p q =>
      "\\in{" ++ sort s ++ ", " ++ sort t ++ "}(" ++ pattern p ++ ", " ++ pattern q ++ ")"
    | .next s p => "\\next{" ++ sort s ++ "}(" ++ pattern p ++ ")"
    | .rewrites s p q => "\\rewrites{" ++ sort s ++ "}(" ++ pattern p ++ ", " ++ pattern q ++ ")"
    | .dv s v => "\\dv{" ++ sort s ++ "}(" ++ strLit v ++ ")"
    | .leftAssoc h ss args =>
      "\\left-assoc{}(" ++ toString h ++ "{" ++ sorts ss ++ "}(" ++ patterns args ++ "))"
    | .rightAssoc h ss args =>
      "\\right-assoc{}(" ++ toString h ++ "{" ++ sorts ss ++ "}(" ++ patterns args ++ "))"
    termination_by structural p => p
  /-- Comma-separated patterns. -/
  def patterns : List Pattern → String
    | [] => ""
    | p :: ps => pattern p ++ patternsTail ps
    termination_by structural ps => ps
  def patternsTail : List Pattern → String
    | [] => ""
    | p :: ps => ", " ++ pattern p ++ patternsTail ps
    termination_by structural ps => ps
end

def attributes (attrs : List AppPattern) : String :=
  "[" ++ patterns (attrs.map AppPattern.toPattern) ++ "]"

/-! ## Sentences, modules, definitions -/

def symbolOrAlias (s : SymbolOrAlias) : String :=
  toString s.ident ++ sortVars s.sortVars

def declaration (s : SymbolOrAlias) (args : List KSort) (result : KSort) : String :=
  symbolOrAlias s ++ "(" ++ sorts args ++ ") : " ++ sort result

def sentence : Sentence → String
  | .import i => "import " ++ toString i.module ++ " " ++ attributes i.attributes
  | .sort s => "sort " ++ toString s.sort ++ sortVars s.sortVars ++ " " ++ attributes s.attributes
  | .hookedSort s =>
    "hooked-sort " ++ toString s.sort ++ sortVars s.sortVars ++ " " ++ attributes s.attributes
  | .symbol s =>
    "symbol " ++ declaration s.symbol.toSymbolOrAlias s.sorts s.sort ++ " " ++ attributes s.attributes
  | .hookedSymbol s =>
    "hooked-symbol " ++ declaration s.symbol.toSymbolOrAlias s.sorts s.sort ++ " "
      ++ attributes s.attributes
  | .alias a =>
    "alias " ++ declaration a.alias.toSymbolOrAlias a.sorts a.sort ++ " where "
      ++ pattern a.app.toPattern ++ " := " ++ pattern a.body ++ " " ++ attributes a.attributes
  | .axiom a => "axiom" ++ sortVars a.sortVars ++ " " ++ pattern a.pattern ++ " " ++ attributes a.attributes
  | .claim c => "claim" ++ sortVars c.sortVars ++ " " ++ pattern c.pattern ++ " " ++ attributes c.attributes

def module (m : Module) : String :=
  "module " ++ toString m.name ++ "\n"
    ++ String.join (m.sentences.map fun s => "  " ++ sentence s ++ "\n")
    ++ "endmodule " ++ attributes m.attributes ++ "\n"

def definition (d : Definition) : String :=
  attributes d.attributes ++ "\n" ++ String.join (d.modules.map module)

end Kore.Printer
