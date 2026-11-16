/-
  Copyright (c) 2023 Institute for Logic and Data Science (ILDS). All rights reserved.
  Released under MIT license as described in the file LICENSE.
  Authors: Horațiu Cheval

  Parser for Kore,
  following closely the syntax from: `https://github.com/runtimeverification/haskell-backend/blob/master/docs/kore-syntax.md`.

  Ported to Lean v4.34.0 for k-rust (2026-11): `Lean.Data.Parsec` became `Std.Internal.Parsec`;
  the other changes are listed in README.md.
-/

import Std.Internal.Parsec
import KoreParser.AST

set_option autoImplicit true
set_option relaxedAutoImplicit false

namespace Kore

open Std.Internal.Parsec Std.Internal.Parsec.String

namespace Parsing

abbrev Parsec := Std.Internal.Parsec.String.Parser

section Utils

/-- Skips whitespace and comments (`// …` to end of line, `/* … */` non-nested),
which the KORE lexical structure treats as whitespace. -/
partial def ws : Parsec Unit := do
  Std.Internal.Parsec.String.ws
  if ← (skipString "//" *> pure true) <|> pure false then
    let _ ← manyChars (satisfy (· != '\n'))
    ws
  else if ← (skipString "/*" *> pure true) <|> pure false then
    blockCommentRest
    ws
  else
    pure ()
where
  blockCommentRest : Parsec Unit := do
    if ← (skipString "*/" *> pure true) <|> pure false then pure ()
    else
      skip
      blockCommentRest

def lexeme (p : Parsec α) : Parsec α :=
  p <* ws

def lexchar : Char → Parsec Char :=
  lexeme ∘ pchar

def comma : Parsec Char :=
  lexchar ','

def between (left : Parsec α) (right : Parsec β) (p : Parsec γ) : Parsec γ := do
  let _ ← left
  let x ← p
  let _ ← right
  return x

def curly : Parsec α → Parsec α :=
  between (lexchar '{') (lexchar '}')

def parens : Parsec α → Parsec α :=
  between (lexchar '(') (lexchar ')')

def squares : Parsec α → Parsec α :=
  between (lexchar '[') (lexchar ']')

/-- `p (sep p)*`; `sep` decides whether another item follows. -/
def sepBy1 (p : Parsec α) (sep : Parsec β) : Parsec (List α) := do
  let x ← p
  let xs ← many (do let _ ← sep; p)
  return x :: xs.toList

/-- Zero or more `p` separated by `sep`, inside a delimiter that ends with `close`. -/
def sepByUntil (close : Char) (p : Parsec α) (sep : Parsec β) : Parsec (List α) := do
  if (← peek?) == some close then return [] else sepBy1 p sep

def sepByExactly2 (p₁ : Parsec α) (p₂ : Parsec β) (sep : Parsec γ) : Parsec (α × β) := do
  let a ← p₁
  let _ ← sep
  let b ← p₂
  return (a, b)

end Utils

/-! ## String literals -/

def hexValue (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- `n` hexadecimal digits naming one Unicode scalar value (no surrogate, at most U+10FFFF). -/
def hexCodePoint (n : Nat) : Parsec Char := do
  let mut v := 0
  for _ in [0:n] do
    let c ← any
    match hexValue c with
    | some d => v := 16 * v + d
    | none => fail s!"invalid hexadecimal digit '{c}' in escape"
  if v.isValidChar then return Char.ofNat v
  else fail s!"escape names no Unicode scalar value: {v}"

/-- The body of a string literal after its opening quote, decoded:
printable ASCII other than `"` and `\` stands for itself, and each escape names one code point. -/
partial def strLitBody (acc : String) : Parsec String := do
  let c ← any
  if c == '"' then return acc
  else if c == '\\' then
    let e ← any
    match e with
    | 't' => strLitBody (acc.push '\t')
    | 'n' => strLitBody (acc.push '\n')
    | 'f' => strLitBody (acc.push '\x0c')
    | 'r' => strLitBody (acc.push '\r')
    | '"' => strLitBody (acc.push '"')
    | '\\' => strLitBody (acc.push '\\')
    | 'x' => strLitBody (acc.push (← hexCodePoint 2))
    | 'u' => strLitBody (acc.push (← hexCodePoint 4))
    | 'U' => strLitBody (acc.push (← hexCodePoint 8))
    | _ => fail s!"unknown escape \\{e}"
  else if 0x20 ≤ c.toNat ∧ c.toNat ≤ 0x7E then strLitBody (acc.push c)
  else fail s!"character U+{String.ofList (Nat.toDigits 16 c.toNat)} outside printable ASCII in a string literal"

def strLit : Parsec String := lexeme do
  skipChar '"'
  strLitBody ""

/-! ## Identifiers -/

def isKIdentFirstChar (c : Char) : Bool :=
  ('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z')

def isKIdentOtherChar (c : Char) : Bool :=
  isKIdentFirstChar c || ('0' ≤ c ∧ c ≤ '9') || c == '\'' || c == '-'

/-- The longest identifier at the current position, without trailing whitespace. -/
def rawIdent : Parsec String := attempt do
  let first ← satisfy isKIdentFirstChar
  let other ← manyChars (satisfy isKIdentOtherChar)
  return first.toString ++ other

def isKeyword (str : String) :=
  [
      "module" , "endmodule"
    , "import"
    , "sort"   , "hooked-sort"
    , "symbol" , "hooked-symbol"
    , "axiom"  , "claim"
    , "alias"  , "where"
  ].contains str

def keyword (kw : String) : Parsec Unit := lexeme <| attempt do
  let str ← rawIdent
  if str == kw then return () else fail s!"keyword {kw} expected"

def kident : Parsec Identifier := lexeme <| attempt do
  let ident ← rawIdent
  if !isKeyword ident then return ⟨ident⟩ else fail s! "{ident} is a keyword"

def symbolIdent : Parsec SymbolIdent := do
  return ⟨← kident⟩

def evarIdent : Parsec EVarIdent := do
  return ⟨← kident⟩

def svarIdent : Parsec SVarIdent := do
  let _ ← pchar '@'
  return ⟨← kident⟩

def sortIdent : Parsec SortIdent := do
  return ⟨← kident⟩

def moduleName : Parsec ModuleName := do
  return ⟨← kident⟩

def sortVar : Parsec SortVar := do
  return ⟨← sortIdent⟩

def sortVars : Parsec (List SortVar) :=
  curly <| sepByUntil '}' sortVar comma

/-! ## Sorts and variables -/

/-- `S{…}` is a sort constructor applied to sorts, `S` a sort variable. -/
partial def ksort : Parsec KSort := do
  let ident ← sortIdent
  if (← peek?) == some '{' then
    return .ctor ident (← curly <| sepByUntil '}' ksort comma)
  else
    return .var ⟨ident⟩

def ksorts : Parsec (List KSort) :=
  curly <| sepByUntil '}' ksort comma

def evar : Parsec EVar := do
  let ident ← evarIdent
  let _ ← lexchar ':'
  let sort ← ksort
  return ⟨ident, sort⟩

def svar : Parsec SVar := do
  let ident ← svarIdent
  let _ ← lexchar ':'
  let sort ← ksort
  return ⟨ident, sort⟩

/-! ## Patterns

The first character decides the production:
`"` a string literal, `@` a set variable, `\` a matching-logic connective (or a `\`-prefixed symbol),
and an identifier is an element variable when `:` follows it and an application otherwise. -/

mutual

  partial def pattern : Parsec Pattern := do
    match ← peek? with
    | some '"' => return .string (← strLit)
    | some '@' => return .var (.svar (← svar))
    | some '\\' => backslashPattern
    | _ =>
      let ident ← kident
      if (← peek?) == some ':' then
        let _ ← lexchar ':'
        return .var (.evar ⟨⟨ident⟩, ← ksort⟩)
      else
        appRest ⟨ident⟩

  partial def patterns : Parsec (List Pattern) :=
    parens <| sepByUntil ')' pattern comma

  /-- The sorts and arguments of an application whose symbol is already read. -/
  partial def appRest (symbol : SymbolIdent) : Parsec Pattern := do
    let sorts ← ksorts
    let args ← patterns
    return .app symbol sorts args

  partial def appPattern : Parsec AppPattern := do
    let symbol ← if (← peek?) == some '\\' then
        (do skipChar '\\'; let id ← lexeme rawIdent; pure (⟨⟨"\\" ++ id⟩⟩ : SymbolIdent))
      else symbolIdent
    match ← appRest symbol with
    | .app h s a => return ⟨h, s, a⟩
    | _ => fail "application pattern expected"

  partial def sortArg : Parsec KSort :=
    curly ksort

  partial def sortArgs2 : Parsec (KSort × KSort) :=
    curly <| sepByExactly2 ksort ksort comma

  partial def patternArg : Parsec Pattern :=
    parens pattern

  partial def patternArgs2 : Parsec (Pattern × Pattern) :=
    parens <| sepByExactly2 pattern pattern comma

  /-- A pattern whose first token starts with `\`: read the name, then its arguments. -/
  partial def backslashPattern : Parsec Pattern := do
    skipChar '\\'
    let name ← lexeme rawIdent
    match name with
    | "top" => do
      let s ← sortArg; parens (pure ()); return .top s
    | "bottom" => do
      let s ← sortArg; parens (pure ()); return .bottom s
    | "not" => return .not (← sortArg) (← patternArg)
    | "and" => return .and (← sortArg) (← patterns)
    | "or" => return .or (← sortArg) (← patterns)
    | "implies" => do
      let s ← sortArg; let (p, q) ← patternArgs2; return .implies s p q
    | "iff" => do
      let s ← sortArg; let (p, q) ← patternArgs2; return .iff s p q
    | "exists" => do
      let s ← sortArg; let (x, p) ← parens <| sepByExactly2 evar pattern comma
      return .exist s x p
    | "forall" => do
      let s ← sortArg; let (x, p) ← parens <| sepByExactly2 evar pattern comma
      return .forall s x p
    | "mu" => do
      let _ ← curly (pure ()); let (X, p) ← parens <| sepByExactly2 svar pattern comma
      return .mu X p
    | "nu" => do
      let _ ← curly (pure ()); let (X, p) ← parens <| sepByExactly2 svar pattern comma
      return .nu X p
    | "ceil" => do
      let (s, t) ← sortArgs2; return .ceil s t (← patternArg)
    | "floor" => do
      let (s, t) ← sortArgs2; return .floor s t (← patternArg)
    | "equals" => do
      let (s, t) ← sortArgs2; let (p, q) ← patternArgs2; return .equals s t p q
    | "in" => do
      let (s, t) ← sortArgs2; let (p, q) ← patternArgs2; return .in s t p q
    | "next" => return .next (← sortArg) (← patternArg)
    | "rewrites" => do
      let s ← sortArg; let (p, q) ← patternArgs2; return .rewrites s p q
    | "dv" => return .dv (← sortArg) (← parens strLit)
    | "left-assoc" => do
      let _ ← curly (pure ()); let a ← parens appPattern
      return .leftAssoc a.head a.sorts a.args
    | "right-assoc" => do
      let _ ← curly (pure ()); let a ← parens appPattern
      return .rightAssoc a.head a.sorts a.args
    | _ => appRest ⟨⟨"\\" ++ name⟩⟩
end

def kattribute : Parsec AppPattern :=
  appPattern

def kattributes : Parsec (List AppPattern) :=
  squares <| sepByUntil ']' kattribute comma

/-! ## Sentences -/

def symbolOrAlias : Parsec SymbolOrAlias := do
  let ident ← if (← peek?) == some '\\' then
      (do skipChar '\\'; let id ← lexeme rawIdent; pure (⟨⟨"\\" ++ id⟩⟩ : SymbolIdent))
    else symbolIdent
  return ⟨ident, ← sortVars⟩

def symbolDecl : Parsec (SymbolOrAlias × List KSort × KSort × List AppPattern) := do
  let head ← symbolOrAlias
  let sortArgs ← parens <| sepByUntil ')' ksort comma
  let sort ← lexchar ':' *> ksort
  let attrs ← kattributes
  return (head, sortArgs, sort, attrs)

def sentenceAlias : Parsec SentenceAlias := do
  let alias ← symbolOrAlias
  let sortArgs ← parens <| sepByUntil ')' ksort comma
  let sort ← lexchar ':' *> ksort
  let dfnHead ← keyword "where" *> appPattern
  let _ ← lexeme (skipString ":=")
  let dfnBody ← pattern
  let attrs ← kattributes
  return ⟨⟨alias⟩, sortArgs, sort, dfnHead, dfnBody, attrs⟩

/-- A sentence, or `none` at `endmodule`. -/
def sentence? : Parsec (Option Sentence) := do
  let kw ← lexeme rawIdent
  match kw with
  | "endmodule" => return none
  | "import" => return some (.import ⟨← moduleName, ← kattributes⟩)
  | "sort" => return some (.sort ⟨← sortIdent, ← sortVars, ← kattributes⟩)
  | "hooked-sort" => return some (.hookedSort ⟨← sortIdent, ← sortVars, ← kattributes⟩)
  | "symbol" =>
    let (h, args, s, attrs) ← symbolDecl
    return some (.symbol ⟨⟨h⟩, args, s, attrs⟩)
  | "hooked-symbol" =>
    let (h, args, s, attrs) ← symbolDecl
    return some (.hookedSymbol ⟨⟨h⟩, args, s, attrs⟩)
  | "alias" => return some (.alias (← sentenceAlias))
  | "axiom" => return some (.axiom ⟨← sortVars, ← pattern, ← kattributes⟩)
  | "claim" => return some (.claim ⟨← sortVars, ← pattern, ← kattributes⟩)
  | _ => fail s!"sentence keyword or endmodule expected, found {kw}"

partial def sentences (acc : Array Sentence) : Parsec (List Sentence) := do
  match ← sentence? with
  | none => return acc.toList
  | some s => sentences (acc.push s)

def module : Parsec Module := do
  let moduleName ← keyword "module" *> moduleName
  let sentences ← sentences #[]
  let attrs ← kattributes
  return ⟨moduleName, sentences, attrs⟩

def definition : Parsec Definition := do
  ws
  let attrs ← kattributes
  let modules ← many1 module
  eof
  return ⟨attrs, modules.toList⟩

end Parsing

def parseDefinition (input : String) : Except String Definition :=
  Parsing.definition.run input

def parsePattern (input : String) : Except String Pattern :=
  (Parsing.ws *> Parsing.pattern <* eof).run input

def parseFile (fpath : System.FilePath) : IO (Except String Definition) := do
  let input ← IO.FS.readFile fpath
  return parseDefinition input

end Kore
