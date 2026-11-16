/-
  The token stream of KORE text, for the round-trip test (new in the k-rust port).
  Released under MIT license as described in the file LICENSE.

  Whitespace and comments separate tokens and are dropped.
  A token is a punctuation mark (`{ } ( ) [ ] , : :=`), an identifier
  (maximal run of identifier characters, with its `\` or `@` prefix if any, keywords included),
  or a string literal, kept as its decoded code points.
-/

import KoreParser.Parser
import KoreParser.Printer

set_option autoImplicit false

namespace Kore

inductive Token where
  | punct (s : String)
  | ident (s : String)
  | str (s : String)
  deriving Repr, BEq, DecidableEq, Inhabited

instance : ToString Token where
  toString
    | .punct s => s
    | .ident s => s
    | .str s => Printer.strLit s

namespace Parsing

open Std.Internal.Parsec Std.Internal.Parsec.String

def token : Parsec Token := do
  match ← peek? with
  | some '"' => return .str (← strLit)
  | some ':' =>
    if ← (skipString ":=" *> pure true) <|> pure false then
      ws; return .punct ":="
    else
      skip; ws; return .punct ":"
  | some '\\' => do skip; return .ident ("\\" ++ (← lexeme rawIdent))
  | some '@' => do skip; return .ident ("@" ++ (← lexeme rawIdent))
  | some c =>
    if "{}()[],".contains c then do skip; ws; return .punct c.toString
    else return .ident (← lexeme rawIdent)
  | none => fail "unexpected end of input"

partial def tokensRest (acc : Array Token) : Parsec (Array Token) := do
  if ← isEof then return acc else tokensRest (acc.push (← token))

end Parsing

def tokenize (input : String) : Except String (Array Token) :=
  (Parsing.ws *> Parsing.tokensRest #[]).run input

end Kore
