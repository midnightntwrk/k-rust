/-
  DONE-0 C1, list E4: every constructor of the reader's KORE syntax tree (kore-lean's `KSort`,
  `VarPattern`, `Pattern`, `Sentence`) has a row key of `test/constructs/rows.toml`. The functions
  below match on every constructor with no wildcard case, so a constructor added to the tree makes
  this file fail to elaborate; `test/constructs.sh` checks that the strings they return are exactly
  E4's `tree:` keys. Run from the package root: `lake env lean test/ConstructsE4.lean`.
-/
import KoreParser.AST

set_option autoImplicit false

namespace ConstructsE4

open Kore

def sortKey : KSort → String
  | .var _ => "tree:KSort.var"
  | .ctor _ _ => "tree:KSort.ctor"

def varKey : VarPattern → String
  | .evar _ => "tree:VarPattern.evar"
  | .svar _ => "tree:VarPattern.svar"

def patternKey : Pattern → String
  | .var _ => "tree:Pattern.var"
  | .app _ _ _ => "tree:Pattern.app"
  | .string _ => "tree:Pattern.string"
  | .top _ => "tree:Pattern.top"
  | .bottom _ => "tree:Pattern.bottom"
  | .not _ _ => "tree:Pattern.not"
  | .and _ _ => "tree:Pattern.and"
  | .or _ _ => "tree:Pattern.or"
  | .implies _ _ _ => "tree:Pattern.implies"
  | .iff _ _ _ => "tree:Pattern.iff"
  | .exist _ _ _ => "tree:Pattern.exist"
  | .forall _ _ _ => "tree:Pattern.forall"
  | .mu _ _ => "tree:Pattern.mu"
  | .nu _ _ => "tree:Pattern.nu"
  | .ceil _ _ _ => "tree:Pattern.ceil"
  | .floor _ _ _ => "tree:Pattern.floor"
  | .equals _ _ _ _ => "tree:Pattern.equals"
  | .in _ _ _ _ => "tree:Pattern.in"
  | .next _ _ => "tree:Pattern.next"
  | .rewrites _ _ _ => "tree:Pattern.rewrites"
  | .dv _ _ => "tree:Pattern.dv"
  | .leftAssoc _ _ _ => "tree:Pattern.leftAssoc"
  | .rightAssoc _ _ _ => "tree:Pattern.rightAssoc"

def sentenceKey : Sentence → String
  | .import _ => "tree:Sentence.import"
  | .sort _ => "tree:Sentence.sort"
  | .hookedSort _ => "tree:Sentence.hookedSort"
  | .symbol _ => "tree:Sentence.symbol"
  | .hookedSymbol _ => "tree:Sentence.hookedSymbol"
  | .alias _ => "tree:Sentence.alias"
  | .axiom _ => "tree:Sentence.axiom"
  | .claim _ => "tree:Sentence.claim"

end ConstructsE4
