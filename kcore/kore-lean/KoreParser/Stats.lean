/-
  Small total functions over the KORE AST (new in the k-rust port).
  Released under MIT license as described in the file LICENSE.

  They show the recursion shape later translations use:
  a function on `Pattern` mutually structural with one on `List Pattern`.
-/

import KoreParser.AST

set_option autoImplicit false

namespace Kore

/-- The name of a pattern's outermost construct. -/
def Pattern.topConnective : Pattern → String
  | .var (.evar _) => "evar"
  | .var (.svar _) => "svar"
  | .app .. => "app"
  | .string _ => "string"
  | .top _ => "\\top"
  | .bottom _ => "\\bottom"
  | .not .. => "\\not"
  | .and .. => "\\and"
  | .or .. => "\\or"
  | .implies .. => "\\implies"
  | .iff .. => "\\iff"
  | .exist .. => "\\exists"
  | .forall .. => "\\forall"
  | .mu .. => "\\mu"
  | .nu .. => "\\nu"
  | .ceil .. => "\\ceil"
  | .floor .. => "\\floor"
  | .equals .. => "\\equals"
  | .in .. => "\\in"
  | .next .. => "\\next"
  | .rewrites .. => "\\rewrites"
  | .dv .. => "\\dv"
  | .leftAssoc .. => "\\left-assoc"
  | .rightAssoc .. => "\\right-assoc"

mutual
  /-- The number of pattern nodes (sorts and variables' sorts not counted). -/
  def Pattern.size : Pattern → Nat
    | .var _ | .string _ | .top _ | .bottom _ | .dv .. => 1
    | .app _ _ args | .leftAssoc _ _ args | .rightAssoc _ _ args => 1 + Pattern.sizeList args
    | .and _ ps | .or _ ps => 1 + Pattern.sizeList ps
    | .not _ p | .exist _ _ p | .forall _ _ p | .mu _ p | .nu _ p
    | .ceil _ _ p | .floor _ _ p | .next _ p => 1 + p.size
    | .implies _ p q | .iff _ p q | .equals _ _ p q | .in _ _ p q | .rewrites _ p q =>
      1 + p.size + q.size
    termination_by structural p => p
  def Pattern.sizeList : List Pattern → Nat
    | [] => 0
    | p :: ps => p.size + Pattern.sizeList ps
    termination_by structural ps => ps
end

theorem Pattern.size_pos (p : Pattern) : 0 < p.size := by
  cases p <;> simp [Pattern.size] <;> omega

def Definition.axioms (d : Definition) : List Axiom :=
  d.modules.flatMap fun m => m.sentences.filterMap fun
    | .axiom a => some a
    | _ => none

def Definition.claims (d : Definition) : List Claim :=
  d.modules.flatMap fun m => m.sentences.filterMap fun
    | .claim c => some c
    | _ => none

def Definition.sentenceCount (d : Definition) : Nat :=
  d.modules.foldl (fun n m => n + m.sentences.length) 0

/-- Occurrences of each string, in order of first occurrence. -/
def tally (xs : List String) : List (String × Nat) :=
  xs.foldl (fun acc x =>
    if acc.any (·.1 == x) then acc.map fun (y, n) => if y == x then (y, n + 1) else (y, n)
    else acc ++ [(x, 1)]) []

/-- Axioms counted by their top connective. -/
def Definition.axiomsByTopConnective (d : Definition) : List (String × Nat) :=
  tally (d.axioms.map (·.pattern.topConnective))

/-- Total pattern nodes in the axioms. -/
def Definition.axiomNodes (d : Definition) : Nat :=
  d.axioms.foldl (fun n a => n + a.pattern.size) 0

/-! A kernel-checked computation on a small axiom, the shape of kompile's function equations. -/

private def R : KSort := .var ⟨⟨⟨"R"⟩⟩⟩
private def K : KSort := .ctor ⟨⟨"SortK"⟩⟩ []
private def x0 : Pattern := .var (.evar ⟨⟨⟨"X0"⟩⟩, K⟩)

example : (Pattern.implies R (.and R [.top R, .in K R x0 (.app ⟨⟨"dotk"⟩⟩ [] [])])
    (.equals K R (.app ⟨⟨"append"⟩⟩ [] [x0, x0]) x0)).size = 11 := by decide

example : (Pattern.implies R (.top R) (.bottom R)).topConnective = "\\implies" := rfl

end Kore
