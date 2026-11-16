/-
  Reading KORE: attributes, locations, sort names, an equation's argument patterns and premise.
  Reviewed layer: `parse` reads the KORE text with them (kept from F0's Parse when F0 was
  removed, P1.4).
-/
import KcoreSpec.Kore.Build

set_option autoImplicit false

namespace KoreAML.Parse

def dropPrefix? (pre s : String) : Option String :=
  let p := pre.toList
  let l := s.toList
  if l.take p.length == p then some (String.ofList (l.drop p.length)) else none

def sortName? : Kore.KSort → Option String
  | .ctor h [] => dropPrefix? "Sort" h.ident.name
  | _ => none

def attrStr? (as : List Kore.AppPattern) (n : String) : Option String :=
  match as.find? (·.head.ident.name == n) with
  | some ⟨_, [], [.string v]⟩ => some v
  | _ => none

def hasAttr (as : List Kore.AppPattern) (n : String) : Bool := as.any (·.head.ident.name == n)

def digits : List Char → Option Nat
  | [] => none
  | cs => cs.foldl (fun acc c => acc.bind fun n =>
      if c.isDigit then some (10 * n + (c.toNat - '0'.toNat)) else none) (some 0)

/-- Split at commas. -/
def splitComma : List Char → List (List Char)
  | [] => [[]]
  | c :: cs => if c == ',' then [] :: splitComma cs else match splitComma cs with
    | w :: ws => (c :: w) :: ws
    | [] => [[c]]

def loc? (as : List Kore.AppPattern) : Option Loc := do
  let s ← attrStr? as "org'Stop'kframework'Stop'attributes'Stop'Location"
  let body ← dropPrefix? "Location(" s
  match splitComma body.toList.dropLast with
  | [a, b, c, e] => pure ⟨← digits a, ← digits b, ← digits c, ← digits e⟩
  | _ => none

def source? (as : List Kore.AppPattern) : Option String := do
  let s ← attrStr? as "org'Stop'kframework'Stop'attributes'Stop'Source"
  let body ← dropPrefix? "Source(" s
  pure (String.ofList body.toList.dropLast)

def info? (as : List Kore.AppPattern) : Option Meta := do
  pure ⟨← attrStr? as "UNIQUE'Unds'ID", ← loc? as⟩

/-- The fuel of `argPats`, `disjuncts` and `binders` (they recurse into the last argument of a
`\and`, `\or` or `\exists`): the most arguments, `owise` competitors (clauses before an `owise`
clause) and exclusion binders one equation may have. It was 100 until M1.6, which met a function
with 299 clauses before its `owise` clause (findings/M1.6-scale-probe.md). Running out only makes
an equation not read as one, never read as something else: `classify` then refuses it. -/
def eqnFuel : Nat := 100000

/-- The patterns of kompile's argument conjunction `\and(\in(X0, p₀), \and(…, \top))`. -/
def argPats : Nat → Kore.Pattern → Option (List Kore.Pattern)
  | _, .top _ => some []
  | fuel + 1, .and _ [.in _ _ _ p, rest] => do pure (p :: (← argPats fuel rest))
  | _, _ => none

/-- The disjuncts of `\or(e₁, \or(…, \bottom))`. -/
def disjuncts : Nat → Kore.Pattern → Option (List Kore.Pattern)
  | _, .bottom _ => some []
  | fuel + 1, .or _ [e, rest] => do pure (e :: (← disjuncts fuel rest))
  | _, _ => none

def binders : Nat → Kore.Pattern → List Kore.EVar × Kore.Pattern
  | fuel + 1, .exist _ x p => let (xs, b) := binders fuel p; (x :: xs, b)
  | _, p => ([], p)

end KoreAML.Parse
