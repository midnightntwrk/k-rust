/-
  A readable printer for translated patterns, in the papers' notation:
  `⊥ ⊤ ¬ ∧ ∨ → ↔ ∃ ∀ μ`, `⌈φ⌉`, `⌊φ⌋`, `=`, `∈`, `⊆`, `⟦s⟧` for inhabitants, `•`,
  and application by juxtaposition.

  A notation is printed only when the pattern is exactly that notation's definition:
  each recognizer decomposes the pattern and then checks, by `DecidableEq`, that rebuilding
  the notation from the parts gives the same pattern back.
  Sorted notations carry their sorts in brackets: `¬[s] φ`, `φ →[s] ψ`, `φ =[s,s'] ψ`, `⊤[s]`.
  Sort names are KORE's; symbol names drop `Lbl` and are unmangled
  (`'Unds'` ↦ `_`, `'-LT-'` ↦ `<`, …) for display only.

  The printer is `partial` (it recurses into deep subterms); it is not part of the specification.
-/
import KcoreSpec.Kore.Translate

set_option autoImplicit false

namespace KoreAML.Print

open ML

/-! ## Names -/

def kCodes : List (String × String) :=
  [("Spce", " "), ("Bang", "!"), ("Quot", "\""), ("Hash", "#"), ("Dolr", "$"), ("Perc", "%"),
   ("And-", "&"), ("Apos", "'"), ("LPar", "("), ("RPar", ")"), ("Star", "*"), ("Plus", "+"),
   ("Comm", ","), ("Hyph", "-"), ("Stop", "."), ("Slsh", "/"), ("Coln", ":"), ("SCln", ";"),
   ("-LT-", "<"), ("Eqls", "="), ("-GT-", ">"), ("Ques", "?"), ("-AT-", "@"), ("LSqB", "["),
   ("Bash", "\\"), ("RSqB", "]"), ("Xor-", "^"), ("Unds", "_"), ("BQuo", "`"), ("LBra", "{"),
   ("Pipe", "|"), ("RBra", "}"), ("Tild", "~")]

/-- Decode one `'…'` segment of K's name mangling (a run of 4-character codes). -/
def decodeSegment (seg : String) : Option String :=
  let rec go (cs : List Char) (fuel : Nat) : Option String :=
    match fuel with
    | 0 => if cs.isEmpty then some "" else none
    | fuel + 1 =>
      if cs.isEmpty then some "" else
      let code := String.ofList (cs.take 4)
      match kCodes.lookup code with
      | some c => (go (cs.drop 4) fuel).map (c ++ ·)
      | none => none
  go seg.toList seg.length

/-- Unmangle a KORE identifier; keep it as is when a segment does not decode. -/
def unmangle (name : String) : String :=
  let parts := name.splitOn "'"
  if parts.length % 2 == 0 then name else
  let decoded := (List.range parts.length).zip parts |>.map fun (i, p) =>
    if i % 2 == 0 then some p else decodeSegment p
  if decoded.all Option.isSome then String.join (decoded.filterMap id) else name

def dropPrefix (pre s : String) : String :=
  if s.startsWith pre && s.length > pre.length then String.ofList (s.toList.drop pre.length) else s

def symName : Sym → String
  | .defined => "⌈_⌉"
  | .inh => "⟦_⟧"
  | .sortSort => "Sort"
  | .sort n => n
  | .symbol n => unmangle (dropPrefix "Lbl" n)
  | .ceil => "ceil"
  | .next => "•"
  | .dv lit => s!"dv\"{lit}\""
  | .str lit => s!"\"{lit}\""
  | .untranslated w => s!"‹UNTRANSLATED {w}›"

/-! ## Recognizers -/

def asNeg? : P → Option P
  | .implication a .bottom => some a
  | _ => none

def asImp? : P → Option (P × P)
  | .implication a b => some (a, b)
  | _ => none

def asApp? : P → Option (P × P)
  | .application a b => some (a, b)
  | _ => none

/-- `φ ⋀ ψ = ∼(∼∼φ ⇒ ∼ψ)`. -/
def asConj? (p : P) : Option (P × P) := do
  let (a, b) ← asImp? (← asNeg? p)
  let φ ← asNeg? (← asNeg? a)
  let ψ ← asNeg? b
  if p = φ ⋀ ψ then some (φ, ψ) else none

def asTop? (p : P) : Bool := p = (⊤ : P)

def asInh? : P → Option P
  | .application (.symbol .inh) s => some s
  | _ => none

def asDefined? : P → Option P
  | .application (.symbol .defined) φ => some φ
  | _ => none

/-- `⌊φ⌋ = ∼⌈∼φ⌉`. -/
def asTotal? (p : P) : Option P := do
  let φ ← asNeg? (← asDefined? (← asNeg? p))
  if p = ⌊φ⌋ then some φ else none

def asEquiv? (p : P) : Option (P × P) := do
  let (l, _) ← asConj? p
  let (φ, ψ) ← asImp? l
  if p = (φ ⇔ ψ) then some (φ, ψ) else none

def asEqual? (p : P) : Option (P × P) := do
  let (φ, ψ) ← asEquiv? (← asTotal? p)
  if p = (φ ≡ ψ) then some (φ, ψ) else none

def asIncluded? (p : P) : Option (P × P) := do
  let (φ, ψ) ← asImp? (← asTotal? p)
  if p = (φ ⊆⊆ ψ) then some (φ, ψ) else none

def asMember? (p : P) : Option (EVar × P) := do
  let (a, φ) ← asConj? (← asDefined? p)
  match a with
  | .evar x => if p = (x ∈∈ φ) then some (x, φ) else none
  | _ => none

def asForallU? (p : P) : Option (EVar × P) :=
  match p with
  | .implication (.existential x (.implication φ .bottom)) .bottom =>
    if p = ∀∀ x φ then some (x, φ) else none
  | _ => none

/-- `¬[s] φ = (∼φ) ⋀ ⟦s⟧`. -/
def asSNot? (p : P) : Option (P × P) := do
  let (a, b) ← asConj? p
  let s ← asInh? b
  let φ ← asNeg? a
  if p = sNot s φ then some (s, φ) else none

def asSExists? (p : P) : Option (EVar × P × P) :=
  match p with
  | .existential x body => do
    let (m, φ) ← asConj? body
    let (y, ins) ← asMember? m
    let s' ← asInh? ins
    if y = x ∧ p = sExists x s' φ then some (x, s', φ) else none
  | _ => none

def asSTop? (p : P) : Option P := do
  let (x, s, φ) ← asSExists? p
  if x = topVar ∧ φ = .evar topVar then some s else none

def asSBot? (p : P) : Option P := do
  let (s, φ) ← asSNot? p
  let s' ← asSTop? φ
  if s = s' then some s else none

def asSOr? (p : P) : Option (P × P × P) := do
  let (s, c) ← asSNot? p
  let (a, b) ← asConj? c
  let (_, φ) ← asSNot? a
  let (_, ψ) ← asSNot? b
  if p = sOr s φ ψ then some (s, φ, ψ) else none

def asSImp? (p : P) : Option (P × P × P) := do
  let (s, a, ψ) ← asSOr? p
  let (_, φ) ← asSNot? a
  if p = sImp s φ ψ then some (s, φ, ψ) else none

def asSIff? (p : P) : Option (P × P × P) := do
  let (l, _) ← asConj? p
  let (s, φ, ψ) ← asSImp? l
  if p = sIff s φ ψ then some (s, φ, ψ) else none

def asSForall? (p : P) : Option (P × EVar × P × P) := do
  let (s, e) ← asSNot? p
  let (x, s', b) ← asSExists? e
  let (_, φ) ← asSNot? b
  if p = sForall s x s' φ then some (s, x, s', φ) else none

def asSCeil? : P → Option (P × P × P)
  | .application (.application (.application (.symbol .ceil) s) s') φ => some (s, s', φ)
  | _ => none

def asSFloor? (p : P) : Option (P × P × P) := do
  let (s', c) ← asSNot? p
  let (s, _, n) ← asSCeil? c
  let (_, φ) ← asSNot? n
  if p = sFloor s s' φ then some (s, s', φ) else none

def asSEquals? (p : P) : Option (P × P × P × P) := do
  let (s, s', b) ← asSFloor? p
  let (_, φ, ψ) ← asSIff? b
  if p = sEquals s s' φ ψ then some (s, s', φ, ψ) else none

def asSIn? (p : P) : Option (P × P × P × P) := do
  let (s, s', c) ← asSCeil? p
  let (φ, ψ) ← asConj? c
  if p = sIn s s' φ ψ then some (s, s', φ, ψ) else none

def asNegMember? (p : P) : Option (EVar × P) := do
  let (x, φ) ← asMember? (← asNeg? p)
  if p = ∼(x ∈∈ φ) then some (x, φ) else none

/-- Patterns whose outermost `∼` the printer shows as a notation rather than as negation. -/
def isNotation (a : P) : Bool :=
  (asConj? a).isSome || asTop? a || (asTotal? a).isSome || (asForallU? a).isSome

/-- The head and arguments of an application spine. -/
def spine : P → P × List P
  | .application f a => let (h, as) := spine f; (h, as ++ [a])
  | p => (p, [])

/-! ## Printing

Precedence levels: 0 binders, 1 `→ ↔`, 2 `∨`, 3 `∧`, 4 `= ∈ ⊆`, 5 prefix `¬ •`,
6 application, 7 atoms and bracketed forms. -/

def paren (ctx lvl : Nat) (s : String) : String := if lvl < ctx then s!"({s})" else s

def varName (names : List String) (i : Nat) (svar : Bool) : String :=
  if i == 0 then (if svar then "X₀" else "x₀") else unmangle (names.getD (i - 1) s!"v{i}")

partial def pp (names : List String) (ctx : Nat) (p : P) : String :=
  let r := pp names
  if let some (s, x, s', φ) := asSForall? p then
    paren ctx 0 s!"∀[{r 0 s}] {varName names x.val false}:{r 6 s'}. {r 0 φ}"
  else if let some (s, s', φ, ψ) := asSEquals? p then
    paren ctx 4 s!"{r 5 φ} =[{r 0 s},{r 0 s'}] {r 5 ψ}"
  else if let some (s, s', φ) := asSFloor? p then
    s!"⌊{r 0 φ}⌋[{r 0 s},{r 0 s'}]"
  else if let some (s, s', φ, ψ) := asSIn? p then
    paren ctx 4 s!"{r 5 φ} ∈[{r 0 s},{r 0 s'}] {r 5 ψ}"
  else if let some (s, s', φ) := asSCeil? p then
    s!"⌈{r 0 φ}⌉[{r 0 s},{r 0 s'}]"
  else if let some (s, φ, ψ) := asSIff? p then
    paren ctx 1 s!"{r 2 φ} ↔[{r 0 s}] {r 2 ψ}"
  else if let some (s, φ, ψ) := asSImp? p then
    paren ctx 1 s!"{r 2 φ} →[{r 0 s}] {r 1 ψ}"
  else if let some s := asSBot? p then
    s!"⊥[{r 0 s}]"
  else if let some (s, φ, ψ) := asSOr? p then
    paren ctx 2 s!"{r 3 φ} ∨[{r 0 s}] {r 2 ψ}"
  else if let some (s, φ) := asSNot? p then
    paren ctx 5 s!"¬[{r 0 s}] {r 5 φ}"
  else if let some s := asSTop? p then
    s!"⊤[{r 0 s}]"
  else if let some (x, s', φ) := asSExists? p then
    paren ctx 0 s!"∃{varName names x.val false}:{r 6 s'}. {r 0 φ}"
  else if let some (x, φ) := asNegMember? p then
    paren ctx 5 s!"¬({varName names x.val false} ∈ {r 5 φ})"
  else if let some (φ, ψ) := asEqual? p then
    paren ctx 4 s!"{r 5 φ} = {r 5 ψ}"
  else if let some (φ, ψ) := asIncluded? p then
    paren ctx 4 s!"{r 5 φ} ⊆ {r 5 ψ}"
  else if let some (x, φ) := asMember? p then
    paren ctx 4 s!"{varName names x.val false} ∈ {r 5 φ}"
  else if let some φ := asTotal? p then
    s!"⌊{r 0 φ}⌋"
  else if asTop? p then "⊤"
  else if let some (φ, ψ) := asEquiv? p then
    paren ctx 1 s!"{r 2 φ} ↔ {r 2 ψ}"
  else if let some (φ, ψ) := asConj? p then
    paren ctx 3 s!"{r 4 φ} ∧ {r 3 ψ}"
  else if let some (x, φ) := asForallU? p then
    paren ctx 0 s!"∀{varName names x.val false}. {r 0 φ}"
  else match p with
  | .bottom => "⊥"
  | .evar x => varName names x.val false
  | .svar X => varName names X.val true
  | .symbol σ => symName σ
  | .existential x φ => paren ctx 0 s!"∃{varName names x.val false}. {r 0 φ}"
  | .mu X φ => paren ctx 0 s!"μ{varName names X.val true}. {r 0 φ}"
  | .implication a .bottom => paren ctx 5 s!"¬{r 5 a}"
  | .implication a b =>
    -- `∼φ ⇒ ψ` is also AML's `φ ∨ ψ`; print it so only when `∼φ` is a bare negation,
    -- not when it is a conjunction, `⊤`, `⌊_⌋`-family or `∀` notation
    -- (a sorted `∃x:s. φ` under the negation is a disjunct, not a `∀`: the closure axiom).
    match a with
    | .implication φ .bottom =>
      if isNotation a && (asSExists? φ).isNone then paren ctx 1 s!"{r 2 a} → {r 1 b}"
      else paren ctx 2 s!"{r 3 φ} ∨ {r 2 b}"
    | _ => paren ctx 1 s!"{r 2 a} → {r 1 b}"
  | .application (.symbol .defined) φ => s!"⌈{r 0 φ}⌉"
  | .application (.symbol .inh) s => s!"⟦{r 0 s}⟧"
  | .application (.symbol .next) φ => paren ctx 5 s!"•{r 6 φ}"
  | .application (.symbol (.dv lit)) s => s!"dv[{r 0 s}](\"{lit}\")"
  | .application .. =>
    let (h, as) := spine p
    paren ctx 6 (String.intercalate " " (r 6 h :: as.map (r 7)))

def item (it : Item) : String := pp it.names 0 it.pat

/-- The pattern with AML's primitives only (`⊥`, `→`, application, `∃`, `μ`, variables, symbols):
no notation is recognized. -/
def raw (names : List String) : P → String
  | .bottom => "⊥"
  | .evar x => varName names x.val false
  | .svar X => varName names X.val true
  | .symbol σ => symName σ
  | .application a b => s!"({raw names a} {raw names b})"
  | .implication a b => s!"({raw names a} → {raw names b})"
  | .existential x φ => s!"(∃{varName names x.val false}. {raw names φ})"
  | .mu X φ => s!"(μ{varName names X.val true}. {raw names φ})"

end KoreAML.Print
