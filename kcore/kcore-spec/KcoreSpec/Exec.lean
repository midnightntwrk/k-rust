/-
  KCore. The executable step of a definition (checked layer; KCORE-SPEC.md §8), proved equal to
  `Step` (`step_iff_of_ok`, StepIff.lean).
  An executable matcher lists all matches (maps modulo AC, by choosing an entry per `|->`
  element), and evaluation runs with fuel and definedness, `none` meaning out of fuel. The rules
  that apply (a well-sorted match whose `requires` evaluates to `true`) are found for every rule;
  only those of the smallest priority among them give successors. A `requires` out of fuel counts
  as applying (it blocks the lower priorities but gives no successor), so fuel never lets a lower
  rule fire.
-/
import KcoreSpec.Step
import KcoreSpec.Tie

set_option autoImplicit false

namespace KCore.Exec

open KCore

def same (v w : GroundTerm) : Bool := GroundTerm.cmp v w == .eq

mutual
  /-- The number of nodes of a pattern. -/
  def termSize : Term → Nat
    | .var _ => 1
    | .dv _ _ => 1
    | .app _ ts => termSizeList ts + 1
    | .inj _ _ t => termSize t + 1
    | .as t _ => termSize t + 1
    termination_by structural t => t
  def termSizeList : List Term → Nat
    | [] => 0
    | t :: ts => termSize t + termSizeList ts
    termination_by structural ts => ts
end

/-- The matcher's fuel for a pattern list: every recursive call of `matchP`, `matchL`,
`mapParts` and `pickAll` descends into the pattern, so a multiple of its size bounds the depth. -/
def patFuel (ps : List Term) : Nat := 4 * termSizeList ps + 4

/-- The result `true`. -/
def isTrue : Option GroundTerm → Bool
  | some (.dv s (.bool true)) => s == Srt.bool
  | _ => false

/-- Bind variable `i` to `v`, or check the binding it has. -/
def bindVar (σ : Subst) (i : Nat) (v : GroundTerm) : Option Subst :=
  match σ.lookup i with
  | some w => if same w v then some σ else none
  | none => some ((i, v) :: σ)

/-- A map pattern as its `|->` elements and its frames (`_Map_` flattened, `.Map` dropped). -/
def mapParts : Nat → Term → Option (List (Term × Term) × List Nat)
  | 0, _ => none
  | _ + 1, .var i => some ([], [i])
  | _ + 1, .app f [] => if f == mapUnit then some ([], []) else none
  | n + 1, .app f [p, q] =>
    if f == mapElem then some ([(p, q)], [])
    else if f == mapConcat then do
      let (e1, f1) ← mapParts n p
      let (e2, f2) ← mapParts n q
      pure (e1 ++ e2, f1 ++ f2)
    else none
  | _, _ => none

/-- The entries with the one at index j removed, and that entry. -/
def pick (es : List (GroundTerm × GroundTerm)) (j : Nat) : Option ((GroundTerm × GroundTerm) × List (GroundTerm × GroundTerm)) :=
  (es[j]?).map fun e => (e, es.eraseIdx j)

mutual
  /-- Every extension of σ under which the pattern denotes the value (fuel bounds the depth). -/
  def matchP (c : Semantics) : Nat → Subst → Term → GroundTerm → List Subst
    | 0, _, _, _ => []
    | _ + 1, σ, .var i, v => (bindVar σ i v).toList
    | _ + 1, σ, .dv s l, v => match v with
      | .dv s' l' => if s == s' && l == l' then [σ] else []
      | _ => []
    | n + 1, σ, .inj a b p, v => match v with
      | .inj x b' u => if b == b' then
          (if x == a then matchP c n σ p u else matchP c n σ p (.inj x a u))
        else []
      | _ => []
    | n + 1, σ, .as p i, v => (matchP c n σ p v).filterMap (bindVar · i v)
    | n + 1, σ, .app f ps, v =>
      if c.isCtor f then match v with
        | .ctor g vs => if f == g then matchL c n σ ps vs else []
        | _ => []
      else if patternHooks.contains f then match v, mapParts (n + 1) (.app f ps) with
        | .map s es, some (elems, frames) => if s == Srt.map then
          (pickAll c n σ elems es).flatMap fun (σ', rest) => match frames with
            | [] => if rest.isEmpty then [σ'] else []
            | [i] => (bindVar σ' i (.map Srt.map rest)).toList
            | _ => []
          else []
        | _, _ => []
      else []
  def matchL (c : Semantics) : Nat → Subst → List Term → List GroundTerm → List Subst
    | 0, _, _, _ => []
    | _ + 1, σ, [], [] => [σ]
    | n + 1, σ, p :: ps, v :: vs => (matchP c n σ p v).flatMap fun σ' => matchL c n σ' ps vs
    | _ + 1, _, _, _ => []
  /-- Choose an entry for each element, in order; each chosen entry is removed. -/
  def pickAll (c : Semantics) : Nat → Subst → List (Term × Term) → List (GroundTerm × GroundTerm) →
      List (Subst × List (GroundTerm × GroundTerm))
    | 0, _, _, _ => []
    | _ + 1, σ, [], es => [(σ, es)]
    | n + 1, σ, (kp, vp) :: elems, es =>
      (List.range es.length).flatMap fun j => match pick es j with
        | some ((k, v), rest) =>
          (matchP c n σ kp k).flatMap fun σ1 => (matchP c n σ1 vp v).flatMap fun σ2 =>
            pickAll c n σ2 elems rest
        | none => []
end

/-- Insert a clause before the first clause of a priority at least its own. -/
def insertPrio (cl : Clause) : List Clause → List Clause
  | [] => [cl]
  | cl' :: cls => if cl.prio ≤ cl'.prio then cl :: cl' :: cls else cl' :: insertPrio cl cls

/-- The clauses in order of priority, smaller first, those of one priority in their order (an
insertion sort, stable). The order of the clauses of one priority is the one the evaluation tries
them in; `Eval` reads none. -/
def byPrio (cls : List Clause) : List Clause := cls.foldr insertPrio []

theorem mem_insertPrio {cl x : Clause} : ∀ {l : List Clause}, x ∈ insertPrio cl l ↔ x = cl ∨ x ∈ l
  | [] => by simp [insertPrio]
  | cl' :: cls => by
    unfold insertPrio
    split
    · exact List.mem_cons
    · rw [List.mem_cons, mem_insertPrio, List.mem_cons]
      constructor
      · rintro (h | h | h)
        · exact .inr (.inl h)
        · exact .inl h
        · exact .inr (.inr h)
      · rintro (h | h | h)
        · exact .inr (.inl h)
        · exact .inl h
        · exact .inr (.inr h)

theorem mem_byPrio {x : Clause} : ∀ {l : List Clause}, x ∈ byPrio l ↔ x ∈ l
  | [] => by simp [byPrio]
  | a :: l => by
    show x ∈ insertPrio a (byPrio l) ↔ _
    rw [mem_insertPrio, mem_byPrio, List.mem_cons]

theorem pairwise_insertPrio {cl : Clause} : ∀ {l : List Clause},
    l.Pairwise (fun a b => a.prio ≤ b.prio) → (insertPrio cl l).Pairwise (fun a b => a.prio ≤ b.prio)
  | [], _ => by simp [insertPrio]
  | cl' :: cls, h => by
    unfold insertPrio
    split
    · rename_i hle
      refine List.Pairwise.cons (fun x hx => ?_) h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hle
      · exact Nat.le_trans hle ((List.pairwise_cons.mp h).1 x hx)
    · rename_i hlt
      obtain ⟨h1, h2⟩ := List.pairwise_cons.mp h
      refine List.Pairwise.cons (fun x hx => ?_) (pairwise_insertPrio h2)
      rcases mem_insertPrio.mp hx with rfl | hx
      · omega
      · exact h1 x hx

theorem pairwise_byPrio : ∀ (l : List Clause), (byPrio l).Pairwise (fun a b => a.prio ≤ b.prio)
  | [] => by simp [byPrio]
  | a :: l => pairwise_insertPrio (l := byPrio l) (pairwise_byPrio l)

/-- Before a clause in `byPrio` lie all the clauses of a smaller priority. -/
theorem byPrio_lt {cls pre post : List Clause} {cl cl' : Clause} (h : byPrio cls = pre ++ cl :: post)
    (hmem : cl' ∈ cls) (hlt : cl'.prio < cl.prio) : cl' ∈ pre := by
  have hs := pairwise_byPrio cls
  have hm : cl' ∈ pre ++ cl :: post := h ▸ mem_byPrio.mpr hmem
  rw [h, List.pairwise_append] at hs
  rcases List.mem_append.mp hm with hp | hp
  · exact hp
  · exfalso
    have := (List.pairwise_cons.mp hs.2.1).1
    rcases List.mem_cons.mp hp with rfl | hp
    · omega
    · have := this cl' hp; omega

/-- σ gives every variable of the list a value of its sort. -/
def wellSorted (c : Semantics) (vars : List Srt) (σ : Subst) : Bool :=
  (List.range vars.length).all fun i => match σ.lookup i with
    | some v => c.sortOf v == vars[i]?
    | none => false

mutual
  /-- `some r`: the result (as `EvalTerm`); `none`: out of fuel or no result. -/
  def evalT (c : Semantics) : Nat → Subst → Term → Option (Option GroundTerm)
    | 0, _, _ => none
    | _ + 1, σ, .var i => some (σ.lookup i)
    | _ + 1, _, .dv s l => some (some (.dv s l))
    | n + 1, σ, .inj a b t => (evalT c n σ t).map (·.map (injNormal a b))
    | _ + 1, _, .as _ _ => none
    | n + 1, σ, .app f ts => do
      let rs ← evalTs c n σ ts
      if c.isCtor f then pure ((allSome rs).map (.ctor f))
      else if isHook f then match allSome rs with
        | none => pure none
        | some vs => c.hookRes f vs
      else if c.isParam f then pure ((allSome rs).bind (c.paramVal f))
      else match allSome rs with
        | none => pure none
        | some vs => evalF c n f vs
  def evalTs (c : Semantics) : Nat → Subst → List Term → Option (List (Option GroundTerm))
    | 0, _, _ => none
    | _ + 1, _, [] => some []
    | n + 1, σ, t :: ts => do pure ((← evalT c n σ t) :: (← evalTs c n σ ts))
  def evalF (c : Semantics) : Nat → Sym → List GroundTerm → Option (Option GroundTerm)
    | 0, _, _ => none
    | n + 1, f, vs => do
      let fn ← c.lookupFn f
      firstClause c n vs (c.fnRest fn vs) (byPrio fn.clauses)
  /-- The clauses in order of priority (`byPrio`), one priority at a time. Of the clauses of the
  first priority (`takeWhile`), every well-sorted match the matcher lists is a candidate, with its
  `requires` evaluated (`some true` without one). The first candidate whose `requires` is `true` and
  whose `ensures` and right-hand side have results gives the right-hand side's where the `ensures`
  is `true`, and no value where it is something else; where every candidate's `requires` is something
  else (false or undefined), the clauses of the next priority are tried; otherwise (a `requires`
  or a right-hand side out of fuel) there is no result. No candidate waits on another of its
  priority: a clause that applies, every clause of a smaller priority failing, is found whatever
  the evaluation of the others of its priority does. Where every clause fails, the result is
  the function's rest `fr` (`Semantics.fnRest`). -/
  def firstClause (c : Semantics) : Nat → List GroundTerm → Option GroundTerm → List Clause →
      Option (Option GroundTerm)
    | 0, _, _, _ => none
    | _ + 1, _, fr, [] => some fr
    | n + 1, vs, fr, cl :: rest =>
      let vals := ((cl :: rest).takeWhile (·.prio == cl.prio)).flatMap fun cl' =>
        ((matchL c (patFuel cl'.pats) [] cl'.pats vs).filter (wellSorted c cl'.vars)).map fun σ =>
          (cl', σ, match cl'.req with
            | none => some true
            | some t => (evalT c n σ t).map isTrue)
      match vals.findSome? fun (cl', σ, b) => if b == some true then
          (match (match cl'.ens with
            | none => some true
            | some t => (evalT c n σ t).map isTrue) with
          | some true => evalT c n σ cl'.rhs
          | some false => some none
          | none => none)
        else none with
      | some r => some r
      | none =>
        if vals.all (·.2.2 == some false) then
          firstClause c n vs fr ((cl :: rest).dropWhile (·.prio == cl.prio))
        else none
end

/-- A clause's well-sorted matches at the arguments, as the matcher lists them. -/
def clauseMatches (c : Semantics) (cl : Clause) (vs : List GroundTerm) : List Subst :=
  (matchL c (patFuel cl.pats) [] cl.pats vs).filter (wellSorted c cl.vars)

/-- A match's `requires` with `n` units of fuel: `some true` without one, `none` out of fuel. -/
def clauseReq (c : Semantics) (n : Nat) (cl : Clause) (σ : Subst) : Option Bool :=
  match cl.req with
  | none => some true
  | some t => (evalT c n σ t).map isTrue

/-- The candidates of the clauses `cls` at `vs` (`firstClause`): each clause with each of its
matches and its `requires`. -/
def candidates (c : Semantics) (n : Nat) (vs : List GroundTerm) (cls : List Clause) :
    List (Clause × Subst × Option Bool) :=
  cls.flatMap fun cl => (clauseMatches c cl vs).map fun σ => (cl, σ, clauseReq c n cl σ)

/-- A match's `ensures` with `n` units of fuel: `some true` without one, `none` out of fuel. -/
def clauseEns (c : Semantics) (n : Nat) (cl : Clause) (σ : Subst) : Option Bool :=
  match cl.ens with
  | none => some true
  | some t => (evalT c n σ t).map isTrue

/-- A match's result where its `requires` is `true`: its right-hand side's where its `ensures` is
`true`, undefined where the `ensures` is something else, none out of fuel. -/
def candBody (c : Semantics) (n : Nat) (cl : Clause) (σ : Subst) : Option (Option GroundTerm) :=
  match clauseEns c n cl σ with
  | some true => evalT c n σ cl.rhs
  | some false => some none
  | none => none

/-- A candidate's result: `candBody`, where its `requires` is `true`. -/
def candResult (c : Semantics) (n : Nat) (a : Clause × Subst × Option Bool) : Option (Option GroundTerm) :=
  if a.2.2 == some true then candBody c n a.1 a.2.1 else none

theorem firstClause_cons (c : Semantics) (n : Nat) (vs : List GroundTerm) (fr : Option GroundTerm) (cl : Clause)
    (rest : List Clause) :
    firstClause c (n + 1) vs fr (cl :: rest) =
      match (candidates c n vs ((cl :: rest).takeWhile (·.prio == cl.prio))).findSome? (candResult c n) with
      | some r => some r
      | none =>
        if (candidates c n vs ((cl :: rest).takeWhile (·.prio == cl.prio))).all (·.2.2 == some false) then
          firstClause c n vs fr ((cl :: rest).dropWhile (·.prio == cl.prio))
        else none := by
  simp only [firstClause]
  rfl

theorem mem_candidates {c : Semantics} {n : Nat} {vs : List GroundTerm} {cls : List Clause} {cl : Clause} {σ : Subst}
    {b : Option Bool} :
    (cl, σ, b) ∈ candidates c n vs cls ↔ cl ∈ cls ∧ σ ∈ clauseMatches c cl vs ∧ b = clauseReq c n cl σ := by
  simp only [candidates, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨cl', h1, σ', h2, rfl, rfl, rfl⟩
    exact ⟨h1, h2, rfl⟩
  · rintro ⟨h1, h2, rfl⟩
    exact ⟨cl, h1, σ, h2, rfl, rfl, rfl⟩

theorem prio_of_mem_takeWhile {p : Nat} : ∀ {l : List Clause} {x : Clause},
    x ∈ l.takeWhile (·.prio == p) → x.prio = p
  | [], _, h => nomatch h
  | a :: l, x, h => by
    simp only [List.takeWhile_cons] at h
    split at h
    · rename_i ha
      rcases List.mem_cons.mp h with rfl | h
      · simpa using ha
      · exact prio_of_mem_takeWhile h
    · nomatch h

/-- In a list sorted by priority whose first clause has priority p, every clause of priority p is
in the first priority's part. -/
theorem mem_takeWhile_of_sorted {p : Nat} : ∀ {l : List Clause} {x : Clause},
    l.Pairwise (fun a b => a.prio ≤ b.prio) → (∀ a ∈ l.head?, a.prio = p) → x ∈ l → x.prio = p →
      x ∈ l.takeWhile (·.prio == p)
  | [], _, _, _, h, _ => nomatch h
  | a :: l, x, hs, ha, hx, hp => by
    have hap : a.prio = p := ha a rfl
    simp only [List.takeWhile_cons, hap, beq_self_eq_true, ↓reduceIte]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_cons_self ..
    · refine List.mem_cons_of_mem _ (mem_takeWhile_of_sorted (List.pairwise_cons.mp hs).2 ?_ hx hp)
      intro b hb
      cases l with
      | nil => nomatch hb
      | cons b' l =>
        have hbb : b = b' := (Option.some.inj hb).symm
        rw [hbb]
        have h1 := (List.pairwise_cons.mp hs).1 b' (List.mem_cons_self ..)
        have h3 : b'.prio ≤ x.prio := by
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact Nat.le_refl _
          · exact (List.pairwise_cons.mp (List.pairwise_cons.mp hs).2).1 x hx'
        omega

/-- A rule's matches at x, each with its `requires`: `some true` (applies), `some false` (does
not), `none` (out of fuel). -/
def ruleMatches (c : Semantics) (n : Nat) (r : Rule) (x : GroundTerm) : List (Subst × Option Bool) :=
  ((matchP c (patFuel [r.lhs]) [] r.lhs x).filter (wellSorted c r.vars)).map fun σ =>
    (σ, match r.req with
      | none => some true
      | some t => (evalT c n σ t).map isTrue)

/-- A match's `ensures`: `some true` where there is none, else its value read as a Boolean
(`none`: out of fuel). -/
def ensVal (c : Semantics) (n : Nat) (r : Rule) (σ : Subst) : Option Bool :=
  match r.ens with
  | none => some true
  | some t => (evalT c n σ t).map isTrue

/-- The successors of a configuration with `n` units of evaluation fuel: among the rules that
apply (or might, out of fuel), those of the smallest priority; for each of their matches whose
`requires` is `true`, the configuration the right-hand side evaluates to, where the `ensures` is
`true`. -/
def successorsN (c : Semantics) (n : Nat) (x : GroundTerm) : List GroundTerm :=
  let ms := c.rules.map fun r => (r, ruleMatches c n r x)
  let applying := ms.filter fun (_, l) => l.any fun (_, b) => b != some false
  match (applying.map (·.1.prio)).min? with
  | none => []
  | some p =>
    (applying.filter (·.1.prio == p)).flatMap fun (r, l) =>
      l.filterMap fun (σ, b) =>
        if b == some true then match evalT c n σ r.rhs with
          | some (some y) =>
            if c.sortOf y == some topCellSort && ensVal c n r σ == some true then some y else none
          | _ => none
        else none

/-- The evaluation fuel of `successors`. -/
def fuel : Nat := 100000

/-- `successorsN` at a fixed fuel (the differentials). -/
def successors (c : Semantics) (x : GroundTerm) : List GroundTerm := successorsN c fuel x

/- `step_iff`: the executable step lists exactly the `Step` successors of a well-formed definition,
for some fuel. It is stated and proved in StepIffWf.lean, after the matcher's and the evaluation's
proofs, which import this file:

    theorem step_iff (d : Definition) (hwf : wf d = true) (x y : Config d.sem) :
        Step d.sem x y ↔ ∃ n, (successorsN d.sem n x.val).any (same · y.val) = true

Coherence is needed for the `→` direction: `Eval` relates the result of every clause that applies
(no clause of a smaller priority applying) under every σ that applies, the executable evaluation
takes one, and coherence (`CoherentAll`, EvalFunctional.lean) makes the result unique. -/

end KCore.Exec

namespace KCore

/-- No clause of a function evaluation reads is `aside`. The executable evaluation tries the
clauses by priority and stops at the first that applies, `aside` or not, while `Eval` lets an
`aside` clause block no clause; its completeness is stated where this holds. -/
def Semantics.AsideFree (c : Semantics) : Prop :=
  ∀ {f : Sym} {fn : Fn}, c.lookupFn f = some fn → ∀ cl ∈ fn.clauses, cl.aside = false

/-- `AsideFree`, decided. -/
def Semantics.asideFree (c : Semantics) : Bool := c.allFns.all fun fn => fn.clauses.all (!·.aside)

theorem Semantics.asideFree_spec {c : Semantics} (h : c.asideFree = true) : c.AsideFree := by
  intro f fn hfn cl hcl
  rw [Semantics.lookupFn_eq] at hfn
  have := List.all_eq_true.mp (List.all_eq_true.mp h fn (List.mem_of_find?_eq_some hfn)) cl hcl
  simpa using this

end KCore
