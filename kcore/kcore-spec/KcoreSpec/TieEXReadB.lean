/-
  The readings `TieEX`'s lemmas take of an equation `prem → F = (∃B:Bool. body) ∧ ens`
  (`hin`, `hcond`, `hbody`, `hinB`, `hcondB`, `hbodyB`), from one decision on the text (`exReadB`),
  in a model with `NodeFacts` and `TermsInSort`.

  The body is one term, or a term with one `\equals` beside it in an `\and` under applications:
  `K[t ∧ (a =_{s1} b)]`, K a path of applications (`bodyPred?`). Its elements are those of `K[t]`
  where a and b agree on s1 (`bodySplit_sem`): the `\equals` holds all of the `\and`'s sort or
  nothing, t lies in that sort (`TightSem`), and an application holds nothing where an argument
  holds nothing (`fill_and_pred`).

  What the decision compares, on translated patterns:
  - the last clause's alternative `j` (B the binder's variable): its term translates as `K[t]`
    does, its conditions as the body's `\equals` at the result sort R, and its term has the
    function's result sort;
  - the alternative of the instance at each literal: its term and its conditions are those of `j`
    with the literal put for the binder's variable (`Pattern.substEvar`). A literal is one element
    at every valuation, so the substituted pattern at e is the pattern at e with B sent to that
    element (`interp_substEvar_one`);
  - the body is `tightB` over the equation's variables and the binder; the tables agree on the
    binder's variable and on R; the `ensures` part is `\top` of the result sort.

  A condition is read as `CGof`: its translation holds on all of R. Each condition here is an
  `\equals` at R, all of R or nothing, so that reading is the condition at any element of R.

  - `exFacts_of_exB`: the six readings (`ExFacts`), from the decision and the guards.
  - `ExFacts.readings`: `TieFR.Readings` of the split, with `boolClosed` (`TieEX.readings_exB`).
  The decision is false of a body with an `\or`, with two predicates, with a predicate that is no
  `\equals` or stands first in its `\and`, and of an `ensures` part other than `\top`.
-/
import KcoreSpec.TieEX
import KcoreSpec.TieFRTightB
import KcoreSpec.CutIdentity

set_option autoImplicit false

namespace KCore

namespace TieEXReadB

open ML KoreAML Faithful KoreAML.TieFR
open KCore.TieFRRead KCore.TermRT KCore.TieEX KCore.TieFRTightB

/-! ## The body's term and predicate -/

mutual
  /-- The path of applications to the first `\and` of a pattern, with its sort and operands. -/
  def andCtx? : Kore.Pattern → Option (KoreCutCtx × Kore.KSort × List Kore.Pattern)
    | .and s ps => some (.hole, s, ps)
    | .app h ss ps => match andCtxList? ps with
      | some (pre, K, s, qs, post) => some (.app h ss pre K post, s, qs)
      | none => none
    | _ => none
    termination_by structural p => p
  def andCtxList? : List Kore.Pattern →
      Option (List Kore.Pattern × KoreCutCtx × Kore.KSort × List Kore.Pattern × List Kore.Pattern)
    | [] => none
    | p :: ps => match andCtx? p with
      | some (K, s, qs) => some ([], K, s, qs, ps)
      | none => match andCtxList? ps with
        | some (pre, rest) => some (p :: pre, rest)
        | none => none
    termination_by structural ps => ps
end

/-- A body `K[t ∧ (a =_{s1} b)]`: the path K, the sort s of the `\and` and of the `\equals`, the
term t, and the `\equals`'s operand sort and operands. -/
structure BodyPred where
  K : KoreCutCtx
  s : Kore.KSort
  t : Kore.Pattern
  s1 : Kore.KSort
  a : Kore.Pattern
  b : Kore.Pattern

/-- The pattern with the `\equals`. -/
def BodyPred.whole (d : BodyPred) : Kore.Pattern := d.K.fill (.and d.s [d.t, .equals d.s1 d.s d.a d.b])

/-- p read as `K[t ∧ (a =_{s1} b)]`, the `\and` its first under applications. -/
def bodyPred? (p : Kore.Pattern) : Option BodyPred :=
  match andCtx? p with
  | some (K, s, [t, .equals s1 s2 a b]) =>
    if s2 = s ∧ K.fill (.and s [t, .equals s1 s2 a b]) = p then some ⟨K, s, t, s1, a, b⟩ else none
  | _ => none

theorem bodyPred?_spec {p : Kore.Pattern} {d : BodyPred} (h : bodyPred? p = some d) : d.whole = p := by
  unfold bodyPred? at h
  split at h
  · split at h
    · rename_i hc
      cases h
      exact hc.1 ▸ hc.2
    · cases h
  · cases h

/-- The body's term: `K[t]`, or the body where it has no predicate. -/
def bodyTerm (p : Kore.Pattern) : Kore.Pattern :=
  match bodyPred? p with
  | some d => d.K.fill d.t
  | none => p

/-- The body's `\equals`: its operand sort and operands. -/
def bodyEqs (p : Kore.Pattern) : List (Kore.KSort × Kore.Pattern × Kore.Pattern) :=
  match bodyPred? p with
  | some d => [(d.s1, d.a, d.b)]
  | none => []

/-- No head is an alias where there is none. -/
theorem noAlias_nil (tbl : VarTable) : ∀ K : KoreCutCtx, K.noAlias ⟨tbl, []⟩ = true
  | .hole => rfl
  | .app _ _ _ C _ => by simp [KoreCutCtx.noAlias, noAlias_nil tbl C]

section
variable {M : Type} {I : Interpretation KoreAML.Sym M}

/-- a and b agree on the sort s1 at e. -/
def EqH (I : Interpretation KoreAML.Sym M) (tbl : VarTable) (e : Valuation M)
    (q : Kore.KSort × Kore.Pattern × Kore.Pattern) : Prop :=
  ∀ z, (inhOf (trSort tbl q.1)).interpret I e z →
    ((tr ⟨tbl, []⟩ q.2.1).interpret I e z ↔ (tr ⟨tbl, []⟩ q.2.2).interpret I e z)

/-- **A pattern that holds what T holds where Q, and nothing otherwise, in an application
context**: the context holds what it holds of T where Q, and nothing otherwise. -/
theorem fill_and_pred {φ T : P} {Q : Prop} {e : Valuation M}
    (h : ∀ a, φ.interpret I e a ↔ T.interpret I e a ∧ Q) :
    ∀ (C : CutCtx) (m : M), (C.fill φ).interpret I e m ↔ (C.fill T).interpret I e m ∧ Q
  | .hole, m => h m
  | .fn C ψ, m => by
    show (C.fill φ ⬝ ψ).interpret I e m ↔ (C.fill T ⬝ ψ).interpret I e m ∧ Q
    simp only [interp_app, fill_and_pred h C]
    constructor
    · rintro ⟨a, b, ⟨ha, hq⟩, hb, hab⟩; exact ⟨⟨a, b, ha, hb, hab⟩, hq⟩
    · rintro ⟨⟨a, b, ha, hb, hab⟩, hq⟩; exact ⟨a, b, ⟨ha, hq⟩, hb, hab⟩
  | .arg ψ C, m => by
    show (ψ ⬝ C.fill φ).interpret I e m ↔ (ψ ⬝ C.fill T).interpret I e m ∧ Q
    simp only [interp_app, fill_and_pred h C]
    constructor
    · rintro ⟨a, b, ha, ⟨hb, hq⟩, hab⟩; exact ⟨⟨a, b, ha, hb, hab⟩, hq⟩
    · rintro ⟨⟨a, b, ha, hb, hab⟩, hq⟩; exact ⟨a, b, ha, ⟨hb, hq⟩, hab⟩

/-- A pattern under applications is `TightSem` where the whole is. -/
theorem tightSem_of_fill {tbl : VarTable} {e : Valuation M} {p : Kore.Pattern} :
    ∀ K : KoreCutCtx, TightSem I tbl e (K.fill p) → TightSem I tbl e p
  | .hole, h => h
  | .app _ _ _ C _, h => by
    rw [KoreCutCtx.fill, TightSem, tightSemList_iff] at h
    exact tightSem_of_fill C (h _ (List.mem_append_right _ (List.mem_cons_self ..)))

/-- **A literal put for a variable**: where δ is the one element y at every valuation, φ with δ
put for x holds at e what φ holds at e with x sent to y. -/
theorem interp_substEvar_one {x : EVar} {δ : P} {y : M}
    (hδ : ∀ (e : Valuation M) m, δ.interpret I e m ↔ m = y) :
    ∀ (φ : P) (e : Valuation M) (m : M),
      (φ.substEvar x δ).interpret I e m ↔ φ.interpret I (updX e x y) m := by
  intro φ
  induction φ with
  | evar z =>
    intro e m
    by_cases h : x = z
    · subst h
      simp only [Pattern.substEvar, ↓reduceIte]
      rw [hδ]
      show _ ↔ m = Function.update e.evalEvar x y x
      rw [Function.update_same]
    · simp only [Pattern.substEvar, h, ↓reduceIte]
      show m = e.evalEvar z ↔ m = Function.update e.evalEvar x y z
      rw [Function.update_noteq (Ne.symm h)]
  | svar X => intro e m; exact Iff.rfl
  | bottom => intro e m; exact Iff.rfl
  | symbol σ => intro e m; exact Iff.rfl
  | application ψ χ ih1 ih2 =>
    intro e m
    simp only [Pattern.substEvar, Pattern.interpret, ih1, ih2]
  | implication ψ χ ih1 ih2 =>
    intro e m
    simp only [Pattern.substEvar, Pattern.interpret, ih1, ih2]
  | existential z ψ ih =>
    intro e m
    by_cases h : x = z
    · subst h
      simp only [Pattern.substEvar, ↓reduceIte, Pattern.interpret, Function.update_idem]
    · simp only [Pattern.substEvar, h, ↓reduceIte, Pattern.interpret, ih]
      have hu : ∀ a, updX ⟨Function.update e.evalEvar z a, e.evalSvar⟩ x y =
          ⟨Function.update (Function.update e.evalEvar x y) z a, e.evalSvar⟩ := fun a =>
        congrArg (fun f => (⟨f, e.evalSvar⟩ : Valuation M)) (Function.update_comm (Ne.symm h) a y e.evalEvar)
      simp only [hu]
  | mu X ψ ih =>
    intro e m
    simp only [Pattern.substEvar, Pattern.interpret, ih]

end

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **The body's elements are its term's where its `\equals` holds**, at a valuation where the body
is `TightSem` and the `\equals`'s operand sort denotes a sort. -/
theorem bodySplit_sem (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) {tbl : VarTable} {e : Valuation M}
    {p : Kore.Pattern} (hT : TightSem I tbl e p) (hs1 : ∀ q ∈ bodyEqs p, SortDen I tbl e q.1) (a : M) :
    (tr ⟨tbl, []⟩ p).interpret I e a ↔
      (tr ⟨tbl, []⟩ (bodyTerm p)).interpret I e a ∧ ∀ q ∈ bodyEqs p, EqH I tbl e q := by
  cases hd : bodyPred? p with
  | none => simp [bodyTerm, bodyEqs, hd]
  | some d =>
    have hp := bodyPred?_spec hd
    simp only [bodyTerm, bodyEqs, hd, List.mem_singleton, forall_eq] at hs1 ⊢
    rw [← hp] at hT ⊢
    have hK := noAlias_nil tbl d.K
    have hTa : TightSem I tbl e (.and d.s [d.t, .equals d.s1 d.s d.a d.b]) := tightSem_of_fill d.K hT
    rw [TightSem] at hTa
    obtain ⟨⟨σ, hσ, hds⟩, hin, -⟩ := hTa
    obtain ⟨σ1, hσ1, hd1⟩ := hs1
    have key : ∀ x, (tr ⟨tbl, []⟩ (.and d.s [d.t, .equals d.s1 d.s d.a d.b])).interpret I e x ↔
        (tr ⟨tbl, []⟩ d.t).interpret I e x ∧ EqH I tbl e (d.s1, d.a, d.b) := by
      intro x
      have hi : ∀ z, (inhOf (trSort tbl d.s1)).interpret I e z ↔ Inh I σ1 z := fun z => interp_inhOf_of hd1
      have hx := hin d.t (List.mem_cons_self ..) x
      rw [interp_inhOf_of hds] at hx
      simp only [tr, trAndList]
      rw [interp_sAnd, interp_sEquals hD hc hd1 hds hσ1 hσ x]
      unfold EqH
      simp only [hi]
      constructor
      · rintro ⟨ht, -, h⟩; exact ⟨ht, h⟩
      · rintro ⟨ht, h⟩; exact ⟨ht, hx ht, h⟩
    unfold BodyPred.whole
    rw [tr_cutCtx ⟨tbl, []⟩ _ d.K hK, tr_cutCtx ⟨tbl, []⟩ _ d.K hK]
    exact fill_and_pred key _ a

/-- **An `\equals` at the result sort R holds all of R where its operands agree, and nothing
otherwise.** -/
theorem eqPat_pred (hD : DefOK I) (hc : I ⊧ᴵ ceilDefItem.pat) {tbl : VarTable} {e : Valuation M}
    {q : Kore.KSort × Kore.Pattern × Kore.Pattern} (hq : SortDen I tbl e q.1)
    (hrS : IsSort I (e.evalEvar (tbl.ev (sortVarKey Rv)))) (m : M) :
    (tr ⟨tbl, []⟩ (.equals q.1 R q.2.1 q.2.2)).interpret I e m ↔
      Inh I (e.evalEvar (tbl.ev (sortVarKey Rv))) m ∧ EqH I tbl e q := by
  obtain ⟨σ1, hσ1, hd1⟩ := hq
  have hi : ∀ z, (inhOf (trSort tbl q.1)).interpret I e z ↔ Inh I σ1 z := fun z => interp_inhOf_of hd1
  rw [tr, TieFRRead.trSort_R, interp_sEquals hD hc hd1 (fun _ => interp_evar) hσ1 hrS m]
  unfold EqH
  simp only [hi]

/-! ## The decision -/

/-- A condition read as holding on all of R. -/
def CGof (I : Interpretation KoreAML.Sym M) (c : Semantics) (tbl : VarTable) (vs : List KoreAML.Var)
    (p : Cond) (e : Valuation M) : Prop :=
  ∀ m, Inh I (e.evalEvar (tbl.ev (sortVarKey Rv))) m → (tr ⟨tbl, []⟩ (Cond.kore c vs R p)).interpret I e m

end

/-- The translations of conditions, at the result sort R. -/
def condPats (c : Semantics) (tbl : VarTable) (vs : List KoreAML.Var) (ps : List Cond) : List P :=
  ps.map fun p => tr ⟨tbl, []⟩ (Cond.kore c vs R p)

/-- The translations of the body's `\equals`, each at the result sort R. -/
def eqPats (tbl : VarTable) (qs : List (Kore.KSort × Kore.Pattern × Kore.Pattern)) : List P :=
  qs.map fun q => tr ⟨tbl, []⟩ (.equals q.1 R q.2.1 q.2.2)

/-- The clauses' variables with the last clause's binder. -/
abbrev vsBof (c : Semantics) (vars : List Srt) : List KoreAML.Var :=
  canonVars c vars ++ [binderB c (canonVars c vars)]

/-- The instances' alternatives: one at `true`, one at `false`. -/
def xsOfB (xT xF : Term × List Cond) : Bool → List (Term × List Cond) := fun b => [bif b then xT else xF]

/-- The tables: `Γ`'s binder variable is the text's B, which is not R's variable; the tables agree
on R, on the equation's variables, and on them with the binder; the binder is the variable after
them and none of them. -/
def tablesB (c : Semantics) (tbl tblT : VarTable) (vars : List Srt) (vsF : List Var) (Bv : Var) : Bool :=
  decide (tbl.ev (evarKey (binderB c (canonVars c vars)).kore) = tblT.ev (evarKey Bv.kore)) &&
  decide (tblT.ev (evarKey Bv.kore) ≠ tbl.ev (sortVarKey Rv)) &&
  decide (tblT.ev (sortVarKey Rv) = tbl.ev (sortVarKey Rv)) &&
  alignOK c tbl tblT vars vsF &&
  alignOK c tbl tblT (vars ++ [Srt.bool]) (vsF ++ [Bv]) &&
  (List.range vars.length).all (fun i =>
    decide (tbl.ev (canonKey c (vars ++ [Srt.bool]) i) = tbl.ev (canonKey c vars i)) &&
      decide (tbl.ev (canonKey c vars i) ≠ tblT.ev (evarKey Bv.kore))) &&
  decide (tbl.ev (canonKey c (vars ++ [Srt.bool]) vars.length) = tblT.ev (evarKey Bv.kore))

/-- The body against the last clause's alternative j: the body is `tightB` over the variables with
the binder, its `\equals`'s operand sort is numbered, its term translates as j's, its `\equals` at
R as j's conditions, and j's term has the numbered sort s. -/
def bodyB (N : Parse.Names) (c : Semantics) (tbl tblT : VarTable) (vars : List Srt) (vsF : List Var) (Bv : Var)
    (s : Srt) (bodyK : Kore.Pattern) (j : Term × List Cond) : Bool :=
  tightB N c tbl tblT (vars ++ [Srt.bool]) (vsF ++ [Bv]) bodyK &&
  (bodyEqs bodyK).all (fun q => sortNumB c tbl tblT q.1) &&
  decide (tr ⟨tblT, []⟩ (bodyTerm bodyK) = altPC c tbl (vsBof c vars) j) &&
  decide (condPats c tbl (vsBof c vars) j.2 = eqPats tblT (bodyEqs bodyK)) &&
  decide (sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) (vars ++ [Srt.bool]) j.1 = some s) &&
  decide (s < nRegSorts + c.sortNames.length)

/-- The `ensures` part is `\top` of the sort s. -/
def ensB (c : Semantics) (tbl tblT : VarTable) (s : Srt) (en : Kore.Pattern) : Bool :=
  decide (ensBools en = some []) && decide (trSort tblT (ensSort en) = trSort tbl (srtOf c s))

/-- The alternative x of the instance at the literal b is j with the literal put for the binder's
variable: its term, and its conditions in order. -/
def instB (c : Semantics) (tbl tblT : VarTable) (vars : List Srt) (Bv : Var) (j : Term × List Cond) (b : Bool)
    (x : Term × List Cond) : Bool :=
  decide ((altPC c tbl (vsBof c vars) j).substEvar (tblT.ev (evarKey Bv.kore)) (den c (bool b)) =
    altPC c tbl (canonVars c vars) x) &&
  decide ((condPats c tbl (vsBof c vars) j.2).map (fun z => z.substEvar (tblT.ev (evarKey Bv.kore)) (den c (bool b))) =
    condPats c tbl (canonVars c vars) x.2)

/-- **The decision of the readings** of `prem → F = (∃B:Bool. body) ∧ ens`, B the text's variable
`Bv`, against the alternatives `xT`, `xF` of the instances at `true` and `false` and the last
clause's alternative j. -/
def exReadB (N : Parse.Names) (c : Semantics) (tbl tblT : VarTable) (vars : List Srt) (vsF : List Var) (Bv : Var)
    (s : Srt) (bodyK en : Kore.Pattern) (xT xF j : Term × List Cond) : Bool :=
  tablesB c tbl tblT vars vsF Bv && bodyB N c tbl tblT vars vsF Bv s bodyK j && ensB c tbl tblT s en &&
    instB c tbl tblT vars Bv j true xT && instB c tbl tblT vars Bv j false xF

section
variable {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- The readings `TieEX`'s lemmas take: `ex_clause_of_text` reads `hin`, `hcond`, `hbody`;
`ex_last_of_text` reads `hxr`, `hinB`, `hcondB`, `hbodyB`; `readings_exB` and `ex_text_of_split`
read them all. -/
structure ExFacts (I : Interpretation KoreAML.Sym M) (c : Semantics) (tbl : VarTable) (vs : List KoreAML.Var)
    (ws : List P) (σ : M) (xsOf : Bool → List (Term × List Cond)) (bs : List (Term × List Cond))
    (body ensT : P) (xB : EVar) (CG CGB : Cond → Valuation M → Prop) : Prop where
  hin : ∀ e m, At I ws (tbl.ev (sortVarKey Rv)) e m → ∀ x ∈ xsOf true ++ xsOf false, ∀ a,
    (altPC c tbl vs x).interpret I e a → Inh I σ a
  hcond : ∀ e m, At I ws (tbl.ev (sortVarKey Rv)) e m → ∀ x ∈ xsOf true ++ xsOf false, ∀ p ∈ x.2,
    ((tr ⟨tbl, []⟩ (Cond.kore c vs R p)).interpret I e m ↔ CG p e)
  hbody : ∀ e m, At I ws (tbl.ev (sortVarKey Rv)) e m → ∀ (b : Bool) (y : M),
    (den c (bool b)).interpret I e y → ∀ a, Inh I σ a →
    (body.interpret I (updX e xB y) a ∧ ensT.interpret I e a ↔
      ∃ x ∈ xsOf b, (altPC c tbl vs x).interpret I e a ∧ altGC CG x e)
  hxr : tbl.ev (evarKey (binderB c vs).kore) ≠ tbl.ev (sortVarKey Rv)
  hinB : ∀ e m, At I ws (tbl.ev (sortVarKey Rv)) e m → ∀ y, (inhOf boolP).interpret I e y → ∀ x ∈ bs, ∀ a,
    (altPC c tbl (vs ++ [binderB c vs]) x).interpret I (updX e (tbl.ev (evarKey (binderB c vs).kore)) y) a →
      Inh I σ a
  hcondB : ∀ e m, At I ws (tbl.ev (sortVarKey Rv)) e m → ∀ y, (inhOf boolP).interpret I e y → ∀ x ∈ bs,
    ∀ p ∈ x.2, ((tr ⟨tbl, []⟩ (Cond.kore c (vs ++ [binderB c vs]) R p)).interpret I
        (updX e (tbl.ev (evarKey (binderB c vs).kore)) y) m ↔
      CGB p (updX e (tbl.ev (evarKey (binderB c vs).kore)) y))
  hbodyB : ∀ e m, At I ws (tbl.ev (sortVarKey Rv)) e m → ∀ y, (inhOf boolP).interpret I e y → ∀ a, Inh I σ a →
    (body.interpret I (updX e xB y) a ∧ ensT.interpret I e a ↔
      ∃ x ∈ bs, (altPC c tbl (vs ++ [binderB c vs]) x).interpret I
          (updX e (tbl.ev (evarKey (binderB c vs).kore)) y) a ∧
        altGC CGB x (updX e (tbl.ev (evarKey (binderB c vs).kore)) y))

/-- **The readings of the split** (`TieFR.Readings`), with `boolClosed`. -/
theorem ExFacts.readings {c : Semantics} (F : HoldsShape.NodeFacts c I) {tbl : VarTable} {vs : List KoreAML.Var}
    {ws : List P} {σ : M} {xsOf : Bool → List (Term × List Cond)} {bs : List (Term × List Cond)}
    {body ensT : P} {xB : EVar} {CG CGB : Cond → Valuation M → Prop}
    (X : ExFacts I c tbl vs ws σ xsOf bs body ensT xB CG CGB) (hcl : I ⊧ᴵ boolClosed c) {s : Srt} {prem : P}
    (hr : sortGuard (tbl.ev (sortVarKey Rv)) ∈ ws)
    (hσ : ∀ (e : Valuation M) a, (trSort tbl (srtOf c s)).interpret I e a ↔ a = σ) (hσS : IsSort I σ) :
    Readings I ws (tbl.ev (sortVarKey Rv)) σ prem (sAnd (sExists xB boolP body) ensT)
      (xsOf true ++ xsOf false) (altPC c tbl vs) (altGC CG)
      (clauseQC c tbl vs s prem) (lastBQC c tbl vs s prem bs) :=
  readings_exB F hcl hr hσ hσS X.hin X.hcond X.hbody X.hxr X.hinB X.hcondB X.hbodyB

/-- What the body gives at a valuation of the guards with B sent to an element y of Bool: the
body's elements are j's term's where each of j's conditions holds on all of R; each of j's
conditions holds at an element of R exactly where it holds on all of R; and j's term lies in σ. -/
theorem binder_core {N : Parse.Names} {c : Semantics} (F : HoldsShape.NodeFacts c I) (hTS : TermsInSort c I)
    (hsy : N.syms = c.symNames) (hso : N.sorts = c.sortNames)
    {tbl tblT : VarTable} {vars : List Srt} {vsF : List Var} {Bv : Var} {s : Srt} {bodyK : Kore.Pattern}
    {j : Term × List Cond} {ws : List P} {σ : M}
    (hvars : Parse.varSorts N vsF = .ok vars) (hg : TieFRVars.guardsHold ws tblT vsF = true)
    (hr : sortGuard (tbl.ev (sortVarKey Rv)) ∈ ws)
    (hσ : ∀ (e : Valuation M) a, (trSort tbl (srtOf c s)).interpret I e a ↔ a = σ)
    (hTab : tablesB c tbl tblT vars vsF Bv = true) (hBody : bodyB N c tbl tblT vars vsF Bv s bodyK j = true)
    {e : Valuation M} {m : M} (hat : At I ws (tbl.ev (sortVarKey Rv)) e m) {y : M}
    (hy : (inhOf boolP).interpret I e y) :
    (∀ a, (tr ⟨tblT, []⟩ bodyK).interpret I (updX e (tblT.ev (evarKey Bv.kore)) y) a ↔
      (altPC c tbl (vsBof c vars) j).interpret I (updX e (tblT.ev (evarKey Bv.kore)) y) a ∧
        ∀ z ∈ condPats c tbl (vsBof c vars) j.2, ∀ m', Inh I (e.evalEvar (tbl.ev (sortVarKey Rv))) m' →
          z.interpret I (updX e (tblT.ev (evarKey Bv.kore)) y) m') ∧
    (∀ z ∈ condPats c tbl (vsBof c vars) j.2, ∀ m', Inh I (e.evalEvar (tbl.ev (sortVarKey Rv))) m' →
      (z.interpret I (updX e (tblT.ev (evarKey Bv.kore)) y) m' ↔
        ∀ m'', Inh I (e.evalEvar (tbl.ev (sortVarKey Rv))) m'' →
          z.interpret I (updX e (tblT.ev (evarKey Bv.kore)) y) m'')) ∧
    ∀ a, (altPC c tbl (vsBof c vars) j).interpret I (updX e (tblT.ev (evarKey Bv.kore)) y) a → Inh I σ a := by
  have hD := F.defOK
  have hc := F.ceilDef
  simp only [tablesB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hTab
  obtain ⟨⟨⟨⟨⟨⟨-, hxr⟩, hrT⟩, hA⟩, hAB⟩, hidx⟩, hlast⟩ := hTab
  simp only [bodyB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hBody
  obtain ⟨⟨⟨⟨⟨hTight, hNum⟩, hTerm⟩, hConds⟩, hty⟩, hs⟩ := hBody
  -- the valuation with B sent to y puts the variables and the binder in their sorts
  have hre : (updX e (tblT.ev (evarKey Bv.kore)) y).evalEvar (tbl.ev (sortVarKey Rv)) =
      e.evalEvar (tbl.ev (sortVarKey Rv)) := Function.update_noteq (Ne.symm hxr) _ _
  have hV : ∀ i < (vars ++ [Srt.bool]).length, InS I (c.sortName ((vars ++ [Srt.bool]).getD i 0))
      ((updX e (tblT.ev (evarKey Bv.kore)) y).evalEvar (tbl.ev (canonKey c (vars ++ [Srt.bool]) i))) := by
    intro i hi
    rw [List.length_append, List.length_singleton] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
    · obtain ⟨h1, h2⟩ := hidx i hlt
      have h0 := TieFRVars.inS_of_guards hD hso hvars hA hg hat.1 (i := i)
        (by rw [← (TieFRVars.varSorts_spec hvars).1]; exact hlt)
      have hg' : (vars ++ [Srt.bool]).getD i 0 = vars.getD i 0 := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      rw [h1, hg']
      show InS I _ (Function.update e.evalEvar _ y _)
      rw [Function.update_noteq h2]
      exact h0
    · have hg' : (vars ++ [Srt.bool]).getD vars.length 0 = Srt.bool := by simp [List.getD_eq_getElem?_getD]
      rw [hlast, hg']
      show InS I _ (Function.update e.evalEvar _ y _)
      rw [Function.update_same]
      have hy' := hy
      rw [← sortP_bool c] at hy'
      exact (inS_iff e).mp hy'
  have hT := tightSem_of_tightB F hTS hsy hso hAB hV hTight
  have hrS : IsSort I ((updX e (tblT.ev (evarKey Bv.kore)) y).evalEvar (tblT.ev (sortVarKey Rv))) := by
    rw [hrT, hre]; exact isSort_of_at hD hr hat
  have hpred : ∀ q ∈ bodyEqs bodyK, ∀ m', (tr ⟨tblT, []⟩ (.equals q.1 R q.2.1 q.2.2)).interpret I
      (updX e (tblT.ev (evarKey Bv.kore)) y) m' ↔
      Inh I (e.evalEvar (tbl.ev (sortVarKey Rv))) m' ∧ EqH I tblT (updX e (tblT.ev (evarKey Bv.kore)) y) q := by
    intro q hq m'
    rw [eqPat_pred hD hc (sortDen_of_sortNumB F (hNum q hq) _) hrS m', hrT, hre]
  refine ⟨fun a => ?_, fun z hz m' hm' => ?_, fun a ha => ?_⟩
  · rw [bodySplit_sem hD hc hT (fun q hq => sortDen_of_sortNumB F (hNum q hq) _) a, hTerm, hConds]
    refine and_congr_right fun _ => ⟨fun h z hz m' hm' => ?_, fun h q hq => ?_⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
      exact (hpred q hq m').mpr ⟨hm', h q hq⟩
    · exact ((hpred q hq m).mp (h _ (List.mem_map.mpr ⟨q, hq, rfl⟩) m hat.2)).2
  · rw [hConds] at hz
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
    constructor
    · intro h m'' hm''
      exact (hpred q hq m'').mpr ⟨hm'', ((hpred q hq m').mp h).2⟩
    · intro h
      exact h m' hm'
  · have hvsB : vsBof c vars = canonVars c (vars ++ [Srt.bool]) := Model.canonVars_snocStdI c vars Srt.bool
    unfold altPC at ha
    rw [hvsB] at ha
    have h := hTS hty hs (fun i hi => hV i (varOccs_lt j.1 hty i hi)) a ha
    rw [← inS_iff e] at h
    have hsp : KoreAML.Cons.sortP (c.sortName s) = trSort tbl (srtOf c s) := by
      rw [srtOf, Faithful.trSort_srt]; rfl
    rw [hsp, interp_inhOf_of (hσ e)] at h
    exact h

/-- **The readings from the decision.** -/
theorem exFacts_of_exB {N : Parse.Names} {c : Semantics} (F : HoldsShape.NodeFacts c I) (hTS : TermsInSort c I)
    (hsy : N.syms = c.symNames) (hso : N.sorts = c.sortNames)
    {tbl tblT : VarTable} {vars : List Srt} {vsF : List Var} {Bv : Var} {s : Srt} {bodyK en : Kore.Pattern}
    {xT xF j : Term × List Cond} {al : List String} {ws : List P} {σ : M}
    (hvars : Parse.varSorts N vsF = .ok vars) (hg : TieFRVars.guardsHold ws tblT vsF = true)
    (hr : sortGuard (tbl.ev (sortVarKey Rv)) ∈ ws)
    (hσ : ∀ (e : Valuation M) a, (trSort tbl (srtOf c s)).interpret I e a ↔ a = σ) (hσS : IsSort I σ)
    (hal : aliasFreeFR al bodyK = true) (hal' : aliasFreeFR al en = true)
    (h : exReadB N c tbl tblT vars vsF Bv s bodyK en xT xF j = true) :
    ExFacts I c tbl (canonVars c vars) ws σ (xsOfB xT xF) [j] (tr ⟨tblT, al⟩ bodyK) (tr ⟨tblT, al⟩ en)
      (tblT.ev (evarKey Bv.kore)) (CGof I c tbl (canonVars c vars)) (CGof I c tbl (vsBof c vars)) := by
  rw [tr_aliasFree tblT al _ hal, tr_aliasFree tblT al _ hal']
  have hD := F.defOK
  have hc := F.ceilDef
  simp only [exReadB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hTab, hBody⟩, hEns⟩, hIT⟩, hIF⟩ := h
  have core := fun {e : Valuation M} {m : M} (hat : At I ws (tbl.ev (sortVarKey Rv)) e m) {y : M}
      (hy : (inhOf boolP).interpret I e y) =>
    binder_core F hTS hsy hso (s := s) (bodyK := bodyK) (j := j) hvars hg hr hσ hTab hBody hat hy
  have hTab' := hTab
  simp only [tablesB, Bool.and_eq_true, decide_eq_true_eq] at hTab'
  obtain ⟨⟨⟨⟨⟨⟨hxBG, hxr⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hTab'
  simp only [ensB, Bool.and_eq_true, decide_eq_true_eq] at hEns
  obtain ⟨hE1, hE2⟩ := hEns
  have hre : ∀ (e : Valuation M) y, (updX e (tblT.ev (evarKey Bv.kore)) y).evalEvar (tbl.ev (sortVarKey Rv)) =
      e.evalEvar (tbl.ev (sortVarKey Rv)) := fun e y => Function.update_noteq (Ne.symm hxr) _ _
  -- the `ensures` part holds all of σ
  have hens : ∀ (e : Valuation M) a, Inh I σ a → (tr ⟨tblT, []⟩ en).interpret I e a := by
    intro e a ha
    rw [ens_reading hD hc (boolDen_of F) hE1 (fun e a => by rw [hE2]; exact hσ e a) hσS e a ha]
    intro b hb; cases hb
  -- the instances: each is j with its literal put for the binder's variable
  have hI : ∀ b, instB c tbl tblT vars Bv j b (bif b then xT else xF) = true := by
    intro b; cases b
    · exact hIF
    · exact hIT
  have hlit : ∀ (e : Valuation M) (b : Bool) (y : M), (den c (bool b)).interpret I e y →
      (inhOf boolP).interpret I e y ∧ ∀ (φ : P) (e' : Valuation M) (m : M),
        (φ.substEvar (tblT.ev (evarKey Bv.kore)) (den c (bool b))).interpret I e' m ↔
          φ.interpret I (updX e' (tblT.ev (evarKey Bv.kore)) y) m := by
    intro e b y hy
    obtain ⟨y0, hy0, hin0⟩ := bool_lit F b e
    have hyy : y = y0 := (hy0 y).mp hy
    have hcl : Closed (den c (bool b)) := by
      rw [den_bool]; exact (Closed.sym _).app (Closed.sym _)
    exact ⟨hyy ▸ hin0, interp_substEvar_one fun e'' m => by rw [hcl.interp e'' e m, hy0 m, hyy]⟩
  have hmemX : ∀ x ∈ xsOfB xT xF true ++ xsOfB xT xF false, ∃ b, x = bif b then xT else xF := by
    intro x hx
    simp only [xsOfB, Bool.cond_true, Bool.cond_false, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨true, rfl⟩
    · exact ⟨false, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e m hat x hx a ha
    obtain ⟨b, rfl⟩ := hmemX x hx
    obtain ⟨y, hy, -⟩ := bool_lit F b e
    obtain ⟨hyB, sub⟩ := hlit e b y ((hy y).mpr rfl)
    have hi := hI b
    simp only [instB, Bool.and_eq_true, decide_eq_true_eq] at hi
    rw [← hi.1, sub] at ha
    exact (core hat hyB).2.2 a ha
  · intro e m hat x hx p hp
    obtain ⟨b, rfl⟩ := hmemX x hx
    obtain ⟨y, hy, -⟩ := bool_lit F b e
    obtain ⟨hyB, sub⟩ := hlit e b y ((hy y).mpr rfl)
    have hi := hI b
    simp only [instB, Bool.and_eq_true, decide_eq_true_eq] at hi
    have hz' : tr ⟨tbl, []⟩ (Cond.kore c (canonVars c vars) R p) ∈
        condPats c tbl (canonVars c vars) (bif b then xT else xF).2 := List.mem_map.mpr ⟨p, hp, rfl⟩
    rw [← hi.2] at hz'
    obtain ⟨z, hz, hzz⟩ := List.mem_map.mp hz'
    unfold CGof
    rw [← hzz]
    simp only [sub]
    exact (core hat hyB).2.1 z hz m hat.2
  · intro e m hat b y hy a ha
    obtain ⟨hyB, sub⟩ := hlit e b y hy
    have hi := hI b
    simp only [instB, Bool.and_eq_true, decide_eq_true_eq] at hi
    rw [(core hat hyB).1 a]
    simp only [xsOfB, List.mem_singleton, exists_eq_left, altGC, CGof]
    rw [← hi.1, sub]
    refine ⟨fun ⟨⟨hA, hC⟩, _⟩ => ⟨hA, fun p hp m' hm' => ?_⟩, fun ⟨hA, hC⟩ => ⟨⟨hA, fun z hz m' hm' => ?_⟩, hens e a ha⟩⟩
    · have hz' : tr ⟨tbl, []⟩ (Cond.kore c (canonVars c vars) R p) ∈
          condPats c tbl (canonVars c vars) (bif b then xT else xF).2 := List.mem_map.mpr ⟨p, hp, rfl⟩
      rw [← hi.2] at hz'
      obtain ⟨z, hz, hzz⟩ := List.mem_map.mp hz'
      rw [← hzz, sub]
      exact hC z hz m' hm'
    · have hz' : z.substEvar (tblT.ev (evarKey Bv.kore)) (den c (bool b)) ∈
          condPats c tbl (canonVars c vars) (bif b then xT else xF).2 := by
        rw [← hi.2]; exact List.mem_map.mpr ⟨z, hz, rfl⟩
      obtain ⟨p, hp, hpz⟩ := List.mem_map.mp hz'
      have := hC p hp m' hm'
      rw [hpz, sub] at this
      exact this
  · rw [hxBG]; exact hxr
  · intro e m hat y hy x hx a ha
    rw [hxBG] at ha
    rw [List.mem_singleton] at hx
    subst hx
    exact (core hat hy).2.2 a ha
  · intro e m hat y hy x hx p hp
    rw [hxBG]
    rw [List.mem_singleton] at hx
    subst hx
    unfold CGof
    rw [hre]
    exact (core hat hy).2.1 _ (List.mem_map.mpr ⟨p, hp, rfl⟩) m hat.2
  · intro e m hat y hy a ha
    rw [hxBG, (core hat hy).1 a]
    have hre' : ∀ (e : Valuation M) y, Function.update e.evalEvar (tblT.ev (evarKey Bv.kore)) y
        (tbl.ev (sortVarKey Rv)) = e.evalEvar (tbl.ev (sortVarKey Rv)) := hre
    simp only [List.mem_singleton, exists_eq_left, altGC, CGof, hre']
    refine ⟨fun ⟨⟨hA, hC⟩, _⟩ => ⟨hA, fun p hp m' hm' => hC _ (List.mem_map.mpr ⟨p, hp, rfl⟩) m' hm'⟩,
      fun ⟨hA, hC⟩ => ⟨⟨hA, fun z hz m' hm' => ?_⟩, hens e a ha⟩⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz
    exact hC p hp m' hm'

end

end TieEXReadB

end KCore
