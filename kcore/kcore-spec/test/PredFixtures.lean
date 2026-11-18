/-
  The fixtures of rules with predicates (CN-4 §4.8, R3 fixture table), read from K 7.1.337 kompile's
  KORE with a connective at a term position cut (`Parse.parse`, which reads it through
  `Parse.connRuleBody`, `ReadingNote.connectiveCut`; and `Parse.andRuleOf`; test/PredReader.lean
  prints the readings). Run from the package root:
  `lake env lean -j1 test/PredFixtures.lean`.

  `definition_of NAME from "file.kore"` adds the definition `Parse.parse` builds;
  `definition_read NAME from "file.kore" by and` the one `Parse.parseWith Parse.andRuleOf` builds.

  ## e3-ml-rule-lhs-not
  `f2-examples/mlnot.kompile.kore` (`test/constructs/fixtures/e3-ml-rule-lhs-not/kore.txt:51-56`):
  `c(#Not(a())) => a()`, kompiled to `<k> c(\not{Exp}(\and{Exp}(a(), _Gen5))) => _Gen5 </k>`, _Gen5
  bound only under `\not`. Read as `c(Z) => G` with `pre := not (and (mem Z a) (mem Z G))`, Z
  (variable 0) bound by the left side, G (variable 3) open and held by the right side under
  constructors. The text's only rule, so the definition has `coreOK` (`coreOK`). For all values z
  and g of Exp, `<k> c(z) </k>` steps to `<k> g </k>` exactly where not (z = a and g = a)
  (`step_iff`): the sentence `c(¬(a ∧ G)) → •G` holds at every G with z outside `a ∧ G`.
  Beside a rule of a larger priority (the definition with the rule `c(Z) => b`, `pre := not (mem Z
  a)`, of priority 200 appended: `cLarger`), G is an open variable of a condition with the variable Z the left side binds, of the
  sort Exp the text leaves unconfined, in a rule that competes with a larger one: `rulesPlain` and
  `coreOK` fail (`larger_refused`) and the reader's message is `openRequires` at Exp.

  ## e3-ml-rule-rhs-or
  `f2-examples/mlror.kompile.kore` (`test/constructs/fixtures/e3-ml-rule-rhs-or/kore.txt:63-68`):
  `go => a() #Or b()`, kompiled with `inj{Exp,KItem}(\or{Exp}(a(), b()))` on the right side. Read as
  `go => ?Z` with `post := or (mem Z a) (mem Z b)`, Z (variable 2) existential, under constructors
  (arm A); `coreOK` holds and the text declares no function (`fnHyp`). `<k> go </k>` steps to
  `<k> a </k>` and to `<k> b </k>` (`step_a`, `step_b`), and every step by the rule is to one of the
  two (`step_inv`). `famEx` is `C[a] ∨ C[b]` at values (`famEx_values_iff`): the values whose
  element is in the family in every model of `Γc` are exactly `<k> a </k>` and `<k> b </k>`
  (`sound_at` one way, `famEx_values` and `step_inv` the other; that `famEx` holds no element off
  the two in a model is not stated). Neither instance is entailed as the successor: by
  `has_model_choice` at `Step` less the step to b (and symmetrically), a model of `Γc` with the
  step's closure in which `den go ⇒ ¬•den b` holds, so `den go ⇒ •den b` is not entailed
  (`not_entailed_b`, `not_entailed_a`, and by `Γc` alone `not_entailed_Γc`).

  ## The conjunction of terms on a right side
  Four texts, each read by `Parse.andRuleOf` (`Parse.andCut`): the definition is the landed reader's
  (`definition_of`) with its rules replaced by the ones `parseWith andRuleOf` reads (its functions,
  sorts and constructors are the landed reading's), which are the landed reader's rules (`parsed`:
  `Parse.ruleBody` reads them through the cut, `andTermsCut`). Each has `coreOK`. The steps are proved from
  `StepBy`, `Holds.mem` and the evaluation of the conjuncts, not through `Exec.step_iff_of_ok`
  (whose `c.ok` asks `\top` predicates of every rule).
  - e3-ml-rule-rhs-and-ctor (mlandc, `c(X) => X #And a()`), e3-ml-rule-rhs-and-var (mlandv,
    `c(X) => a() #And X`): the variable form `c(X) => X` with `post := mem X a` (`VarForm`):
    `c(a)` steps to `a` (`step_ca`) and `c(b)` has no successor (`stuck_cb`).
  - e3-ml-rule-lhs-or-rhs-and (mlorand, `c(X) #Or d(X) => X #And a()`): two rules of the variable
    form, at c and at d: `c(a)` and `d(a)` step to `a`, `c(b)` has no successor.
  - e3-ml-rule-rhs-and-term (mlandt, `go(X) => f(X) #And g(X)`, f the identity, g negation): the
    fresh form `go(X) => ?Z` with `post := and (mem Z f(X)) (mem Z g(X))`. `go(0)` steps to `0` and
    to nothing else (`step_go0_iff`; f(0) and g(0) evaluated by `Exec.evalT_sound` on the clauses
    of the landed reading), `go(1)` has no successor (`stuck_go1`: f(1) = 1, g(1) = -1), and the
    successor of `go(0)` is the one value `famEx` has (`famEx_one`: `sound_at` and `famEx_values`,
    with `FnHyp` from the deciders' empty obligation lists).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore
open ML Faithful

namespace PredFixtures

open Lean Elab Command in
/-- `definition_read NAME from "file.kore" by and`: `def NAME : Definition`, the definition
`Parse.parseWith` builds from the file with the rules read by `Parse.andRuleOf`, added as a term
(not compiled). -/
elab "definition_read " id:ident " from " path:str " by " rd:ident : command => do
  let f ← match rd.getId.toString with
    | "and" => pure Parse.andRuleOf
    | s => throwError "definition_read: no reading function {s}"
  let input ← IO.FS.readFile path.getString
  let k ← match Kore.parseDefinition input with
    | .error e => throwError "definition_read: {path.getString}: KORE read error {e}"
    | .ok k => pure k
  let d ← match Parse.parseWith f k with
    | .ok d => pure d
    | .error r => throwError "definition_read: {path.getString}: refused: {r.toText}"
  let name := (← getCurrNamespace) ++ id.getId
  liftCoreM <| addDecl <| .defnDecl {
    name, levelParams := [], type := mkConst ``Definition, value := definitionExpr d,
    hints := .regular 0, safety := .safe }

/-! ## Inversions -/

theorem holds_not_inv {c : Semantics} {n : Nat} {σ : Subst} {p : Cond} {b : Bool}
    (h : Holds c n σ (.not p) b) : ∃ b', Holds c n σ p b' ∧ b = !b' := by
  generalize hq : Cond.not p = q at h
  cases h with
  | not h => cases hq; exact ⟨_, h, rfl⟩
  | _ => cases hq

theorem holds_and_inv {c : Semantics} {n : Nat} {σ : Subst} {p q : Cond} {b : Bool}
    (h : Holds c n σ (.and p q) b) : ∃ b₁ b₂, Holds c n σ p b₁ ∧ Holds c n σ q b₂ ∧ b = (b₁ && b₂) := by
  generalize hq : Cond.and p q = r at h
  cases h with
  | and h h' => cases hq; exact ⟨_, _, h, h', rfl⟩
  | _ => cases hq

theorem holds_or_inv {c : Semantics} {n : Nat} {σ : Subst} {p q : Cond} {b : Bool}
    (h : Holds c n σ (.or p q) b) : ∃ b₁ b₂, Holds c n σ p b₁ ∧ Holds c n σ q b₂ ∧ b = (b₁ || b₂) := by
  generalize hq : Cond.or p q = r at h
  cases h with
  | or h h' => cases hq; exact ⟨_, _, h, h', rfl⟩
  | _ => cases hq

theorem holds_mem_inv {c : Semantics} {n : Nat} {σ : Subst} {s : Srt} {t u : Term} {b : Bool}
    (h : Holds c n σ (.mem s t u) b) :
    ∃ r r', EvalTerm c σ t r ∧ EvalTerm c σ u r' ∧ b = (r.isSome && sameResult r r') := by
  generalize hq : Cond.mem s t u = q at h
  cases h with
  | mem h h' => cases hq; exact ⟨_, _, h, h', rfl⟩
  | _ => cases hq

/-- A nullary constructor evaluates to itself. -/
theorem evalTerm_const {c : Semantics} {σ : Subst} {f : Sym} {r : Option GroundTerm}
    (hc : c.isCtor f = true) (h : EvalTerm c σ (.app f []) r) : r = some (.ctor f []) := by
  obtain ⟨rs, hrs, rfl⟩ := EvalTerm.ctor_inv hc h
  cases EvalTerms.nil_inv hrs
  rfl

/-- `sameResult` of two results is their equality. -/
theorem sameResult_some {v w : GroundTerm} : sameResult (some v) (some w) = decide (v = w) := by
  unfold sameResult
  by_cases h : v = w
  · subst h; simp [cmp_eq_iff]
  · simp [cmp_eq_iff, h]

/-- An injection's normal form is the injection of a term that is no injection. -/
theorem injNormal_of_not_inj {a b : Srt} {v : GroundTerm} (h : v.isInj = false) :
    injNormal a b v = .inj a b v := by
  cases v <;> first | rfl | cases h

/-- A value of a sort no sort lies below is no injection. -/
theorem isInj_of_sort {c : Semantics} {s : Srt} (hs : ∀ p ∈ c.subsorts, p.2 ≠ s) {v : GroundTerm}
    (hv : c.sortOf v = some s) : v.isInj = false := by
  cases v with
  | inj a b w =>
    simp only [Semantics.sortOf] at hv
    split at hv
    · rename_i hc
      simp only [Bool.and_eq_true, List.contains_iff_mem] at hc
      cases hv
      exact absurd rfl (hs _ hc.1.1)
    · cases hv
  | _ => rfl

theorem allSome_cons {r : Option GroundTerm} {rs : List (Option GroundTerm)} {v : GroundTerm}
    {vs : List GroundTerm} (h : allSome (r :: rs) = some (v :: vs)) : r = some v ∧ allSome rs = some vs := by
  cases r with
  | none => cases h
  | some w =>
    simp only [allSome, Option.bind_some] at h
    cases hr : allSome rs with
    | none => rw [hr] at h; cases h
    | some ws => rw [hr] at h; cases h; exact ⟨rfl, rfl⟩

/-- A constructor application evaluating to a constructor term of two arguments: the two
arguments' results. -/
theorem evalTerm_ctor2 {c : Semantics} {σ : Subst} {f : Sym} {t u : Term} {v w : GroundTerm}
    (hc : c.isCtor f = true) (h : EvalTerm c σ (.app f [t, u]) (some (.ctor f [v, w]))) :
    EvalTerm c σ t (some v) ∧ EvalTerm c σ u (some w) := by
  obtain ⟨rs, hrs, he⟩ := EvalTerm.ctor_inv hc h
  obtain ⟨r1, rs1, rfl, h1, hrs1⟩ := EvalTerms.cons_inv hrs
  obtain ⟨r2, rs2, rfl, h2, hrs2⟩ := EvalTerms.cons_inv hrs1
  cases EvalTerms.nil_inv hrs2
  cases ha : allSome [r1, r2] with
  | none => rw [ha] at he; cases he
  | some vs =>
    rw [ha] at he
    cases he
    obtain ⟨rfl, h'⟩ := allSome_cons ha
    obtain ⟨rfl, -⟩ := allSome_cons h'
    exact ⟨h1, h2⟩

/-- A constructor application evaluating to a constructor term of one argument. -/
theorem evalTerm_ctor1 {c : Semantics} {σ : Subst} {f : Sym} {t : Term} {v : GroundTerm}
    (hc : c.isCtor f = true) (h : EvalTerm c σ (.app f [t]) (some (.ctor f [v]))) :
    EvalTerm c σ t (some v) := by
  obtain ⟨rs, hrs, he⟩ := EvalTerm.ctor_inv hc h
  obtain ⟨r1, rs1, rfl, h1, hrs1⟩ := EvalTerms.cons_inv hrs
  cases EvalTerms.nil_inv hrs1
  cases ha : allSome [r1] with
  | none => rw [ha] at he; cases he
  | some vs =>
    rw [ha] at he
    cases he
    obtain ⟨rfl, -⟩ := allSome_cons ha
    exact h1

/-- The pattern of a constructor application of two arguments at a constructor term. -/
theorem patVal_ctor2 {c : Semantics} {σ : Subst} {f : Sym} {p q : Term} {v w : GroundTerm}
    (hf : patternHooks.contains f = false) (hc : c.isCtor f = true)
    (h : PatVal c σ (.app f [p, q]) (.ctor f [v, w])) : PatVal c σ p v ∧ PatVal c σ q w := by
  obtain ⟨-, vs, he, hs⟩ := PatVal.app_inv hf h hc
  cases he
  obtain ⟨_, _, he1, h1, hs1⟩ := PatVals.cons_inv hs
  cases he1
  obtain ⟨_, _, he2, h2, _⟩ := PatVals.cons_inv hs1
  cases he2
  exact ⟨h1, h2⟩

theorem patVal_ctor1 {c : Semantics} {σ : Subst} {f : Sym} {p : Term} {v : GroundTerm}
    (hf : patternHooks.contains f = false) (hc : c.isCtor f = true)
    (h : PatVal c σ (.app f [p]) (.ctor f [v])) : PatVal c σ p v := by
  obtain ⟨-, vs, he, hs⟩ := PatVal.app_inv hf h hc
  cases he
  obtain ⟨_, _, he1, h1, _⟩ := PatVals.cons_inv hs
  cases he1
  exact h1

/-- The configuration `<generatedTop>(<k>(kseq(inj{s,KItem}(st), dotk)), <generatedCounter>(0))`,
the k cell's symbol `kCell`. -/
def cfgOf (kCell : Sym) (s : Srt) (st : GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor kseq [.inj s Srt.kitem st, .ctor dotk []]], .ctor counterLabel [int 0]]

/-- The configuration pattern `<generatedTop>(<k>(kseq(inj{s,KItem}(p), Vk)), Vc)`. -/
def cfgPat (kCell : Sym) (s : Srt) (p : Term) (k c : Nat) : Term :=
  .app topLabel [.app kCell [.app kseq [.inj s Srt.kitem p, .var k]], .var c]

theorem sortOf_ctor_congr {c : Semantics} {f : Sym} {ts ts0 : List GroundTerm}
    (hl : (lookupSig c.ctorSigs f).isSome = true)
    (h : c.sortsOf ts = c.sortsOf ts0) : c.sortOf (.ctor f ts) = c.sortOf (.ctor f ts0) := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hl
  simp only [Semantics.sortOf, hk, h]

theorem sortsOf_head_congr {c : Semantics} {t t0 : GroundTerm} {ts : List GroundTerm}
    (h : c.sortOf t = c.sortOf t0) : c.sortsOf (t :: ts) = c.sortsOf (t0 :: ts) := by
  simp only [Semantics.sortsOf, h]

theorem sortOf_inj_congr {c : Semantics} {a b : Srt} {t t0 : GroundTerm} (h : c.sortOf t = c.sortOf t0)
    (hi : t.isInj = t0.isInj) : c.sortOf (.inj a b t) = c.sortOf (.inj a b t0) := by
  simp only [Semantics.sortOf, h, hi]

/-- `cfgOf kCell s st` has the sort of `cfgOf kCell s st0` where st and st0 have one sort and
neither is an injection. -/
theorem sortOf_cfgOf_congr {c : Semantics} {kCell : Sym} {s : Srt} {st st0 : GroundTerm}
    (hl : (lookupSig c.ctorSigs topLabel).isSome = true ∧ (lookupSig c.ctorSigs kCell).isSome = true ∧
      (lookupSig c.ctorSigs kseq).isSome = true)
    (h : c.sortOf st = c.sortOf st0) (hi : st.isInj = st0.isInj) :
    c.sortOf (cfgOf kCell s st) = c.sortOf (cfgOf kCell s st0) :=
  sortOf_ctor_congr hl.1 (sortsOf_head_congr (sortOf_ctor_congr hl.2.1 (sortsOf_head_congr
    (sortOf_ctor_congr hl.2.2 (sortsOf_head_congr (sortOf_inj_congr h hi))))))

/-- A model of `Γc` with the step's closure in which `den x ⇒ ¬•den y` holds: then the theory does
not entail `den x ⇒ •den y` (x's element is in `den x`). -/
theorem not_entailed_of_model {c : Semantics} {x y : Config c} {M : Type} [Inhabited M]
    {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP (Γc c ∪ Γstep c))
    (h : I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) :
    ¬ ((Γc c ∪ Γstep c) ⊧ (den c x.val ⇒ KoreAML.sNext (den c y.val))) := by
  intro hE
  have h1 := hE hI
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl (Or.inl hφ))
  let e : Valuation M := ⟨fun _ => default, fun _ _ => False⟩
  have hm := ((elemOf_spec hIΓ x.property e).1 (elemOf c I x.val)).mpr rfl
  have a1 := h1 e (elemOf c I x.val)
  have a2 := h e (elemOf c I x.val)
  rw [interpret_impl] at a1 a2
  exact (interpret_neg.mp (a2 hm)) (a1 hm)

/-- `famEx` reads σ off the existential variables only. -/
theorem famEx_congr_off (c : Semantics) (r : Rule) {σ σ' : Subst}
    (h : ∀ i, i ∉ r.exs → σ'.lookup i = σ.lookup i) : famEx c r σ' = famEx c r σ := by
  unfold famEx
  dsimp only
  rw [fixK_congrOpen c r fun i hi => h i (by simpa using (List.mem_filter.mp hi).2)]

/-- A constructor application of two arguments with a result: the constructor term of the two
arguments' results. -/
theorem evalTerm_ctor2_ex {c : Semantics} {σ : Subst} {f : Sym} {t u : Term} {v : GroundTerm}
    (hc : c.isCtor f = true) (h : EvalTerm c σ (.app f [t, u]) (some v)) :
    ∃ v₁ v₂, v = .ctor f [v₁, v₂] ∧ EvalTerm c σ t (some v₁) ∧ EvalTerm c σ u (some v₂) := by
  obtain ⟨rs, hrs, he⟩ := EvalTerm.ctor_inv hc h
  obtain ⟨r1, rs1, rfl, h1, hrs1⟩ := EvalTerms.cons_inv hrs
  obtain ⟨r2, rs2, rfl, h2, hrs2⟩ := EvalTerms.cons_inv hrs1
  cases EvalTerms.nil_inv hrs2
  cases r1 with
  | none => cases he
  | some v₁ =>
    cases r2 with
    | none => cases he
    | some v₂ => cases he; exact ⟨v₁, v₂, rfl, h1, h2⟩

/-- A constructor application of one argument with a result. -/
theorem evalTerm_ctor1_ex {c : Semantics} {σ : Subst} {f : Sym} {t : Term} {v : GroundTerm}
    (hc : c.isCtor f = true) (h : EvalTerm c σ (.app f [t]) (some v)) :
    ∃ v₁, v = .ctor f [v₁] ∧ EvalTerm c σ t (some v₁) := by
  obtain ⟨rs, hrs, he⟩ := EvalTerm.ctor_inv hc h
  obtain ⟨r1, rs1, rfl, h1, hrs1⟩ := EvalTerms.cons_inv hrs
  cases EvalTerms.nil_inv hrs1
  cases r1 with
  | none => cases he
  | some v₁ => cases he; exact ⟨v₁, rfl, h1⟩

/-- An evaluation of `cfgPat kCell s p k c` to a value: the value is `cfgOf kCell s w` where p
evaluates to w, V_k is `.` and V_c the counter at 0. -/
theorem evalTerm_cfgPat {c : Semantics} {σ : Subst} {kCell : Sym} {s : Srt} {p : Term} {k i : Nat}
    {v : GroundTerm} (hc : c.isCtor topLabel = true ∧ c.isCtor kCell = true ∧ c.isCtor kseq = true)
    (hk : σ.lookup k = some (.ctor dotk [])) (hi : σ.lookup i = some (.ctor counterLabel [int 0]))
    (h : EvalTerm c σ (cfgPat kCell s p k i) (some v)) :
    ∃ w, EvalTerm c σ p (some w) ∧ v = .ctor topLabel [.ctor kCell [.ctor kseq
      [injNormal s Srt.kitem w, .ctor dotk []]], .ctor counterLabel [int 0]] := by
  obtain ⟨v₁, v₂, rfl, h1, h2⟩ := evalTerm_ctor2_ex hc.1 h
  obtain ⟨u, rfl, h3⟩ := evalTerm_ctor1_ex hc.2.1 h1
  obtain ⟨u₁, u₂, rfl, h4, h5⟩ := evalTerm_ctor2_ex hc.2.2 h3
  obtain ⟨r', h6, hr⟩ := EvalTerm.inj_inv h4
  have e5 := EvalTerm.var_inv h5
  have e2 := EvalTerm.var_inv h2
  rw [hk] at e5
  rw [hi] at e2
  cases e5
  cases e2
  cases r' with
  | none => cases hr
  | some w =>
    simp only [Option.map_some, Option.some.injEq] at hr
    subst hr
    exact ⟨w, h6, rfl⟩

/-- A match of `cfgPat kCell s p k i` at `cfgOf kCell s st`: p matches a w whose injection is st's, and
V_k, V_c are `.` and the counter. -/
theorem patVal_cfgPat {c : Semantics} {σ : Subst} {kCell : Sym} {s : Srt} {p : Term} {k i : Nat}
    {st : GroundTerm} (hc : c.isCtor topLabel = true ∧ c.isCtor kCell = true ∧ c.isCtor kseq = true)
    (hh : patternHooks.contains topLabel = false ∧ patternHooks.contains kCell = false ∧
      patternHooks.contains kseq = false)
    (h : PatVal c σ (cfgPat kCell s p k i) (cfgOf kCell s st)) :
    (∃ w, PatVal c σ p w ∧ injNormal s Srt.kitem w = .inj s Srt.kitem st) ∧
      σ.lookup k = some (.ctor dotk []) ∧ σ.lookup i = some (.ctor counterLabel [int 0]) := by
  have ⟨h1, hc'⟩ := patVal_ctor2 hh.1 hc.1 h
  have h2 := patVal_ctor1 hh.2.1 hc.2.1 h1
  have ⟨h3, hk'⟩ := patVal_ctor2 hh.2.2 hc.2.2 h2
  obtain ⟨w, hw, he⟩ := PatVal.inj_inv h3
  exact ⟨⟨w, hw, he.symm⟩, PatVal.var_inv hk', PatVal.var_inv hc'⟩

/-! ## e3-ml-rule-lhs-not -/

namespace LhsNot

definition_of defn from "f2-examples/mlnot.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def exp : Srt := 32
def kCell : Sym := 383
def symA : Sym := 385
def symC : Sym := 387

theorem names_ok : c.sortName exp = "Exp" ∧ c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧
    c.symName symA = "Lbla" ∧ c.symName symC = "Lblc" := by
  decide +kernel

/-- **Admitted as the only rule**: the definition with the rule `c(Z) => G` has `coreOK`. -/
theorem coreOK : c.coreOK = true := by decide +kernel

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)

theorem r0_mem : r0 ∈ c.rules := List.getElem_mem _

/-- The text has the one rule. -/
theorem rule_eq {r : Rule} (hr : r ∈ c.rules) : r = r0 := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have h1 : c.rules.length = 1 := by decide +kernel
  have : i = 0 := by omega
  subst this
  rfl

theorem r0_vars : r0.vars = [exp, Srt.k, 19, exp] := by decide +kernel
theorem r0_lhs : r0.lhs = cfgPat kCell exp (.app symC [.var 0]) 1 2 := rfl
theorem r0_rhs : r0.rhs = cfgPat kCell exp (.var 3) 1 2 := rfl
/-- `pre := not (and (mem Z a) (mem Z G))`, Z the variable 0, G the variable 3. -/
theorem r0_shape : r0.req = none ∧ r0.ens = none ∧ r0.exs = [] ∧ r0.post = .top ∧
    r0.pre = .not (.and (.mem exp (.var 0) (.app symA [])) (.mem exp (.var 0) (.var 3))) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem syms_ok : c.isCtor topLabel = true ∧ c.isCtor kCell = true ∧ c.isCtor kseq = true ∧
    c.isCtor symA = true ∧ c.isCtor symC = true ∧ c.isCtor dotk = true ∧ c.isCtor counterLabel = true := by
  decide +kernel

theorem hooks_ok : patternHooks.contains topLabel = false ∧ patternHooks.contains kCell = false ∧
    patternHooks.contains kseq = false ∧ patternHooks.contains symC = false := by
  decide +kernel

theorem lookups_ok : (lookupSig c.ctorSigs topLabel).isSome = true ∧ (lookupSig c.ctorSigs kCell).isSome = true ∧
    (lookupSig c.ctorSigs kseq).isSome = true ∧ (lookupSig c.ctorSigs symC).isSome = true := by
  decide +kernel

/-- No sort lies below Exp. -/
theorem exp_bottom : ∀ p ∈ c.subsorts, p.2 ≠ exp := by
  intro p hp
  have h : c.subsorts.all (fun p => p.2 != exp) = true := by decide +kernel
  simpa using List.all_eq_true.mp h p hp

/-! ### The configurations -/

def A : GroundTerm := .ctor symA []
def ctr : GroundTerm := .ctor counterLabel [int 0]
def cfg (st : GroundTerm) : GroundTerm := cfgOf kCell exp st

theorem sortOf_A : c.sortOf A = some exp := by decide +kernel

theorem sortOf_cfg {g : GroundTerm} (hg : c.sortOf g = some exp) : c.sortOf (cfg g) = some topCellSort := by
  have h0 : c.sortOf (cfg A) = some topCellSort := by decide +kernel
  rw [← h0]
  exact sortOf_cfgOf_congr ⟨lookups_ok.1, lookups_ok.2.1, lookups_ok.2.2.1⟩ (by rw [hg, sortOf_A])
    (by rw [isInj_of_sort exp_bottom hg]; rfl)

theorem sortOf_cfgC {z : GroundTerm} (hz : c.sortOf z = some exp) :
    c.sortOf (cfg (.ctor symC [z])) = some topCellSort := by
  have h0 : c.sortOf (cfg (.ctor symC [A])) = some topCellSort := by decide +kernel
  rw [← h0]
  exact sortOf_cfgOf_congr ⟨lookups_ok.1, lookups_ok.2.1, lookups_ok.2.2.1⟩
    (sortOf_ctor_congr lookups_ok.2.2.2 (sortsOf_head_congr (by rw [hz, sortOf_A]))) rfl

/-- `<k> c(z) </k>`. -/
def C (z : GroundTerm) (hz : c.sortOf z = some exp) : Config c := ⟨cfg (.ctor symC [z]), sortOf_cfgC hz⟩
/-- `<k> g </k>`. -/
def G (g : GroundTerm) (hg : c.sortOf g = some exp) : Config c := ⟨cfg g, sortOf_cfg hg⟩

/-! ### The step -/

def σ (z g : GroundTerm) : Subst := [(0, z), (1, .ctor dotk []), (2, ctr), (3, g)]

/-- `pre` under any σ: false exactly where σ gives Z the value `a` and G the value Z has. -/
theorem pre_holds (τ : Subst) : Holds c r0.vars.length τ r0.pre
    (!(((τ.lookup 0).isSome && sameResult (τ.lookup 0) (some A)) &&
      ((τ.lookup 0).isSome && sameResult (τ.lookup 0) (τ.lookup 3)))) := by
  rw [r0_shape.2.2.2.2]
  exact .not (.and (.mem .var (.ctor syms_ok.2.2.2.1 .nil)) (.mem .var .var))

/-- The truth value of `pre` under any σ is `pre_holds`'s. -/
theorem pre_val {τ : Subst} {b : Bool} (h : Holds c r0.vars.length τ r0.pre b) :
    b = (!(((τ.lookup 0).isSome && sameResult (τ.lookup 0) (some A)) &&
      ((τ.lookup 0).isSome && sameResult (τ.lookup 0) (τ.lookup 3)))) := by
  rw [r0_shape.2.2.2.2] at h
  obtain ⟨b', hp, rfl⟩ := holds_not_inv h
  obtain ⟨b₁, b₂, h₁, h₂, rfl⟩ := holds_and_inv hp
  obtain ⟨r₁, r₁', e₁, e₁', rfl⟩ := holds_mem_inv h₁
  obtain ⟨r₂, r₂', e₂, e₂', rfl⟩ := holds_mem_inv h₂
  rw [EvalTerm.var_inv e₁, evalTerm_const syms_ok.2.2.2.1 e₁', EvalTerm.var_inv e₂, EvalTerm.var_inv e₂']
  rfl

/-- `pre` where σ gives Z the value z and G the value g. -/
theorem pre_at {τ : Subst} {z g : GroundTerm} (h0 : τ.lookup 0 = some z) (h3 : τ.lookup 3 = some g) {b : Bool} :
    Holds c r0.vars.length τ r0.pre b ↔ b = !(decide (z = A) && decide (z = g)) := by
  constructor
  · intro h
    rw [pre_val h, h0, h3]
    simp only [Option.isSome_some, Bool.true_and, sameResult_some]
  · intro hb
    have h := pre_holds τ
    rw [h0, h3] at h
    simp only [Option.isSome_some, Bool.true_and, sameResult_some] at h
    rw [hb]; exact h

theorem prio_none {r' : Rule} (hr' : r' ∈ c.rules) (hlt : r'.prio < r0.prio) : False := by
  rw [rule_eq hr'] at hlt
  exact Nat.lt_irrefl _ hlt

theorem stepBy {z g : GroundTerm} (hz : c.sortOf z = some exp) (hg : c.sortOf g = some exp)
    (hne : ¬ (z = A ∧ g = A)) : StepBy c r0 (σ z g) (C z hz) (G g hg) where
  mem := r0_mem
  hσ := fun j s hs => by
    rw [r0_vars] at hs
    match j, hs with
    | 0, hs => cases hs; exact ⟨_, rfl, hz⟩
    | 1, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
    | 2, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
    | 3, hs => cases hs; exact ⟨_, rfl, hg⟩
  hmatch := by
    rw [r0_lhs]
    have hiz : injNormal exp Srt.kitem (.ctor symC [z]) = .inj exp Srt.kitem (.ctor symC [z]) := rfl
    exact .ctor syms_ok.1 (.cons (.ctor syms_ok.2.1 (.cons (.ctor syms_ok.2.2.1
      (.cons (hiz ▸ .inj (.ctor syms_ok.2.2.2.2.1 (.cons (.var rfl) .nil))) (.cons (.var rfl) .nil))) .nil))
      (.cons (.var rfl) .nil))
  hreq := fun t ht => by rw [r0_shape.1] at ht; cases ht
  hpre := (pre_at rfl rfl).mpr (by
    by_cases ha : z = A
    · subst ha
      have : g ≠ A := fun h => hne ⟨rfl, h⟩
      simp [Ne.symm this]
    · simp [ha])
  heval := by
    rw [r0_rhs]
    have hig : injNormal exp Srt.kitem g = .inj exp Srt.kitem g := injNormal_of_not_inj (isInj_of_sort exp_bottom hg)
    have he : EvalTerm c (σ z g) (.inj exp Srt.kitem (.var 3)) (((σ z g).lookup 3).map (injNormal exp Srt.kitem)) :=
      .inj .var
    have hv : ((σ z g).lookup 3).map (injNormal exp Srt.kitem) = some (.inj exp Srt.kitem g) := by
      show (some g).map _ = _
      rw [Option.map_some, hig]
    rw [hv] at he
    exact .ctor syms_ok.1 (.cons (.ctor syms_ok.2.1 (.cons (.ctor syms_ok.2.2.1
      (.cons he (.cons .var .nil))) .nil)) (.cons .var .nil))
  hens := fun t ht => by rw [r0_shape.2.1] at ht; cases ht
  hpost := by rw [r0_shape.2.2.2.1]; exact .top
  hprio := fun r' hr' hlt => (prio_none hr' hlt).elim

/-- A match of the left side at `<k> c(z) </k>` gives Z the value z. -/
theorem lookup0 {τ : Subst} {z : GroundTerm} (hm : PatVal c τ r0.lhs (cfg (.ctor symC [z]))) :
    τ.lookup 0 = some z := by
  rw [r0_lhs] at hm
  have h1 := (patVal_ctor2 hooks_ok.1 syms_ok.1 hm).1
  have h2 := patVal_ctor1 hooks_ok.2.1 syms_ok.2.1 h1
  have h3 := (patVal_ctor2 hooks_ok.2.2.1 syms_ok.2.2.1 h2).1
  obtain ⟨w, hw, he⟩ := PatVal.inj_inv h3
  obtain ⟨-, vs, rfl, hs⟩ := PatVal.app_inv hooks_ok.2.2.2 hw syms_ok.2.2.2.2.1
  have he' : GroundTerm.inj exp Srt.kitem (.ctor symC [z]) = .inj exp Srt.kitem (.ctor symC vs) := he
  cases he'
  obtain ⟨_, _, he1, h4, _⟩ := PatVals.cons_inv hs
  cases he1
  exact PatVal.var_inv h4

/-- An evaluation of the right side to `<k> g </k>` gives G the value g. -/
theorem lookup3 {τ : Subst} {g : GroundTerm} (hτ : c.WellSorted r0.vars τ)
    (he : EvalTerm c τ r0.rhs (some (cfg g))) : τ.lookup 3 = some g := by
  obtain ⟨v₃, hl₃, hv₃⟩ := hτ 3 exp (by rw [r0_vars]; rfl)
  rw [r0_rhs] at he
  have h1 := (evalTerm_ctor2 syms_ok.1 he).1
  have h2 := evalTerm_ctor1 syms_ok.2.1 h1
  have h3 := (evalTerm_ctor2 syms_ok.2.2.1 h2).1
  obtain ⟨r', h4, hr⟩ := EvalTerm.inj_inv h3
  rw [EvalTerm.var_inv h4] at hr
  cases hl : τ.lookup 3 with
  | none => rw [hl] at hr; cases hr
  | some v =>
    rw [hl] at hr
    simp only [Option.map_some, Option.some.injEq] at hr
    cases v with
    | inj a b w =>
      rw [hl] at hl₃
      cases hl₃
      cases isInj_of_sort exp_bottom hv₃
    | _ => simp only [injNormal] at hr; cases hr; rfl

/-- **`<k> c(z) </k>` steps to `<k> g </k>` exactly where not (z = a and g = a)**, for all values z
and g of Exp. -/
theorem step_iff {z g : GroundTerm} (hz : c.sortOf z = some exp) (hg : c.sortOf g = some exp) :
    Step c (C z hz) (G g hg) ↔ ¬ (z = A ∧ g = A) := by
  constructor
  · intro h ⟨hza, hga⟩
    obtain ⟨r, τ, hs⟩ := step_iff_by.mp h
    have hr := rule_eq hs.mem
    subst hr
    have h0 := lookup0 hs.hmatch
    have h3 := lookup3 hs.hσ hs.heval
    have hf := (pre_at h0 h3).mp hs.hpre
    rw [hza, hga] at hf
    simp at hf
  · intro hne
    exact step_iff_by.mpr ⟨r0, σ z g, stepBy hz hg hne⟩

/-! ### Beside a rule of a larger priority -/

def symB : Sym := 386

/-- `c(Z) => b` with `pre := not (mem Z a)` at the priority 200: the shape of
e3-ml-rule-lhs-not-other's `c(#Not(a())) => b()`, written by hand. -/
def rOther : Rule :=
  { vars := [exp, Srt.k, 19], lhs := cfgPat kCell exp (.app symC [.var 0]) 1 2, req := none,
    rhs := cfgPat kCell exp (.app symB []) 1 2, ens := none, prio := 200,
    pre := .not (.mem exp (.var 0) (.app symA [])) }

/-- The definition's semantics with `rOther` appended. -/
noncomputable def cLarger : Semantics := { c with rules := c.rules ++ [rOther] }

/-- **Beside a rule of a larger priority the rule is refused**: in `cLarger` the rule `c(Z) => G`
competes with `rOther`, and G (variable 3), of the unconfined sort Exp, is open in `pre`, which
also reads Z, bound by the left side: the rule's conjunct of `rulesPlain` fails, and `coreOK`
with it. `rOther` alone is well sorted with the conjunct. -/
theorem larger_refused : c.confined exp = false ∧ r0.opens = [3] ∧ cLarger.rulePlainPP r0 = false ∧
    cLarger.ruleSorted rOther = true ∧ cLarger.rulePlainPP rOther = true ∧
    cLarger.rulesPlain = false ∧ cLarger.coreOK = false := by
  decide +kernel

/-- The reader's message for the rule in `cLarger`. -/
def largerMessage : IO Unit := do
  match Kore.parseDefinition (← IO.FS.readFile "f2-examples/mlnot.kompile.kore") with
  | .error e => IO.println s!"KORE read error {e}"
  | .ok k => match Parse.parse k with
    | .error r => IO.println s!"refused {r.reason.name}"
    | .ok d =>
      let c' : Semantics := { d.sem with rules := d.sem.rules ++ [rOther] }
      match d.sem.rules.head?, d.pres.rules.head? with
      | some r, some p => IO.println s!"{(Parse.openRefusal c' r p.names).map fun x => (x.1.name, x.2)}"
      | _, _ => IO.println "no rule"

/--
info: (some (openRequires, Var'Unds'Gen5:Exp: in a condition with a variable the left side binds, of a sort the text leaves unconfined, in a rule of a priority below another's))
-/
#guard_msgs in
#eval largerMessage

/-- info: 'PredFixtures.LhsNot.step_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_iff
/-- info: 'PredFixtures.LhsNot.larger_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms larger_refused

end LhsNot

/-! ## e3-ml-rule-rhs-or -/

namespace RhsOr

definition_of defn from "f2-examples/mlror.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def exp : Srt := 32
def kCell : Sym := 383
def symA : Sym := 385
def symB : Sym := 386
def symGo : Sym := 389

theorem names_ok : c.sortName exp = "Exp" ∧ c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧
    c.symName symA = "Lbla" ∧ c.symName symB = "Lblb" ∧ c.symName symGo = "Lblgo" := by
  decide +kernel

/-- **Admitted**: the definition with the rule `go => ?Z` has `coreOK`. -/
theorem coreOK : c.coreOK = true := by decide +kernel

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)

theorem r0_mem : r0 ∈ c.rules := List.getElem_mem _

/-- The text has the one rule. -/
theorem rule_eq {r : Rule} (hr : r ∈ c.rules) : r = r0 := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have h1 : c.rules.length = 1 := by decide +kernel
  have : i = 0 := by omega
  subst this
  rfl

theorem r0_vars : r0.vars = [Srt.k, 19, exp] := by decide +kernel
theorem r0_lhs : r0.lhs = cfgPat kCell exp (.app symGo []) 0 1 := rfl
theorem r0_rhs : r0.rhs = cfgPat kCell exp (.var 2) 0 1 := rfl
/-- `go => ?Z` with `post := or (mem Z a) (mem Z b)`, Z the variable 2. -/
theorem r0_shape : r0.req = none ∧ r0.ens = none ∧ r0.exs = [2] ∧ r0.pre = .top ∧
    r0.post = .or (.mem exp (.var 2) (.app symA [])) (.mem exp (.var 2) (.app symB [])) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem syms_ok : c.isCtor topLabel = true ∧ c.isCtor kCell = true ∧ c.isCtor kseq = true ∧
    c.isCtor symA = true ∧ c.isCtor symB = true ∧ c.isCtor symGo = true ∧ c.isCtor dotk = true := by
  decide +kernel

theorem hooks_ok : patternHooks.contains topLabel = false ∧ patternHooks.contains kCell = false ∧
    patternHooks.contains kseq = false ∧ patternHooks.contains symGo = false := by
  decide +kernel

/-- The text declares no function and no open generator, and no rule needs a witness. -/
theorem fns_nil : c.fns = [] := by decide +kernel
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem noWitness : ∀ r ∈ c.rules, r.needsWitness c = false := by decide +kernel
theorem lhs_vars : ∀ j ∈ varOccs r0.lhs, j < 2 := by decide +kernel

theorem fnHyp : FnHyp c :=
  have hn : ∀ fn, fn ∈ c.fns → False := fun fn hfn => by rw [fns_nil] at hfn; cases hfn
  ⟨fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim,
    fun fn hfn => (hn fn hfn).elim,
    openDecided_of_plain noWitness (fun fn hfn => (hn fn hfn).elim),
    openLaws_of_plain noRaw⟩

theorem fnDet : FnDet c := (fnModel_of_fnHyp coreOK fnHyp).1

/-! ### The configurations -/

def dotkT : GroundTerm := .ctor dotk []
def ctr : GroundTerm := .ctor counterLabel [int 0]
def cfg (st : GroundTerm) : GroundTerm := cfgOf kCell exp st
def a : GroundTerm := .ctor symA []
def b : GroundTerm := .ctor symB []

/-- `<k> go </k>`. -/
def Go : Config c := ⟨cfg (.ctor symGo []), by decide +kernel⟩
/-- `<k> a </k>`, `<k> b </k>`. -/
def A : Config c := ⟨cfg a, by decide +kernel⟩
def B : Config c := ⟨cfg b, by decide +kernel⟩

theorem A_ne_B : A ≠ B := fun h => absurd (congrArg Subtype.val h) (by decide +kernel)

/-! ### `Step` from `go` to `a` and to `b` -/

/-- `post` where σ gives Z the value v. -/
theorem post_at {τ : Subst} {v : GroundTerm} (h2 : τ.lookup 2 = some v) {bv : Bool} :
    Holds c r0.vars.length τ r0.post bv ↔ bv = (decide (v = a) || decide (v = b)) := by
  rw [r0_shape.2.2.2.2]
  constructor
  · intro h
    obtain ⟨b₁, b₂, h₁, h₂, rfl⟩ := holds_or_inv h
    obtain ⟨r₁, r₁', e₁, e₁', rfl⟩ := holds_mem_inv h₁
    obtain ⟨r₂, r₂', e₂, e₂', rfl⟩ := holds_mem_inv h₂
    rw [EvalTerm.var_inv e₁, evalTerm_const syms_ok.2.2.2.1 e₁', EvalTerm.var_inv e₂,
      evalTerm_const syms_ok.2.2.2.2.1 e₂', h2]
    simp only [Option.isSome_some, Bool.true_and, sameResult_some]; rfl
  · intro hb
    have h : Holds c r0.vars.length τ (.or (.mem exp (.var 2) (.app symA [])) (.mem exp (.var 2) (.app symB [])))
        (((τ.lookup 2).isSome && sameResult (τ.lookup 2) (some a)) ||
          ((τ.lookup 2).isSome && sameResult (τ.lookup 2) (some b))) :=
      .or (.mem .var (.ctor syms_ok.2.2.2.1 .nil)) (.mem .var (.ctor syms_ok.2.2.2.2.1 .nil))
    rw [h2] at h
    simp only [Option.isSome_some, Bool.true_and, sameResult_some] at h
    rw [hb]; exact h

/-- The right side under σ that gives V0, V1 and Z the values `.`, the counter and v. -/
theorem rhs_eval {τ : Subst} {v : GroundTerm} (h0 : τ.lookup 0 = some dotkT) (h1 : τ.lookup 1 = some ctr)
    (h2 : τ.lookup 2 = some v) (hv : v.isInj = false) : EvalTerm c τ r0.rhs (some (cfg v)) := by
  rw [r0_rhs]
  have he : EvalTerm c τ (.inj exp Srt.kitem (.var 2)) ((τ.lookup 2).map (injNormal exp Srt.kitem)) := .inj .var
  rw [h2, Option.map_some, injNormal_of_not_inj hv] at he
  have e0 : EvalTerm c τ (.var 0) (some dotkT) := h0 ▸ .var
  have e1 : EvalTerm c τ (.var 1) (some ctr) := h1 ▸ .var
  exact .ctor syms_ok.1 (.cons (.ctor syms_ok.2.1 (.cons (.ctor syms_ok.2.2.1
    (.cons he (.cons e0 .nil))) .nil)) (.cons e1 .nil))

theorem prio_none {r' : Rule} (hr' : r' ∈ c.rules) (hlt : r'.prio < r0.prio) : False := by
  rw [rule_eq hr'] at hlt
  exact Nat.lt_irrefl _ hlt

/-- A step by the rule at any σ that gives V0, V1 the values of `<k> go </k>` and Z a or b. -/
theorem stepBy_at {τ : Subst} {v : GroundTerm} (h0 : τ.lookup 0 = some dotkT) (h1 : τ.lookup 1 = some ctr)
    (h2 : τ.lookup 2 = some v) (hv : v = a ∨ v = b) (y : Config c) (hy : y.val = cfg v) :
    StepBy c r0 τ Go y where
  mem := r0_mem
  hσ := fun j s hs => by
    rw [r0_vars] at hs
    match j, hs with
    | 0, hs => cases hs; exact ⟨_, h0, by decide +kernel⟩
    | 1, hs => cases hs; exact ⟨_, h1, by decide +kernel⟩
    | 2, hs => cases hs; exact ⟨_, h2, by rcases hv with rfl | rfl <;> decide +kernel⟩
  hmatch := by
    rw [r0_lhs]
    have hi : injNormal exp Srt.kitem (.ctor symGo []) = .inj exp Srt.kitem (.ctor symGo []) := rfl
    exact .ctor syms_ok.1 (.cons (.ctor syms_ok.2.1 (.cons (.ctor syms_ok.2.2.1
      (.cons (hi ▸ .inj (.ctor syms_ok.2.2.2.2.2.1 .nil)) (.cons (.var h0) .nil))) .nil))
      (.cons (.var h1) .nil))
  hreq := fun t ht => by rw [r0_shape.1] at ht; cases ht
  hpre := by rw [r0_shape.2.2.2.1]; exact .top
  heval := by
    rw [hy]
    exact rhs_eval h0 h1 h2 (by rcases hv with rfl | rfl <;> rfl)
  hens := fun t ht => by rw [r0_shape.2.1] at ht; cases ht
  hpost := (post_at h2).mpr (by rcases hv with rfl | rfl <;> decide +kernel)
  hprio := fun r' hr' hlt => (prio_none hr' hlt).elim

def σ (v : GroundTerm) : Subst := [(0, dotkT), (1, ctr), (2, v)]

/-- **`go` steps to `a` and to `b`.** -/
theorem stepBy_a : StepBy c r0 (σ a) Go A := stepBy_at rfl rfl rfl (.inl rfl) A rfl
theorem stepBy_b : StepBy c r0 (σ b) Go B := stepBy_at rfl rfl rfl (.inr rfl) B rfl
theorem step_a : Step c Go A := step_iff_by.mpr ⟨r0, σ a, stepBy_a⟩
theorem step_b : Step c Go B := step_iff_by.mpr ⟨r0, σ b, stepBy_b⟩

/-- A match at `<k> go </k>` gives V0 and V1 the values `.` and the counter. -/
theorem lookups {τ : Subst} (hm : PatVal c τ r0.lhs Go.val) :
    τ.lookup 0 = some dotkT ∧ τ.lookup 1 = some ctr := by
  rw [r0_lhs] at hm
  have ⟨h1, hc⟩ := patVal_ctor2 hooks_ok.1 syms_ok.1 hm
  have h2 := patVal_ctor1 hooks_ok.2.1 syms_ok.2.1 h1
  have h3 := (patVal_ctor2 hooks_ok.2.2.1 syms_ok.2.2.1 h2).2
  exact ⟨PatVal.var_inv h3, PatVal.var_inv hc⟩

/-- **Every step by the rule from `go` is to `a` or to `b`**, and Z has that value. -/
theorem step_inv {τ : Subst} {x y : Config c} (hs : StepBy c r0 τ x y) (hx : x = Go) :
    ∃ v, τ.lookup 2 = some v ∧ (v = a ∨ v = b) ∧ (y = A ∨ y = B) := by
  subst hx
  obtain ⟨h0, h1⟩ := lookups hs.hmatch
  obtain ⟨v, h2, -⟩ := hs.hσ 2 exp (by rw [r0_vars]; rfl)
  have hp := (post_at h2).mp hs.hpost
  have hv : v = a ∨ v = b := by
    by_cases ha : v = a
    · exact .inl ha
    · by_cases hb : v = b
      · exact .inr hb
      · simp [ha, hb] at hp
  refine ⟨v, h2, hv, ?_⟩
  have he := EvalTerm.functional_of_fnDet fnDet hs.heval (rhs_eval h0 h1 h2 (by rcases hv with rfl | rfl <;> rfl))
  rcases hv with rfl | rfl
  · exact .inl (Subtype.ext (Option.some.inj he))
  · exact .inr (Subtype.ext (Option.some.inj he))

/-! ### `famEx` is `<k> a </k> ∨ <k> b </k>` at values -/

/-- The family of the application at `go` is the same pattern under `σ a` and `σ b`: they differ
at Z only, an existential variable. -/
theorem famEx_ab : famEx c r0 (σ b) = famEx c r0 (σ a) :=
  famEx_congr_off c r0 fun i hi => by
    rw [r0_shape.2.2.1] at hi
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, hi => exact absurd (List.mem_singleton_self 2) hi
    | _ + 3, _ => rfl

/-- **The values of `famEx` at `go` are `<k> a </k>` and `<k> b </k>`**: in every model of `Γc` the
element of each is in the family (`sound_at`), and a value whose element is in it in every model
is a step by the rule (`famEx_values`), so one of the two. -/
theorem famEx_values_iff (y : Config c) :
    (Γc c ⊧ (den c y.val ⇒ famEx c r0 (σ a))) ↔ (y = A ∨ y = B) := by
  constructor
  · intro hy
    obtain ⟨τ, -, hs⟩ := famEx_values c coreOK fnHyp Go y r0 (σ a) ⟨A, stepBy_a⟩ hy
    obtain ⟨_, _, _, h⟩ := step_inv hs rfl
    exact h
  · have hw : ∀ r' ∈ c.rules, r'.prio < r0.prio → r'.needsWitness c = true →
        (∃ σ', PatVal c σ' r'.lhs Go.val) → r'.CondDecided c := fun r' hr' hlt => (prio_none hr' hlt).elim
    have hc : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c :=
      fun fn hfn => by rw [fns_nil] at hfn; cases hfn
    rintro (rfl | rfl)
    · exact (sound_at c coreOK Go A r0 (σ a) stepBy_a hw hc).2
    · exact famEx_ab ▸ (sound_at c coreOK Go B r0 (σ b) stepBy_b hw hc).2

/-! ### Neither instance is entailed -/

/-- The steps of `Step`, less the one from `go` to `excl`. -/
def T (excl : Config c) (x y : Config c) : Prop := Step c x y ∧ (x = Go → y ≠ excl)

/-- `has_model_choice` at `T excl`, where `keep` is the other instance: a model of `Γc` with the
step's closure whose transition at values is `T excl`. -/
theorem model_without {excl keep : Config c} {vk : GroundTerm} (hk : keep.val = cfg vk) (hvk : vk = a ∨ vk = b)
    (hne : keep ≠ excl) :
    ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), (I ⊧ᴵP (Γc c ∪ Γstep c)) ∧
      ∀ x y : Config c, T excl x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val))) :=
  has_model_choice c coreOK fnHyp (T excl) (fun _ _ h => h.1)
    (fun x y r τ hs hex => by rw [rule_eq hs.mem, r0_shape.2.2.1] at hex; cases hex)
    (fun x y r τ hs => by
      have hr := rule_eq hs.mem
      subst hr
      by_cases hx : x = Go
      · subst hx
        obtain ⟨h0, h1⟩ := lookups hs.hmatch
        have h0' : List.lookup 0 ((2, vk) :: τ) = some dotkT := by simp [List.lookup, h0]
        have h1' : List.lookup 1 ((2, vk) :: τ) = some ctr := by simp [List.lookup, h1]
        have h2' : List.lookup 2 ((2, vk) :: τ) = some vk := by simp [List.lookup]
        refine ⟨keep, (2, vk) :: τ, fun i hi => ?_, stepBy_at h0' h1' h2' hvk keep hk,
          step_iff_by.mpr ⟨r0, _, stepBy_at h0' h1' h2' hvk keep hk⟩, fun _ => hne⟩
        rw [r0_shape.2.2.1] at hi
        have hne2 : (i == 2) = false := beq_false_of_ne (by simpa using hi)
        show List.lookup i ((2, vk) :: τ) = List.lookup i τ
        rw [List.lookup_cons, hne2]
      · exact ⟨y, τ, fun _ _ => rfl, hs, step_iff_by.mpr ⟨_, _, hs⟩, fun h => absurd h hx⟩)

/-- **`den go ⇒ •den b` is not entailed**: in the model at `T B` the configuration `go` steps to
`a` only. -/
theorem not_entailed_b : ¬ ((Γc c ∪ Γstep c) ⊧ (den c Go.val ⇒ KoreAML.sNext (den c B.val))) := by
  obtain ⟨M, i, I, hI, hT⟩ := model_without (excl := B) (keep := A) (vk := a) rfl (.inl rfl) A_ne_B
  exact not_entailed_of_model hI (Classical.not_not.mp fun hn => ((hT Go B).mpr hn).2 rfl rfl)

/-- **`den go ⇒ •den a` is not entailed**, symmetrically. -/
theorem not_entailed_a : ¬ ((Γc c ∪ Γstep c) ⊧ (den c Go.val ⇒ KoreAML.sNext (den c A.val))) := by
  obtain ⟨M, i, I, hI, hT⟩ := model_without (excl := A) (keep := B) (vk := b) rfl (.inr rfl) A_ne_B.symm
  exact not_entailed_of_model hI (Classical.not_not.mp fun hn => ((hT Go A).mpr hn).2 rfl rfl)

/-- Neither is entailed by `Γc` alone, a part of the theory above. -/
theorem not_entailed_Γc : ¬ (Γc c ⊧ (den c Go.val ⇒ KoreAML.sNext (den c A.val))) ∧
    ¬ (Γc c ⊧ (den c Go.val ⇒ KoreAML.sNext (den c B.val))) :=
  ⟨fun h => not_entailed_a fun hI => h fun φ hφ => hI φ (Or.inl hφ),
   fun h => not_entailed_b fun hI => h fun φ hφ => hI φ (Or.inl hφ)⟩

/-- info: 'PredFixtures.RhsOr.famEx_values_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms famEx_values_iff
/-- info: 'PredFixtures.RhsOr.not_entailed_Γc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms not_entailed_Γc

end RhsOr

/-! ## The conjunction of terms on a right side (e3-ml-rule-rhs-and-*) -/

namespace RhsAnd

def exp : Srt := 32
def kCell : Sym := 383
def symA : Sym := 385
def symB : Sym := 386
def symC : Sym := 387
def symD : Sym := 388

def aT : GroundTerm := .ctor symA []
def bT : GroundTerm := .ctor symB []
def dotkT : GroundTerm := .ctor dotk []
def ctr : GroundTerm := .ctor counterLabel [int 0]
def cfg (st : GroundTerm) : GroundTerm := cfgOf kCell exp st

/-- The variable form at the constructor `sC`: `<k> sC(X) => X </k>` with `post := mem X a`, X the
variable 0, V1 and V2 the k cell's rest and the counter. -/
structure VarForm (c : Semantics) (r : Rule) (sC : Sym) : Prop where
  vars : r.vars = [exp, Srt.k, 19]
  lhs : r.lhs = cfgPat kCell exp (.app sC [.var 0]) 1 2
  rhs : r.rhs = cfgPat kCell exp (.var 0) 1 2
  req : r.req = none
  ens : r.ens = none
  pre : r.pre = .top
  post : r.post = .mem exp (.var 0) (.app symA [])
  ctors : c.isCtor topLabel = true ∧ c.isCtor kCell = true ∧ c.isCtor kseq = true ∧ c.isCtor symA = true ∧
    c.isCtor sC = true
  hooks : patternHooks.contains topLabel = false ∧ patternHooks.contains kCell = false ∧
    patternHooks.contains kseq = false ∧ patternHooks.contains sC = false

def σA : Subst := [(0, aT), (1, dotkT), (2, ctr)]

namespace VarForm
variable {c : Semantics} {r : Rule} {sC : Sym}

/-- **`sC(a)` steps to `a`** by the rule: X := a, and `post` is `a ∈ a`. -/
theorem stepBy (h : VarForm c r sC) (hmem : r ∈ c.rules) (hprio : ∀ r' ∈ c.rules, ¬ r'.prio < r.prio)
    (haS : c.sortOf aT = some exp) (hdS : c.sortOf dotkT = some Srt.k) (hcS : c.sortOf ctr = some 19)
    (x y : Config c) (hx : x.val = cfg (.ctor sC [aT])) (hy : y.val = cfg aT) : StepBy c r σA x y where
  mem := hmem
  hσ := fun j s hs => by
    rw [h.vars] at hs
    match j, hs with
    | 0, hs => cases hs; exact ⟨_, rfl, haS⟩
    | 1, hs => cases hs; exact ⟨_, rfl, hdS⟩
    | 2, hs => cases hs; exact ⟨_, rfl, hcS⟩
  hmatch := by
    rw [h.lhs, hx]
    have hi : injNormal exp Srt.kitem (.ctor sC [aT]) = .inj exp Srt.kitem (.ctor sC [aT]) := rfl
    exact .ctor h.ctors.1 (.cons (.ctor h.ctors.2.1 (.cons (.ctor h.ctors.2.2.1
      (.cons (hi ▸ .inj (.ctor h.ctors.2.2.2.2 (.cons (.var rfl) .nil))) (.cons (.var rfl) .nil))) .nil))
      (.cons (.var rfl) .nil))
  hreq := fun t ht => by rw [h.req] at ht; cases ht
  hpre := by rw [h.pre]; exact .top
  heval := by
    rw [h.rhs, hy]
    have he : EvalTerm c σA (.inj exp Srt.kitem (.var 0)) (some (.inj exp Srt.kitem aT)) := .inj .var
    exact .ctor h.ctors.1 (.cons (.ctor h.ctors.2.1 (.cons (.ctor h.ctors.2.2.1
      (.cons he (.cons .var .nil))) .nil)) (.cons .var .nil))
  hens := fun t ht => by rw [h.ens] at ht; cases ht
  hpost := by
    rw [h.post]
    have hm : Holds c r.vars.length σA (.mem exp (.var 0) (.app symA []))
        ((σA.lookup 0).isSome && sameResult (σA.lookup 0) (some aT)) := .mem .var (.ctor h.ctors.2.2.2.1 .nil)
    have hb : ((σA.lookup 0).isSome && sameResult (σA.lookup 0) (some aT)) = true := by
      show (true && sameResult (some aT) (some aT)) = true
      rw [sameResult_some]; simp
    rwa [hb] at hm
  hprio := fun r' hr' hlt => absurd hlt (hprio r' hr')

/-- **A step by the rule from `T(z)` is from `sC(a)` to `a`**: the match gives X the value z,
`post` holds only at z = a, and the right side is then `a`. -/
theorem inv (h : VarForm c r sC) {τ : Subst} {x y : Config c} (hs : StepBy c r τ x y) {T : Sym}
    {z : GroundTerm} (hx : x.val = cfg (.ctor T [z])) : T = sC ∧ z = aT ∧ y.val = cfg aT := by
  have hm := hs.hmatch
  rw [h.lhs, hx] at hm
  obtain ⟨⟨w, hw, hwe⟩, hk, hc⟩ := patVal_cfgPat ⟨h.ctors.1, h.ctors.2.1, h.ctors.2.2.1⟩
    ⟨h.hooks.1, h.hooks.2.1, h.hooks.2.2.1⟩ hm
  obtain ⟨-, vs, rfl, hvs⟩ := PatVal.app_inv h.hooks.2.2.2 hw h.ctors.2.2.2.2
  have hwe' : GroundTerm.inj exp Srt.kitem (.ctor sC vs) = .inj exp Srt.kitem (.ctor T [z]) := hwe
  cases hwe'
  obtain ⟨_, _, he1, h0, _⟩ := PatVals.cons_inv hvs
  cases he1
  have hl0 := PatVal.var_inv h0
  have hp := hs.hpost
  rw [h.post] at hp
  obtain ⟨r₁, r₁', e₁, e₁', hb⟩ := holds_mem_inv hp
  rw [EvalTerm.var_inv e₁, evalTerm_const h.ctors.2.2.2.1 e₁', hl0] at hb
  simp only [Option.isSome_some, Bool.true_and, sameResult_some] at hb
  have hz : z = aT := (by simpa using hb.symm : z = .ctor symA [])
  subst hz
  have he := hs.heval
  rw [h.rhs] at he
  obtain ⟨w', hw', hy⟩ := evalTerm_cfgPat ⟨h.ctors.1, h.ctors.2.1, h.ctors.2.2.1⟩ hk hc he
  have hw'' : some w' = some aT := (EvalTerm.var_inv hw').trans hl0
  cases hw''
  exact ⟨rfl, rfl, hy⟩

end VarForm

/-! ### e3-ml-rule-rhs-and-ctor, e3-ml-rule-rhs-and-var: `c(X) => X #And a()`, `c(X) => a() #And X` -/

namespace MlAndC

definition_of defL from "f2-examples/mlandc.kompile.kore"
definition_read defA from "f2-examples/mlandc.kompile.kore" by and

/-- The reader reads the text's rules through the cut (`Parse.ruleBody`, `andTermsCut`): the
landed definition's rules are those `Parse.andRuleOf` reads. -/
theorem parsed : defL.sem.rules = defA.sem.rules := rfl

/-- The definition the landed reader builds, with its rules replaced by those `Parse.andRuleOf`
reads from the text. -/
noncomputable abbrev c : Semantics := { defL.sem with rules := defA.sem.rules }

theorem names_ok : c.sortName exp = "Exp" ∧ c.symName symA = "Lbla" ∧ c.symName symB = "Lblb" ∧
    c.symName symC = "Lblc" := by
  decide +kernel

theorem coreOK : c.coreOK = true := by decide +kernel
theorem prios : c.rules.length = 1 ∧ ∀ r ∈ c.rules, r.prio = 50 := by decide +kernel

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)
theorem r0_mem : r0 ∈ c.rules := List.getElem_mem _
theorem rule_eq {r : Rule} (hr : r ∈ c.rules) : r = r0 := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have : i = 0 := by have := prios.1; omega
  subst this
  rfl

/-- The rule read is the variable form at c, with no `ensures`. -/
theorem form : VarForm c r0 symC :=
  ⟨by decide +kernel, rfl, rfl, rfl, rfl, rfl, rfl, by decide +kernel, by decide +kernel⟩

def CA : Config c := ⟨cfg (.ctor symC [aT]), by decide +kernel⟩
def CB : Config c := ⟨cfg (.ctor symC [bT]), by decide +kernel⟩
def A : Config c := ⟨cfg aT, by decide +kernel⟩

/-- **`c(a)` steps to `a`.** -/
theorem step_ca : Step c CA A :=
  step_iff_by.mpr ⟨r0, σA, form.stepBy r0_mem
    (fun r' hr' hlt => by rw [prios.2 r' hr', prios.2 r0 r0_mem] at hlt; exact Nat.lt_irrefl _ hlt)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) CA A rfl rfl⟩

/-- **`c(b)` has no successor.** -/
theorem stuck_cb : ∀ y, ¬ Step c CB y := fun y h => by
  obtain ⟨r, τ, hs⟩ := step_iff_by.mp h
  rw [rule_eq hs.mem] at hs
  obtain ⟨-, hz, -⟩ := form.inv hs (T := symC) (z := bT) rfl
  exact absurd hz (by decide +kernel)

end MlAndC

namespace MlAndV

definition_of defL from "f2-examples/mlandv.kompile.kore"
definition_read defA from "f2-examples/mlandv.kompile.kore" by and

/-- The reader reads the text's rules through the cut (`Parse.ruleBody`, `andTermsCut`): the
landed definition's rules are those `Parse.andRuleOf` reads. -/
theorem parsed : defL.sem.rules = defA.sem.rules := rfl

noncomputable abbrev c : Semantics := { defL.sem with rules := defA.sem.rules }

theorem names_ok : c.sortName exp = "Exp" ∧ c.symName symA = "Lbla" ∧ c.symName symB = "Lblb" ∧
    c.symName symC = "Lblc" := by
  decide +kernel

theorem coreOK : c.coreOK = true := by decide +kernel
theorem prios : c.rules.length = 1 ∧ ∀ r ∈ c.rules, r.prio = 50 := by decide +kernel

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)
theorem r0_mem : r0 ∈ c.rules := List.getElem_mem _
theorem rule_eq {r : Rule} (hr : r ∈ c.rules) : r = r0 := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have : i = 0 := by have := prios.1; omega
  subst this
  rfl

theorem form : VarForm c r0 symC :=
  ⟨by decide +kernel, rfl, rfl, rfl, rfl, rfl, rfl, by decide +kernel, by decide +kernel⟩

def CA : Config c := ⟨cfg (.ctor symC [aT]), by decide +kernel⟩
def CB : Config c := ⟨cfg (.ctor symC [bT]), by decide +kernel⟩
def A : Config c := ⟨cfg aT, by decide +kernel⟩

theorem step_ca : Step c CA A :=
  step_iff_by.mpr ⟨r0, σA, form.stepBy r0_mem
    (fun r' hr' hlt => by rw [prios.2 r' hr', prios.2 r0 r0_mem] at hlt; exact Nat.lt_irrefl _ hlt)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) CA A rfl rfl⟩

theorem stuck_cb : ∀ y, ¬ Step c CB y := fun y h => by
  obtain ⟨r, τ, hs⟩ := step_iff_by.mp h
  rw [rule_eq hs.mem] at hs
  obtain ⟨-, hz, -⟩ := form.inv hs (T := symC) (z := bT) rfl
  exact absurd hz (by decide +kernel)

end MlAndV

/-! ### e3-ml-rule-lhs-or-rhs-and: `c(X) #Or d(X) => X #And a()`, two rules -/

namespace MlOrAnd

definition_of defL from "f2-examples/mlorand.kompile.kore"
definition_read defA from "f2-examples/mlorand.kompile.kore" by and

/-- The reader reads the text's rules through the cut (`Parse.ruleBody`, `andTermsCut`): the
landed definition's rules are those `Parse.andRuleOf` reads. -/
theorem parsed : defL.sem.rules = defA.sem.rules := rfl

noncomputable abbrev c : Semantics := { defL.sem with rules := defA.sem.rules }

theorem names_ok : c.sortName exp = "Exp" ∧ c.symName symA = "Lbla" ∧ c.symName symB = "Lblb" ∧
    c.symName symC = "Lblc" ∧ c.symName symD = "Lbld" := by
  decide +kernel

theorem coreOK : c.coreOK = true := by decide +kernel
theorem prios : c.rules.length = 2 ∧ ∀ r ∈ c.rules, r.prio = 50 := by decide +kernel

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)
noncomputable def r1 : Rule := c.rules[1]'(by decide +kernel)
theorem r0_mem : r0 ∈ c.rules := List.getElem_mem _
theorem r1_mem : r1 ∈ c.rules := List.getElem_mem _
theorem rule_eq {r : Rule} (hr : r ∈ c.rules) : r = r0 ∨ r = r1 := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have h2 := prios.1
  match i, hi with
  | 0, _ => exact .inl rfl
  | 1, _ => exact .inr rfl
  | n + 2, hi => omega

/-- One rule per disjunct of the left side, each the variable form. -/
theorem form0 : VarForm c r0 symC :=
  ⟨by decide +kernel, rfl, rfl, rfl, rfl, rfl, rfl, by decide +kernel, by decide +kernel⟩
theorem form1 : VarForm c r1 symD :=
  ⟨by decide +kernel, rfl, rfl, rfl, rfl, rfl, rfl, by decide +kernel, by decide +kernel⟩

theorem prio_none (r : Rule) (hr : r ∈ c.rules) : ∀ r' ∈ c.rules, ¬ r'.prio < r.prio :=
  fun r' hr' hlt => by rw [prios.2 r' hr', prios.2 r hr] at hlt; exact Nat.lt_irrefl _ hlt

def CA : Config c := ⟨cfg (.ctor symC [aT]), by decide +kernel⟩
def DA : Config c := ⟨cfg (.ctor symD [aT]), by decide +kernel⟩
def CB : Config c := ⟨cfg (.ctor symC [bT]), by decide +kernel⟩
def A : Config c := ⟨cfg aT, by decide +kernel⟩

/-- **`c(a)` and `d(a)` step to `a`.** -/
theorem step_ca : Step c CA A :=
  step_iff_by.mpr ⟨r0, σA, form0.stepBy r0_mem (prio_none r0 r0_mem)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) CA A rfl rfl⟩
theorem step_da : Step c DA A :=
  step_iff_by.mpr ⟨r1, σA, form1.stepBy r1_mem (prio_none r1 r1_mem)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) DA A rfl rfl⟩

/-- **`c(b)` has no successor**: neither rule gives one (the d rule does not match). -/
theorem stuck_cb : ∀ y, ¬ Step c CB y := fun y h => by
  obtain ⟨r, τ, hs⟩ := step_iff_by.mp h
  rcases rule_eq hs.mem with rfl | rfl
  · obtain ⟨-, hz, -⟩ := form0.inv hs (T := symC) (z := bT) rfl
    exact absurd hz (by decide +kernel)
  · obtain ⟨hT, -, -⟩ := form1.inv hs (T := symC) (z := bT) rfl
    exact absurd hT (by decide +kernel)

end MlOrAnd

/-! ### e3-ml-rule-rhs-and-term: `go(X) => f(X) #And g(X)`, f the identity, g negation -/

namespace MlAndT

definition_of defL from "f2-examples/mlandt.kompile.kore"
definition_read defA from "f2-examples/mlandt.kompile.kore" by and

/-- The reader reads the text's rules through the cut (`Parse.ruleBody`, `andTermsCut`): the
landed definition's rules are those `Parse.andRuleOf` reads. -/
theorem parsed : defL.sem.rules = defA.sem.rules := rfl

noncomputable abbrev c : Semantics := { defL.sem with rules := defA.sem.rules }

def symGo : Sym := 386
def symF : Sym := 388
def symG : Sym := 389

theorem names_ok : c.sortName exp = "Exp" ∧ c.symName symGo = "Lblgo" ∧ c.symName symF = "Lblf" ∧
    c.symName symG = "Lblg" := by
  decide +kernel

theorem coreOK : c.coreOK = true := by decide +kernel
theorem prios : c.rules.length = 1 ∧ ∀ r ∈ c.rules, r.prio = 50 := by decide +kernel

noncomputable def r0 : Rule := c.rules[0]'(by decide +kernel)
theorem r0_mem : r0 ∈ c.rules := List.getElem_mem _
theorem rule_eq {r : Rule} (hr : r ∈ c.rules) : r = r0 := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have : i = 0 := by have := prios.1; omega
  subst this
  rfl

def fX : Term := .app symF [.var 0]
def gX : Term := .app symG [.var 0]

/-- The fresh form: `go(X) => ?Z` with `post := and (mem Z f(X)) (mem Z g(X))`, Z the variable 3. -/
theorem r0_vars : r0.vars = [Srt.int, Srt.k, 19, Srt.int] := by decide +kernel
theorem r0_lhs : r0.lhs = cfgPat kCell exp (.app symGo [.var 0]) 1 2 := rfl
theorem r0_rhs : r0.rhs = cfgPat kCell Srt.int (.var 3) 1 2 := rfl
theorem r0_shape : r0.req = none ∧ r0.ens = none ∧ r0.pre = .top ∧ r0.exs = [3] ∧
    r0.post = .and (.mem Srt.int (.var 3) fX) (.mem Srt.int (.var 3) gX) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem syms_ok : c.isCtor topLabel = true ∧ c.isCtor kCell = true ∧ c.isCtor kseq = true ∧
    c.isCtor symGo = true := by
  decide +kernel
theorem hooks_ok : patternHooks.contains topLabel = false ∧ patternHooks.contains kCell = false ∧
    patternHooks.contains kseq = false ∧ patternHooks.contains symGo = false := by
  decide +kernel

/-! #### The evaluation of the conjuncts -/

/-- The definition without its rule: the rule has a predicate and an existential variable, which
`ok` and `okM` refuse; the clauses' context does not read the rules. -/
noncomputable abbrev cNoRules : Semantics := { defL.sem with rules := [] }
theorem okL : cNoRules.ok = true := by decide +kernel
theorem sortedOK : c.sortedOK = true := by decide +kernel
theorem srReady : c.srReady = true := by decide +kernel
theorem matchReady : c.matchReady = true := by decide +kernel

theorem hsc : SortCtx c := sortCtx_of_all sortedOK srReady (Exec.ovlCase_of matchReady)
/-- The clauses are the landed definition's: `ok` of the definition without its rule gives their
context. -/
theorem hcc : Exec.ClauseCtx c :=
  have h : Exec.ClauseCtx cNoRules := Exec.clauseCtx_of okL
  h
theorem hmc : Exec.MatchCtx c := Exec.matchCtx_of matchReady

/-- Evaluation has one result: the deciders confirm coherence. -/
theorem coherent : CoherentAll c := by
  have hag : c.agreeObligations = [] := by decide +kernel
  have hcf : c.clausesFixed = true := by decide +kernel
  refine coherentAll_of_parts (matchIndependentAll_of_sortedOK sortedOK (Semantics.fnsNoExs_of_all (by decide +kernel)) matchReady
    (.of_fixed hcf (Exec.matchCtx_of matchReady).noOvl)) fun f fn hfn => ?_
  obtain ⟨hmem, -⟩ := lookupFn_spec hfn
  rcases List.mem_append.mp hmem with h | h
  · exact clausesAgree_of_sortedOK sortedOK (Semantics.fnsNoExs_of_all (by decide +kernel)) srReady matchReady (fun f hf => by rw [hag] at hf; nomatch hf) fn h
  · exact sortPreds_agree h

theorem fnDet : FnDet c := fnDet_of_coherent coherent

theorem headsOK : HeadsOK c (c.fns.map Fn.sig) := fun k hk => by
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hk
  exact ⟨g, List.mem_append_left _ hg, rfl⟩

def σn (n : Int) : Subst := [(0, int n)]

theorem wsn (n : Int) : c.WellSorted [Srt.int] (σn n) := fun j s hs => by
  match j, hs with
  | 0, hs => cases hs; exact ⟨_, rfl, sortOf_int n⟩

/-- A term over X evaluated at `X := n` gives its result at any σ that gives X the value n. -/
theorem at_τ {t : Term} (ht : varOccs t = [0]) {n : Int} {r : Option GroundTerm} (h : EvalTerm c (σn n) t r)
    {τ : Subst} (h0 : τ.lookup 0 = some (int n)) : EvalTerm c τ t r :=
  Exec.EvalTerm.congr h fun i hi => by
    rw [ht, List.mem_singleton] at hi
    subst hi
    exact h0.symm

theorem f0 : EvalTerm c (σn 0) fX (some (int 0)) :=
  Exec.evalT_sound hsc hcc hmc 20 (by decide +kernel) headsOK (wsn 0) (s := Srt.int) (by decide +kernel)
theorem g0 : EvalTerm c (σn 0) gX (some (int 0)) :=
  Exec.evalT_sound hsc hcc hmc 20 (by decide +kernel) headsOK (wsn 0) (s := Srt.int) (by decide +kernel)
theorem f1 : EvalTerm c (σn 1) fX (some (int 1)) :=
  Exec.evalT_sound hsc hcc hmc 20 (by decide +kernel) headsOK (wsn 1) (s := Srt.int) (by decide +kernel)
theorem g1 : EvalTerm c (σn 1) gX (some (int (-1))) :=
  Exec.evalT_sound hsc hcc hmc 20 (by decide +kernel) headsOK (wsn 1) (s := Srt.int) (by decide +kernel)

/-! #### The steps -/

/-- `<k> go(n) </k>`; `<k> n </k>`. -/
def goCfg (n : Int) : GroundTerm := cfgOf kCell exp (.ctor symGo [int n])
def resCfg (n : Int) : GroundTerm := cfgOf kCell Srt.int (int n)

def Go0 : Config c := ⟨goCfg 0, by decide +kernel⟩
def Go1 : Config c := ⟨goCfg 1, by decide +kernel⟩
def Zero : Config c := ⟨resCfg 0, by decide +kernel⟩

def σ0 : Subst := [(0, int 0), (1, dotkT), (2, ctr), (3, int 0)]

/-- **`go(0)` steps to `0`**: X := 0, Z := 0, the value both conjuncts have there. -/
theorem stepBy0 : StepBy c r0 σ0 Go0 Zero where
  mem := r0_mem
  hσ := fun j s hs => by
    rw [r0_vars] at hs
    match j, hs with
    | 0, hs => cases hs; exact ⟨_, rfl, sortOf_int 0⟩
    | 1, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
    | 2, hs => cases hs; exact ⟨_, rfl, by decide +kernel⟩
    | 3, hs => cases hs; exact ⟨_, rfl, sortOf_int 0⟩
  hmatch := by
    rw [r0_lhs]
    have hi : injNormal exp Srt.kitem (.ctor symGo [int 0]) = .inj exp Srt.kitem (.ctor symGo [int 0]) := rfl
    exact .ctor syms_ok.1 (.cons (.ctor syms_ok.2.1 (.cons (.ctor syms_ok.2.2.1
      (.cons (hi ▸ .inj (.ctor syms_ok.2.2.2 (.cons (.var rfl) .nil))) (.cons (.var rfl) .nil))) .nil))
      (.cons (.var rfl) .nil))
  hreq := fun t ht => by rw [r0_shape.1] at ht; cases ht
  hpre := by rw [r0_shape.2.2.1]; exact .top
  heval := by
    rw [r0_rhs]
    have he : EvalTerm c σ0 (.inj Srt.int Srt.kitem (.var 3)) (some (.inj Srt.int Srt.kitem (int 0))) := .inj .var
    exact .ctor syms_ok.1 (.cons (.ctor syms_ok.2.1 (.cons (.ctor syms_ok.2.2.1
      (.cons he (.cons .var .nil))) .nil)) (.cons .var .nil))
  hens := fun t ht => by rw [r0_shape.2.1] at ht; cases ht
  hpost := by
    rw [r0_shape.2.2.2.2]
    have h : Holds c r0.vars.length σ0 (.and (.mem Srt.int (.var 3) fX) (.mem Srt.int (.var 3) gX))
        (((σ0.lookup 3).isSome && sameResult (σ0.lookup 3) (some (int 0))) &&
          ((σ0.lookup 3).isSome && sameResult (σ0.lookup 3) (some (int 0)))) :=
      .and (.mem .var (at_τ rfl f0 rfl)) (.mem .var (at_τ rfl g0 rfl))
    have hb : (((σ0.lookup 3).isSome && sameResult (σ0.lookup 3) (some (int 0))) &&
        ((σ0.lookup 3).isSome && sameResult (σ0.lookup 3) (some (int 0)))) = true := by
      show ((true && sameResult (some (int 0)) (some (int 0))) && (true && sameResult (some (int 0)) (some (int 0)))) = true
      rw [sameResult_some]; simp
    rwa [hb] at h
  hprio := fun r' hr' hlt => by
    rw [prios.2 r' hr', prios.2 r0 r0_mem] at hlt; exact absurd hlt (Nat.lt_irrefl _)

theorem step_go0 : Step c Go0 Zero := step_iff_by.mpr ⟨r0, σ0, stepBy0⟩

/-- **A step by the rule from `go(n)`**, where f(n) is n and g(n) is m: n = m, and the successor
is `n`. -/
theorem go_inv {n m : Int} (hf : EvalTerm c (σn n) fX (some (int n))) (hg : EvalTerm c (σn n) gX (some (int m)))
    {τ : Subst} {x y : Config c} (hx : x.val = goCfg n) (hs : StepBy c r0 τ x y) :
    n = m ∧ y.val = resCfg n := by
  have hm := hs.hmatch
  rw [r0_lhs, hx] at hm
  obtain ⟨⟨w, hw, hwe⟩, hk, hc⟩ := patVal_cfgPat ⟨syms_ok.1, syms_ok.2.1, syms_ok.2.2.1⟩
    ⟨hooks_ok.1, hooks_ok.2.1, hooks_ok.2.2.1⟩ hm
  obtain ⟨-, vs, rfl, hvs⟩ := PatVal.app_inv hooks_ok.2.2.2 hw syms_ok.2.2.2
  have hwe' : GroundTerm.inj exp Srt.kitem (.ctor symGo vs) = .inj exp Srt.kitem (.ctor symGo [int n]) := hwe
  cases hwe'
  obtain ⟨_, _, he1, h0, _⟩ := PatVals.cons_inv hvs
  cases he1
  have hl0 := PatVal.var_inv h0
  obtain ⟨v, hl3, -⟩ := hs.hσ 3 Srt.int (by rw [r0_vars]; rfl)
  have hp := hs.hpost
  rw [r0_shape.2.2.2.2] at hp
  obtain ⟨b₁, b₂, h₁, h₂, hb⟩ := holds_and_inv hp
  obtain ⟨r₁, r₁', e₁, e₁', rfl⟩ := holds_mem_inv h₁
  obtain ⟨r₂, r₂', e₂, e₂', rfl⟩ := holds_mem_inv h₂
  rw [EvalTerm.var_inv e₁, EvalTerm.var_inv e₂, hl3, EvalTerm.functional_of_fnDet fnDet e₁' (at_τ rfl hf hl0),
    EvalTerm.functional_of_fnDet fnDet e₂' (at_τ rfl hg hl0)] at hb
  simp only [Option.isSome_some, Bool.true_and, sameResult_some] at hb
  have hv : v = int n ∧ v = int m := by simpa using hb.symm
  obtain ⟨rfl, hvm⟩ := hv
  have he := hs.heval
  rw [r0_rhs] at he
  obtain ⟨w', hw', hy⟩ := evalTerm_cfgPat ⟨syms_ok.1, syms_ok.2.1, syms_ok.2.2.1⟩ hk hc he
  have hw'' : some w' = some (int n) := (EvalTerm.var_inv hw').trans hl3
  cases hw''
  have hnm : n = m := by simpa [int] using hvm
  exact ⟨hnm, hy⟩

/-- **The successor of `go(0)` is `0`, and only it.** -/
theorem step_go0_iff (y : Config c) : Step c Go0 y ↔ y = Zero := by
  constructor
  · intro h
    obtain ⟨r, τ, hs⟩ := step_iff_by.mp h
    rw [rule_eq hs.mem] at hs
    exact Subtype.ext (go_inv f0 g0 rfl hs).2
  · rintro rfl; exact step_go0

/-- **`go(1)` has no successor**: f(1) = 1 and g(1) = -1 have no common value. -/
theorem stuck_go1 : ∀ y, ¬ Step c Go1 y := fun y h => by
  obtain ⟨r, τ, hs⟩ := step_iff_by.mp h
  rw [rule_eq hs.mem] at hs
  exact absurd (go_inv f1 g1 rfl hs).1 (by decide)

/-! #### The one value of `famEx` -/

theorem noWitness : (∀ r ∈ c.rules, r.needsWitness c = false) ∧
    (∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = false) := by
  decide +kernel
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel

def callOrder : List Sym := [symF, symG]

theorem obligations : c.rankObligations callOrder ++ c.decObligationsL = [] ∧
    c.totalObligationsRP callOrder [] = [] ∧ c.agreeObligationsI = [] ∧ c.matchObligationsL = [] := by
  decide +kernel

/-- `FnHyp`: f and g terminate, their equations agree, nothing needs a witness and no parameter is
an open generator. -/
theorem fnHyp : FnHyp c :=
  fnHyp_of_fnObligations coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) ParamsTotal.nil
    (ord := callOrder)
    ⟨fun f hf => by rw [obligations.1] at hf; exact absurd hf List.not_mem_nil,
     fun f hf => by rw [obligations.2.1] at hf; exact absurd hf List.not_mem_nil,
     fun f hf => by rw [obligations.2.2.1] at hf; exact absurd hf List.not_mem_nil,
     fun p hp => by rw [obligations.2.2.2] at hp; exact absurd hp List.not_mem_nil,
     openDecided_of_plain noWitness.1 noWitness.2, openLaws_of_plain noRaw⟩

/-- **The successor of `go(0)` is the one value `famEx` has**: in every model of `Γc` the element of
`0` is in the family of the application at `go(0)` (`sound_at`), and a value whose element is in it
in every model is a step by the rule (`famEx_values`), so `0`. -/
theorem famEx_one (y : Config c) : (Γc c ⊧ (den c y.val ⇒ famEx c r0 σ0)) ↔ y = Zero := by
  constructor
  · intro hy
    obtain ⟨τ, -, hs⟩ := famEx_values c coreOK fnHyp Go0 y r0 σ0 ⟨Zero, stepBy0⟩ hy
    exact Subtype.ext (go_inv f0 g0 rfl hs).2
  · rintro rfl
    exact (sound_at c coreOK Go0 Zero r0 σ0 stepBy0
      (fun r' hr' hlt => by rw [prios.2 r' hr', prios.2 r0 r0_mem] at hlt; exact absurd hlt (Nat.lt_irrefl _))
      (fun fn hfn cl hcl h => absurd h (by rw [noWitness.2 fn hfn cl hcl]; decide))).2

/-- info: 'PredFixtures.RhsAnd.MlAndT.famEx_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms famEx_one

end MlAndT

end RhsAnd

end PredFixtures
