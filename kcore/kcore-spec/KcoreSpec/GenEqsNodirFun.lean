/-
  The `functional` axioms `∃y:S. y = L(x̄)` of symbols Γ lacks that the text gives no equation
  (a macro or alias symbol, whose rule the text does not hold), with the no-direction equations and
  constant initializers' `functional` axioms of `nod_instance`, in one model of the theory.

  - **The sentence (`nodFunctionalAt?`).** `∃y:S. y = L(x₁, …, xₙ)`, `L` a symbol without sort
    arguments applied to element variables; the symbol, the variables and the sort.
  - **What it states at values (`NodFunAt`).** For every list of values of the variables' sorts
    `ws`, `L(ws)` denotes one element of `S`.
  - **The model (`nod_instance_fun`).** The text states nothing of such a symbol but that it is
    `functional`, so a model may give it any total function into `S`. Here it gives `L` its first
    argument, where the first variable is of the sort `S` (`nodSentFunAtB` checks it): the model
    `model_with_inits_arm` gives at the arm's names and the symbols `fs` together, each free of the
    theory (`armNameB`), `G` the arm's on the names (as `model_of_arm` takes it) and the first
    argument on `fs` (`nodFunG`). The arm's lemmas read the model only
    at its names (`InitModel` restricted, `nodFun_restrict`), so the equations and constants'
    `functional` axioms of `nod_instance` hold in it too.
-/
import KcoreSpec.GenEqsNodir

set_option autoImplicit false

namespace KCore

open ML Faithful

namespace GenEqs

open Faithful.Model

/-- The variables of a list of patterns, each an element variable. -/
def nodVarArgs? : List Kore.Pattern → Option (List Kore.EVar)
  | [] => some []
  | .var (.evar x) :: ps => (nodVarArgs? ps).map (x :: ·)
  | _ => none

/-- The symbol, the argument variables and the sort of a `functional` axiom `∃y:S. y = L(x̄)` of a
symbol without sort arguments over element variables. -/
def nodFunctionalAt? (a : Kore.Axiom) : Option (String × List Kore.EVar × Kore.KSort) :=
  match a.pattern with
  | .exist _ v (.equals _ _ (.var (.evar w)) (.app f [] ps)) =>
    if decide (v = w) then (nodVarArgs? ps).map fun xs => (f.ident.name, xs, v.sort) else none
  | _ => none

/-- **The `functional` axiom of `L` over the variables `xs` at the sort `S` holds at every list of
values of their sorts**: `∃y:S. y = L(ws)`. -/
def NodFunAt (c : Semantics) (I : Interpretation KoreAML.Sym Elem) (L : String) (xs : List Kore.EVar)
    (S : Kore.KSort) : Prop :=
  ∀ ws, NodVals c xs ws → ∀ s, armSrt c S = some s → ∀ y : EVar,
    I ⊧ᴵ KoreAML.sExists y (KoreAML.Cons.sortP (c.sortName s)) (.evar y ≡ KoreAML.appList (symP L) (ws.map (den c)))

/-- The arity of a name: `fs`'s for a symbol of `fs`, `ar`'s otherwise. -/
def nodFunAr (fs : List (String × Nat)) (ar : String → Nat) (n : String) : Nat :=
  match fs.find? (·.1 == n) with
  | some p => p.2
  | none => ar n

/-- The names' values: a symbol of `fs` its first argument, another name `G`'s. -/
def nodFunG (fs : List (String × Nat)) (G : String → List GroundTerm → Option GroundTerm) :
    String → List GroundTerm → Option GroundTerm := fun n ws =>
  match fs.find? (·.1 == n) with
  | some _ => ws.head?
  | none => G n ws

/-- The symbols `fs` are none of the names and each is free of the theory (`armNameB`). -/
def nodFunsB (Nm : Parse.Names) (msrc : String) (eqs : List Parse.RawEqn) (c : Semantics) (names : List String)
    (fs : List (String × Nat)) : Bool :=
  fs.all fun p => !names.contains p.1 && armNameB Nm msrc eqs c p.1

/-- The sentence of index `i` is a `functional` axiom `∃y:S. y = L(x₁, …, xₙ)` with `L` of `fs` at
arity `n ≥ 1`, its first variable of the sort `S`, a sort of the semantics. -/
def nodSentFunAtB (c : Semantics) (fs : List (String × Nat)) (sents : List KoreAML.AxiomDecl) (i : Nat) : Bool :=
  match sents.find? (·.index == i) with
  | some ad => match nodFunctionalAt? ad.ax with
    | some (L, x :: xs, S) => decide (fs.find? (·.1 == L) = some (L, xs.length + 1)) && decide (x.sort = S) &&
        (armSrt c S).isSome
    | _ => false
  | none => false

theorem nodFun_find_none {fs : List (String × Nat)} {names : List String} {n : String}
    (hfs : fs.all (fun p => !names.contains p.1) = true) (hn : names.contains n = true) :
    fs.find? (·.1 == n) = none := by
  rw [List.find?_eq_none]
  intro p hp he
  have := List.all_eq_true.mp hfs p hp
  rw [beq_iff_eq.mp he, hn] at this
  cases this

/-- **A model in which the names `N'` denote `G'` is one in which the names `N` denote `G`**, where
`N` is among `N'` and `ar'`, `G'` are `ar`, `G` there. -/
theorem nodFun_restrict {c : Semantics} {N N' : String → Prop} {ar ar' : String → Nat}
    {G G' : String → List GroundTerm → Option GroundTerm} {I : Interpretation KoreAML.Sym Elem}
    (hM : InitModel c N' ar' G' I) (hN : ∀ n, N n → N' n) (har : ∀ n, N n → ar' n = ar n)
    (hG : ∀ n, N n → G' n = G n) : InitModel c N ar G I :=
  ⟨hM.sat, hM.vals, fun n hn ws hl hws ρ m => by
    rw [← hG n hn]; exact hM.names n (hN n hn) ws ((har n hn).trans hl.symm).symm hws ρ m⟩

/-- **One model of the theory, whose steps are the semantics', in which each listed sentence
holds**: `nod_instance`'s equations (`eqIdx`) and constants' `functional` axioms (`funIdx`), and the
`functional` axioms (`funAtIdx`) of the symbols `fs`, at every list of values of their variables'
sorts. -/
theorem nod_instance_fun (c : Semantics) (hc : c.coreOK = true) (hf : FnHyp c) (Nm : Parse.Names) (msrc : String)
    (eqs : List Parse.RawEqn) (cells : List Cell) (names order : List String) (sents : List KoreAML.AxiomDecl)
    (eqIdx funIdx : List Nat) (fs : List (String × Nat)) (funAtIdx : List Nat)
    (hnames : names.all (armNameB Nm msrc eqs c) = true) (hR : armRankB order eqs = true)
    (hord : order.all names.contains = true) (hchk : nodOrderB c names eqs order = true)
    (hfix : nodFixedB c = true)
    (heq : eqIdx.all (nodSentEqB Nm msrc eqs c cells names order sents) = true)
    (hfun : funIdx.all (nodSentFunB c eqs names order sents) = true)
    (hfs : nodFunsB Nm msrc eqs c names fs = true)
    (hat : funAtIdx.all (nodSentFunAtB c fs sents) = true) :
    ∃ I : Interpretation KoreAML.Sym Elem, (I ⊧ᴵP (Γc c ∪ Γstep c)) ∧
      (∀ x y : Config c, Step c x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val)))) ∧
      (∀ i ∈ eqIdx, ∃ ad ∈ sents, ad.index = i ∧ ∃ e, Parse.scanEqn (.axiom ad.ax) = some e ∧ NodEqn c I e) ∧
      (∀ i ∈ funIdx, ∃ ad ∈ sents, ad.index = i ∧ ∃ L S, nodFunctional? ad.ax = some (L, S) ∧ NodFun c I L S) ∧
      (∀ i ∈ funAtIdx, ∃ ad ∈ sents, ad.index = i ∧ ∃ L xs S, nodFunctionalAt? ad.ax = some (L, xs, S) ∧
        NodFunAt c I L xs S) := by
  have hfs1 : fs.all (fun p => !names.contains p.1) = true :=
    List.all_eq_true.mpr fun p hp => by
      have := List.all_eq_true.mp hfs p hp
      simp only [Bool.and_eq_true] at this; exact this.1
  let N' : String → Prop := fun n => names.contains n = true ∨ (fs.find? (·.1 == n)).isSome = true
  have hN' : ∀ n, N' n → (∀ φ, (Γc c ∪ Γstep c) φ → KoreAML.Sym.symbol n ∉ psyms φ) ∧ unresolvedB c n = true := by
    rintro n (hn | hn)
    · exact armName_free hc (List.all_eq_true.mp hnames n (List.contains_iff_mem.mp hn))
    · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hn
      have hpn : p.1 = n := by have := List.find?_some hp; exact beq_iff_eq.mp this
      have := List.all_eq_true.mp hfs p (List.mem_of_find?_eq_some hp)
      simp only [Bool.and_eq_true] at this
      exact hpn ▸ armName_free hc this.2
  obtain ⟨I, hM', hstep⟩ := model_with_inits_arm c hc hf N' (nodFunAr fs (armAr eqs))
    (nodFunG fs (armGOf c eqs names order (armBase c eqs))) hN'
  have hM : InitModel c (fun n => names.contains n = true) (armAr eqs) (armGOf c eqs names order (armBase c eqs)) I :=
    nodFun_restrict hM' (fun n hn => .inl hn)
      (fun n hn => by simp only [nodFunAr, nodFun_find_none hfs1 hn])
      (fun n hn => funext fun ws => by simp only [nodFunG, nodFun_find_none hfs1 hn])
  have hk : lookupSig c.ctorSigs kseq = some ⟨kseq, [Srt.kitem, Srt.k], Srt.k⟩ := by
    simp only [nodFixedB, Bool.and_eq_true, decide_eq_true_eq] at hfix; exact hfix.1.2
  refine ⟨I, hM.sat, hstep, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · have h := List.all_eq_true.mp heq i hi
    unfold nodSentEqB at h
    cases ha : sents.find? (·.index == i) with
    | none => rw [ha] at h; cases h
    | some ad =>
      rw [ha] at h; dsimp only at h
      cases he : Parse.scanEqn (.axiom ad.ax) with
      | none => rw [he] at h; cases h
      | some e =>
        rw [he] at h
        have hi' : ad.index = i := by have := List.find?_some ha; exact beq_iff_eq.mp this
        exact ⟨ad, List.mem_of_find?_eq_some ha, hi', e, he, nod_eqB hM hc hfix hR hord hchk h⟩
  · have h := List.all_eq_true.mp hfun i hi
    unfold nodSentFunB at h
    cases ha : sents.find? (·.index == i) with
    | none => rw [ha] at h; cases h
    | some ad =>
      rw [ha] at h; dsimp only at h
      cases hfa : nodFunctional? ad.ax with
      | none => rw [hfa] at h; cases h
      | some p =>
        obtain ⟨L, S⟩ := p
        rw [hfa] at h; dsimp only at h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨⟨hn, har⟩, hlk⟩, hsr⟩ := h
        have hi' : ad.index = i := by have := List.find?_some ha; exact beq_iff_eq.mp this
        refine ⟨ad, List.mem_of_find?_eq_some ha, hi', L, S, hfa, fun s hS y => ?_⟩
        cases hl : armLook order eqs L with
        | none => rw [hl] at hlk; cases hlk
        | some e =>
          rw [hl] at hlk
          have hx : Parse.distinctEVars? e.pats = some [] := of_decide_eq_true hlk
          rw [hS] at hsr
          split at hsr
          · rename_i s0 s' hR0 hs'
            cases hs'
            have : s0 = s := of_decide_eq_true hsr
            subst this
            exact nod_const_functional hM hc hk hR hchk hn hl hx har hR0 y
          · cases hsr
  · have h := List.all_eq_true.mp hat i hi
    unfold nodSentFunAtB at h
    cases ha : sents.find? (·.index == i) with
    | none => rw [ha] at h; cases h
    | some ad =>
      rw [ha] at h; dsimp only at h
      have hi' : ad.index = i := by have := List.find?_some ha; exact beq_iff_eq.mp this
      cases hfa : nodFunctionalAt? ad.ax with
      | none => rw [hfa] at h; cases h
      | some p =>
        obtain ⟨L, xs0, S⟩ := p
        rw [hfa] at h
        cases xs0 with
        | nil => cases h
        | cons x xs =>
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨hfd, hxS⟩, -⟩ := h
          refine ⟨ad, List.mem_of_find?_eq_some ha, hi', L, x :: xs, S, hfa, ?_⟩
          intro ws hws s hS y
          have hsorted := nodVals_sorted hws
          cases hws with
          | cons hw hws' =>
            rename_i w ws'
            obtain ⟨s0, hx0, hw0⟩ := hw
            rw [hxS, hS] at hx0
            cases hx0
            have hNL : N' L := .inr (by rw [hfd]; rfl)
            have hlen : (w :: ws').length = nodFunAr fs (armAr eqs) L := by
              simp only [nodFunAr, hfd, List.length_cons, (nodVals_sorts hws').2]
            have hG : nodFunG fs (armGOf c eqs names order (armBase c eqs)) L (w :: ws') = some w := by
              simp only [nodFunG, hfd, List.head?_cons]
            have hden : DenV c I (KoreAML.appList (symP L) ((w :: ws').map (den c))) w :=
              ⟨⟨s, hw0⟩, fun ρ m => by
                rw [hM'.names L hNL (w :: ws') hlen hsorted ρ m, hG]
                simp⟩
            exact hM'.functional hden hw0 y

/-! ## Under every interpretation of the parameters -/

kernel_rfl nodFunsB_withHooks : ∀ (c : Semantics) (H : HookParams) (Nm : Parse.Names) (msrc : String)
  (eqs : List Parse.RawEqn) (names : List String) (fs : List (String × Nat)),
  nodFunsB Nm msrc eqs (c.withHooks H) names fs = nodFunsB Nm msrc eqs c names fs
kernel_rfl nodSentFunAtB_withHooks : ∀ (c : Semantics) (H : HookParams) (fs : List (String × Nat))
  (sents : List KoreAML.AxiomDecl) (i : Nat), nodSentFunAtB (c.withHooks H) fs sents i = nodSentFunAtB c fs sents i

/-- **`nod_instance_fun` under every interpretation `H` of the parameters**, its checks decided once
on the data: each reads no interpretation. -/
theorem nod_instance_fun_withHooks (c : Semantics) (hc : c.coreOK = true) (hf : ∀ H, FnHyp (c.withHooks H))
    (Nm : Parse.Names) (msrc : String) (eqs : List Parse.RawEqn) (cells : List Cell) (names order : List String)
    (sents : List KoreAML.AxiomDecl) (eqIdx funIdx : List Nat) (fs : List (String × Nat)) (funAtIdx : List Nat)
    (hnames : names.all (armNameB Nm msrc eqs c) = true) (hR : armRankB order eqs = true)
    (hord : order.all names.contains = true) (hchk : nodOrderB c names eqs order = true)
    (hfix : nodFixedB c = true)
    (heq : eqIdx.all (nodSentEqB Nm msrc eqs c cells names order sents) = true)
    (hfun : funIdx.all (nodSentFunB c eqs names order sents) = true)
    (hfs : nodFunsB Nm msrc eqs c names fs = true)
    (hat : funAtIdx.all (nodSentFunAtB c fs sents) = true) (H : HookParams) :
    ∃ I : Interpretation KoreAML.Sym Elem, (I ⊧ᴵP (Γc (c.withHooks H) ∪ Γstep (c.withHooks H))) ∧
      (∀ x y : Config (c.withHooks H),
        Step (c.withHooks H) x y ↔ ¬ (I ⊧ᴵ (den (c.withHooks H) x.val ⇒ ∼ KoreAML.sNext (den (c.withHooks H) y.val)))) ∧
      (∀ i ∈ eqIdx, ∃ ad ∈ sents, ad.index = i ∧ ∃ e, Parse.scanEqn (.axiom ad.ax) = some e ∧
        NodEqn (c.withHooks H) I e) ∧
      (∀ i ∈ funIdx, ∃ ad ∈ sents, ad.index = i ∧ ∃ L S, nodFunctional? ad.ax = some (L, S) ∧
        NodFun (c.withHooks H) I L S) ∧
      (∀ i ∈ funAtIdx, ∃ ad ∈ sents, ad.index = i ∧ ∃ L xs S, nodFunctionalAt? ad.ax = some (L, xs, S) ∧
        NodFunAt (c.withHooks H) I L xs S) :=
  nod_instance_fun (c.withHooks H) ((Semantics.coreOK_withHooks c H).trans hc) (hf H) Nm msrc eqs cells names order sents
    eqIdx funIdx fs funAtIdx
    (by rw [show armNameB Nm msrc eqs (c.withHooks H) = armNameB Nm msrc eqs c from funext (armNameB_withHooks c H Nm msrc eqs)]; exact hnames) hR hord
    ((nodOrderB_withHooks c H names eqs order).trans hchk) ((nodFixedB_withHooks c H).trans hfix)
    (by rw [show nodSentEqB Nm msrc eqs (c.withHooks H) cells names order sents = nodSentEqB Nm msrc eqs c cells names order sents from funext (nodSentEqB_withHooks c H Nm msrc eqs cells names order sents)]; exact heq)
    (by rw [show nodSentFunB (c.withHooks H) eqs names order sents = nodSentFunB c eqs names order sents from funext (nodSentFunB_withHooks c H eqs names order sents)]; exact hfun)
    ((nodFunsB_withHooks c H Nm msrc eqs names fs).trans hfs)
    (by rw [show nodSentFunAtB (c.withHooks H) fs sents = nodSentFunAtB c fs sents from funext (nodSentFunAtB_withHooks c H fs sents)]; exact hat)

end GenEqs

end KCore
