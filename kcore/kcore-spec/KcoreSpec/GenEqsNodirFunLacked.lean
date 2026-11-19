/-
  The `functional` axioms `∃y:S. y = L(x̄)` of symbols the semantics lacks that the text gives no
  equation (a library function no read sentence applies, such as a hooked map function), with the
  no-direction equations and constant initializers' `functional` axioms of `nod_instance`, in one
  model of the theory; each name and each such symbol checked by the symbols of the semantics alone
  (`nodLackedB`, `KcoreSpec/GenEqsNodirLacked.lean`).

  - **The sentence (`nodFunctionalAt?`, `KcoreSpec/GenEqsNodirFun.lean`).** `∃y:S. y = L(x₁, …, xₙ)`,
    `L` a symbol without sort arguments applied to element variables.
  - **The model (`nod_instance_funv_lacked`).** The text states nothing of such a symbol but that
    it is `functional`, so a model may give it any total function into `S`. Here a symbol of `fs`
    is given its first argument, where the first variable is of the sort `S` (`nodSentFunAtB`), and
    a symbol of `fv` the value `fv` lists for it, a value of the sort `S` (`nodSentFunValB`): the
    model `model_with_inits_arm` gives at the names and the symbols of `fs` and `fv` together, each
    borne by no symbol of the semantics, so that no premise of the theory names it
    (`nodLacked_free`). The arm's lemmas read the model only at its names (`nodFun_restrict`).
  - **In a given model (`nod_funv_lacked_of_model`).** The same sentences hold in any model that
    gives the names and the symbols of `fs` and `fv` these meanings, whatever it gives other names:
    an instance that gives further lacked symbols meanings reads it. For such symbols:
    `nod_const_dv_eqn` and `nod_const_dv_functional` (a constant whose equation's right side is a
    domain value; `nod_order_dv` for a constant of `order`), `nod_alias_dv_eqn` (`L(x) = L₂(x, d)`).
-/
import KcoreSpec.GenEqsNodirFun
import KcoreSpec.GenEqsNodirLacked

set_option autoImplicit false

namespace KCore

open ML Faithful

namespace GenEqs

open Faithful.Model

/-- The arity of a name: `fs`'s for a symbol of `fs`, `fv`'s for a symbol of `fv`, `ar`'s otherwise. -/
def nodFunValAr (fs : List (String × Nat)) (fv : List (String × Nat × GroundTerm)) (ar : String → Nat) (n : String) :
    Nat :=
  match fs.find? (·.1 == n) with
  | some p => p.2
  | none => match fv.find? (·.1 == n) with
    | some p => p.2.1
    | none => ar n

/-- The names' values: a symbol of `fs` its first argument, a symbol of `fv` its listed value,
another name `G`'s. -/
def nodFunValG (fs : List (String × Nat)) (fv : List (String × Nat × GroundTerm))
    (G : String → List GroundTerm → Option GroundTerm) : String → List GroundTerm → Option GroundTerm := fun n ws =>
  match fs.find? (·.1 == n) with
  | some _ => ws.head?
  | none => match fv.find? (·.1 == n) with
    | some p => some p.2.2
    | none => G n ws

/-- The symbols of `fs` and `fv` are none of the names and each is borne by no symbol of the
semantics (`nodLackedB`). -/
def nodFunsLackedB (c : Semantics) (names : List String) (fs : List (String × Nat))
    (fv : List (String × Nat × GroundTerm)) : Bool :=
  fs.all (fun p => !names.contains p.1 && nodLackedB c p.1) &&
    fv.all (fun p => !names.contains p.1 && nodLackedB c p.1)

/-- The sentence of index `i` is a `functional` axiom `∃y:S. y = L(x₁, …, xₙ)` with `L` of `fv` at
arity `n` and not of `fs`, its listed value of the sort `S`, a sort of the semantics. -/
def nodSentFunValB (c : Semantics) (fs : List (String × Nat)) (fv : List (String × Nat × GroundTerm))
    (sents : List KoreAML.AxiomDecl) (i : Nat) : Bool :=
  match sents.find? (·.index == i) with
  | some ad => match nodFunctionalAt? ad.ax with
    | some (L, xs, S) => (fs.find? (·.1 == L)).isNone &&
        (match fv.find? (·.1 == L) with
         | some p => decide (p.2.1 = xs.length) &&
            (match armSrt c S with
             | some s => decide (c.sortOf p.2.2 = some s)
             | none => false)
         | none => false)
    | none => false
  | none => false

theorem nodFunVal_find_none {c : Semantics} {fs : List (String × Nat)} {fv : List (String × Nat × GroundTerm)} {names : List String}
    {n : String} (hfs : nodFunsLackedB c names fs fv = true) (hn : names.contains n = true) :
    fs.find? (·.1 == n) = none ∧ fv.find? (·.1 == n) = none := by
  unfold nodFunsLackedB at hfs
  simp only [Bool.and_eq_true] at hfs
  refine ⟨List.find?_eq_none.mpr fun p hp he => ?_, List.find?_eq_none.mpr fun p hp he => ?_⟩
  · have := List.all_eq_true.mp hfs.1 p hp
    rw [beq_iff_eq.mp he, hn] at this
    cases this
  · have := List.all_eq_true.mp hfs.2 p hp
    rw [beq_iff_eq.mp he, hn] at this
    cases this

/-- The names the model gives meanings: the names, and the symbols of `fs` and of `fv`. -/
abbrev nodFunValN (names : List String) (fs : List (String × Nat)) (fv : List (String × Nat × GroundTerm))
    (n : String) : Prop :=
  names.contains n = true ∨ (fs.find? (·.1 == n)).isSome = true ∨ (fv.find? (·.1 == n)).isSome = true

/-- **No premise of the theory names a name of `nodFunValN`, and none resolves to a symbol**: each
is borne by no symbol of the semantics. -/
theorem nodFunValN_free {c : Semantics} (hc : c.coreOK = true) {names : List String} {fs : List (String × Nat)}
    {fv : List (String × Nat × GroundTerm)} (hnames : names.all (nodLackedB c) = true)
    (hfs : nodFunsLackedB c names fs fv = true) :
    ∀ n, nodFunValN names fs fv n →
      (∀ φ, (Γc c ∪ Γstep c) φ → KoreAML.Sym.symbol n ∉ psyms φ) ∧ unresolvedB c n = true := by
  unfold nodFunsLackedB at hfs
  simp only [Bool.and_eq_true] at hfs
  obtain ⟨hfsA, hfvA⟩ := hfs
  rintro n (hn | hn | hn)
  · exact nodLacked_free hc (List.all_eq_true.mp hnames n (List.contains_iff_mem.mp hn))
  · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hn
    have hpn : p.1 = n := by have := List.find?_some hp; exact beq_iff_eq.mp this
    have := List.all_eq_true.mp hfsA p (List.mem_of_find?_eq_some hp)
    simp only [Bool.and_eq_true] at this
    exact hpn ▸ nodLacked_free hc this.2
  · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hn
    have hpn : p.1 = n := by have := List.find?_some hp; exact beq_iff_eq.mp this
    have := List.all_eq_true.mp hfvA p (List.mem_of_find?_eq_some hp)
    simp only [Bool.and_eq_true] at this
    exact hpn ▸ nodLacked_free hc this.2

/-- **In a model that gives the names, `fs` and `fv` their meanings, each listed sentence holds**:
`nod_instance`'s equations (`eqIdx`) and constants' `functional` axioms (`funIdx`), and the
`functional` axioms of the symbols of `fs` (`funAtIdx`) and of `fv` (`funValIdx`), at every list of
values of their variables' sorts. The model may give other names meanings as well: it is read at
these names only. -/
theorem nod_funv_lacked_of_model (c : Semantics) (hc : c.coreOK = true) (Nm : Parse.Names)
    (msrc : String) (eqs : List Parse.RawEqn) (cells : List Cell) (names order : List String)
    (sents : List KoreAML.AxiomDecl) (eqIdx funIdx : List Nat) (fs : List (String × Nat))
    (fv : List (String × Nat × GroundTerm)) (funAtIdx funValIdx : List Nat)
    (hR : armRankB order eqs = true)
    (hord : order.all names.contains = true) (hchk : nodOrderB c names eqs order = true)
    (hfix : nodFixedB c = true)
    (heq : eqIdx.all (nodSentEqB Nm msrc eqs c cells names order sents) = true)
    (hfun : funIdx.all (nodSentFunB c eqs names order sents) = true)
    (hfs : nodFunsLackedB c names fs fv = true)
    (hat : funAtIdx.all (nodSentFunAtB c fs sents) = true)
    (hval : funValIdx.all (nodSentFunValB c fs fv sents) = true)
    {I : Interpretation KoreAML.Sym Elem}
    (hM' : InitModel c (nodFunValN names fs fv) (nodFunValAr fs fv (armAr eqs))
      (nodFunValG fs fv (armGOf c eqs names order (armBase c eqs))) I) :
      (∀ i ∈ eqIdx, ∃ ad ∈ sents, ad.index = i ∧ ∃ e, Parse.scanEqn (.axiom ad.ax) = some e ∧ NodEqn c I e) ∧
      (∀ i ∈ funIdx, ∃ ad ∈ sents, ad.index = i ∧ ∃ L S, nodFunctional? ad.ax = some (L, S) ∧ NodFun c I L S) ∧
      (∀ i ∈ funAtIdx, ∃ ad ∈ sents, ad.index = i ∧ ∃ L xs S, nodFunctionalAt? ad.ax = some (L, xs, S) ∧
        NodFunAt c I L xs S) ∧
      (∀ i ∈ funValIdx, ∃ ad ∈ sents, ad.index = i ∧ ∃ L xs S, nodFunctionalAt? ad.ax = some (L, xs, S) ∧
        NodFunAt c I L xs S) := by
  have hfs' : nodFunsLackedB c names fs fv = true := hfs
  have hM : InitModel c (fun n => names.contains n = true) (armAr eqs) (armGOf c eqs names order (armBase c eqs)) I :=
    nodFun_restrict hM' (fun n hn => Or.inl hn)
      (fun n hn => by
        obtain ⟨h1, h2⟩ := nodFunVal_find_none hfs' hn
        simp only [nodFunValAr, h1, h2])
      (fun n hn => funext fun ws => by
        obtain ⟨h1, h2⟩ := nodFunVal_find_none hfs' hn
        simp only [nodFunValG, h1, h2])
  have hk : lookupSig c.ctorSigs kseq = some ⟨kseq, [Srt.kitem, Srt.k], Srt.k⟩ := by
    simp only [nodFixedB, Bool.and_eq_true, decide_eq_true_eq] at hfix; exact hfix.1.2
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
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
            have hNL : nodFunValN names fs fv L := .inr (.inl (by rw [hfd]; rfl))
            have hlen : (w :: ws').length = nodFunValAr fs fv (armAr eqs) L := by
              simp only [nodFunValAr, hfd, List.length_cons, (nodVals_sorts hws').2]
            have hG : nodFunValG fs fv (armGOf c eqs names order (armBase c eqs)) L (w :: ws') = some w := by
              simp only [nodFunValG, hfd, List.head?_cons]
            have hden : DenV c I (KoreAML.appList (symP L) ((w :: ws').map (den c))) w :=
              ⟨⟨s, hw0⟩, fun ρ m => by
                rw [hM'.names L hNL (w :: ws') hlen hsorted ρ m, hG]
                simp⟩
            exact hM'.functional hden hw0 y
  · have h := List.all_eq_true.mp hval i hi
    unfold nodSentFunValB at h
    cases ha : sents.find? (·.index == i) with
    | none => rw [ha] at h; cases h
    | some ad =>
      rw [ha] at h; dsimp only at h
      have hi' : ad.index = i := by have := List.find?_some ha; exact beq_iff_eq.mp this
      cases hfa : nodFunctionalAt? ad.ax with
      | none => rw [hfa] at h; cases h
      | some p =>
        obtain ⟨L, xs, S⟩ := p
        rw [hfa] at h; dsimp only at h
        simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at h
        obtain ⟨hfn, hv⟩ := h
        cases hfv : fv.find? (·.1 == L) with
        | none => rw [hfv] at hv; cases hv
        | some q =>
          rw [hfv] at hv; dsimp only at hv
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
          obtain ⟨hql, hqs⟩ := hv
          refine ⟨ad, List.mem_of_find?_eq_some ha, hi', L, xs, S, hfa, ?_⟩
          intro ws hws s hS y
          rw [hS] at hqs
          have hvs : c.sortOf q.2.2 = some s := of_decide_eq_true hqs
          have hsorted := nodVals_sorted hws
          have hNL : nodFunValN names fs fv L := .inr (.inr (by rw [hfv]; rfl))
          have hlen : ws.length = nodFunValAr fs fv (armAr eqs) L := by
            simp only [nodFunValAr, hfn, hfv, hql, (nodVals_sorts hws).2]
          have hG : nodFunValG fs fv (armGOf c eqs names order (armBase c eqs)) L ws = some q.2.2 := by
            simp only [nodFunValG, hfn, hfv]
          have hden : DenV c I (KoreAML.appList (symP L) (ws.map (den c))) q.2.2 :=
            ⟨⟨s, hvs⟩, fun ρ m => by
              rw [hM'.names L hNL ws hlen hsorted ρ m, hG]
              simp⟩
          exact hM'.functional hden hvs y

/-- **One model of the theory, whose steps are the semantics', in which each listed sentence
holds**: `nod_instance`'s equations (`eqIdx`) and constants' `functional` axioms (`funIdx`), and the
`functional` axioms of the symbols of `fs` (`funAtIdx`) and of `fv` (`funValIdx`), at every list of
values of their variables' sorts; the names, `fs` and `fv` borne by no symbol of the semantics. -/
theorem nod_instance_funv_lacked (c : Semantics) (hc : c.coreOK = true) (hf : FnHyp c) (Nm : Parse.Names)
    (msrc : String) (eqs : List Parse.RawEqn) (cells : List Cell) (names order : List String)
    (sents : List KoreAML.AxiomDecl) (eqIdx funIdx : List Nat) (fs : List (String × Nat))
    (fv : List (String × Nat × GroundTerm)) (funAtIdx funValIdx : List Nat)
    (hnames : names.all (nodLackedB c) = true) (hR : armRankB order eqs = true)
    (hord : order.all names.contains = true) (hchk : nodOrderB c names eqs order = true)
    (hfix : nodFixedB c = true)
    (heq : eqIdx.all (nodSentEqB Nm msrc eqs c cells names order sents) = true)
    (hfun : funIdx.all (nodSentFunB c eqs names order sents) = true)
    (hfs : nodFunsLackedB c names fs fv = true)
    (hat : funAtIdx.all (nodSentFunAtB c fs sents) = true)
    (hval : funValIdx.all (nodSentFunValB c fs fv sents) = true) :
    ∃ I : Interpretation KoreAML.Sym Elem, (I ⊧ᴵP (Γc c ∪ Γstep c)) ∧
      (∀ x y : Config c, Step c x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val)))) ∧
      (∀ i ∈ eqIdx, ∃ ad ∈ sents, ad.index = i ∧ ∃ e, Parse.scanEqn (.axiom ad.ax) = some e ∧ NodEqn c I e) ∧
      (∀ i ∈ funIdx, ∃ ad ∈ sents, ad.index = i ∧ ∃ L S, nodFunctional? ad.ax = some (L, S) ∧ NodFun c I L S) ∧
      (∀ i ∈ funAtIdx, ∃ ad ∈ sents, ad.index = i ∧ ∃ L xs S, nodFunctionalAt? ad.ax = some (L, xs, S) ∧
        NodFunAt c I L xs S) ∧
      (∀ i ∈ funValIdx, ∃ ad ∈ sents, ad.index = i ∧ ∃ L xs S, nodFunctionalAt? ad.ax = some (L, xs, S) ∧
        NodFunAt c I L xs S) := by
  obtain ⟨I, hM', hstep⟩ := model_with_inits_arm c hc hf (nodFunValN names fs fv) (nodFunValAr fs fv (armAr eqs))
    (nodFunValG fs fv (armGOf c eqs names order (armBase c eqs))) (nodFunValN_free hc hnames hfs)
  exact ⟨I, hM'.sat, hstep, nod_funv_lacked_of_model c hc Nm msrc eqs cells names order sents eqIdx funIdx fs fv
    funAtIdx funValIdx hR hord hchk hfix heq hfun hfs hat hval hM'⟩

kernel_rfl nodFunsLackedB_withHooks : ∀ (c : Semantics) (H : HookParams) (names : List String)
  (fs : List (String × Nat)) (fv : List (String × Nat × GroundTerm)),
  nodFunsLackedB (c.withHooks H) names fs fv = nodFunsLackedB c names fs fv
/-- `nodSentFunValB` reads no interpretation where no parameter is an open generator (the values'
sorts, `Semantics.sortOf_withHooks`). -/
theorem nodSentFunValB_withHooks (c : Semantics) (H : HookParams) (hr : ∀ k ∈ c.params, k.raw = false)
    (fs : List (String × Nat)) (fv : List (String × Nat × GroundTerm)) (sents : List KoreAML.AxiomDecl) (i : Nat) :
    nodSentFunValB (c.withHooks H) fs fv sents i = nodSentFunValB c fs fv sents i := by
  unfold nodSentFunValB
  rw [Semantics.sortOf_withHooks c H hr]
  rfl

/-- **`nod_instance_funv_lacked` under every interpretation `H` of the parameters**, its checks
decided once on the data: each reads no interpretation where no parameter is an open generator. -/
theorem nod_instance_funv_lacked_withHooks (c : Semantics) (hc : c.coreOK = true) (hf : ∀ H, FnHyp (c.withHooks H))
    (hr : ∀ k ∈ c.params, k.raw = false)
    (Nm : Parse.Names) (msrc : String) (eqs : List Parse.RawEqn) (cells : List Cell) (names order : List String)
    (sents : List KoreAML.AxiomDecl) (eqIdx funIdx : List Nat) (fs : List (String × Nat))
    (fv : List (String × Nat × GroundTerm)) (funAtIdx funValIdx : List Nat)
    (hnames : names.all (nodLackedB c) = true) (hR : armRankB order eqs = true)
    (hord : order.all names.contains = true) (hchk : nodOrderB c names eqs order = true)
    (hfix : nodFixedB c = true)
    (heq : eqIdx.all (nodSentEqB Nm msrc eqs c cells names order sents) = true)
    (hfun : funIdx.all (nodSentFunB c eqs names order sents) = true)
    (hfs : nodFunsLackedB c names fs fv = true)
    (hat : funAtIdx.all (nodSentFunAtB c fs sents) = true)
    (hval : funValIdx.all (nodSentFunValB c fs fv sents) = true) (H : HookParams) :
    ∃ I : Interpretation KoreAML.Sym Elem, (I ⊧ᴵP (Γc (c.withHooks H) ∪ Γstep (c.withHooks H))) ∧
      (∀ x y : Config (c.withHooks H),
        Step (c.withHooks H) x y ↔ ¬ (I ⊧ᴵ (den (c.withHooks H) x.val ⇒ ∼ KoreAML.sNext (den (c.withHooks H) y.val)))) ∧
      (∀ i ∈ eqIdx, ∃ ad ∈ sents, ad.index = i ∧ ∃ e, Parse.scanEqn (.axiom ad.ax) = some e ∧
        NodEqn (c.withHooks H) I e) ∧
      (∀ i ∈ funIdx, ∃ ad ∈ sents, ad.index = i ∧ ∃ L S, nodFunctional? ad.ax = some (L, S) ∧
        NodFun (c.withHooks H) I L S) ∧
      (∀ i ∈ funAtIdx, ∃ ad ∈ sents, ad.index = i ∧ ∃ L xs S, nodFunctionalAt? ad.ax = some (L, xs, S) ∧
        NodFunAt (c.withHooks H) I L xs S) ∧
      (∀ i ∈ funValIdx, ∃ ad ∈ sents, ad.index = i ∧ ∃ L xs S, nodFunctionalAt? ad.ax = some (L, xs, S) ∧
        NodFunAt (c.withHooks H) I L xs S) :=
  nod_instance_funv_lacked (c.withHooks H) ((Semantics.coreOK_withHooks c H).trans hc) (hf H) Nm msrc eqs cells names
    order sents eqIdx funIdx fs fv funAtIdx funValIdx
    (by rw [show nodLackedB (c.withHooks H) = nodLackedB c from funext (nodLackedB_withHooks c H)]; exact hnames) hR hord
    ((nodOrderB_withHooks c H names eqs order).trans hchk) ((nodFixedB_withHooks c H).trans hfix)
    (by rw [show nodSentEqB Nm msrc eqs (c.withHooks H) cells names order sents = nodSentEqB Nm msrc eqs c cells names order sents from funext (nodSentEqB_withHooks c H Nm msrc eqs cells names order sents)]; exact heq)
    (by rw [show nodSentFunB (c.withHooks H) eqs names order sents = nodSentFunB c eqs names order sents from funext (nodSentFunB_withHooks c H eqs names order sents)]; exact hfun)
    ((nodFunsLackedB_withHooks c H names fs fv).trans hfs)
    (by rw [show nodSentFunAtB (c.withHooks H) fs sents = nodSentFunAtB c fs sents from funext (nodSentFunAtB_withHooks c H fs sents)]; exact hat)
    (by rw [show nodSentFunValB (c.withHooks H) fs fv sents = nodSentFunValB c fs fv sents from funext (nodSentFunValB_withHooks c H hr fs fv sents)]; exact hval)

/-- **`nod_funv_lacked_of_model` under an interpretation `H` of the parameters**, its checks decided
once on the data. -/
theorem nod_funv_lacked_of_model_withHooks (c : Semantics) (hc : c.coreOK = true)
    (hr : ∀ k ∈ c.params, k.raw = false)
    (Nm : Parse.Names) (msrc : String) (eqs : List Parse.RawEqn) (cells : List Cell) (names order : List String)
    (sents : List KoreAML.AxiomDecl) (eqIdx funIdx : List Nat) (fs : List (String × Nat))
    (fv : List (String × Nat × GroundTerm)) (funAtIdx funValIdx : List Nat)
    (hR : armRankB order eqs = true)
    (hord : order.all names.contains = true) (hchk : nodOrderB c names eqs order = true)
    (hfix : nodFixedB c = true)
    (heq : eqIdx.all (nodSentEqB Nm msrc eqs c cells names order sents) = true)
    (hfun : funIdx.all (nodSentFunB c eqs names order sents) = true)
    (hfs : nodFunsLackedB c names fs fv = true)
    (hat : funAtIdx.all (nodSentFunAtB c fs sents) = true)
    (hval : funValIdx.all (nodSentFunValB c fs fv sents) = true) (H : HookParams)
    {I : Interpretation KoreAML.Sym Elem}
    (hM' : InitModel (c.withHooks H) (nodFunValN names fs fv) (nodFunValAr fs fv (armAr eqs))
      (nodFunValG fs fv (armGOf (c.withHooks H) eqs names order (armBase (c.withHooks H) eqs))) I) :
      (∀ i ∈ eqIdx, ∃ ad ∈ sents, ad.index = i ∧ ∃ e, Parse.scanEqn (.axiom ad.ax) = some e ∧
        NodEqn (c.withHooks H) I e) ∧
      (∀ i ∈ funIdx, ∃ ad ∈ sents, ad.index = i ∧ ∃ L S, nodFunctional? ad.ax = some (L, S) ∧
        NodFun (c.withHooks H) I L S) ∧
      (∀ i ∈ funAtIdx, ∃ ad ∈ sents, ad.index = i ∧ ∃ L xs S, nodFunctionalAt? ad.ax = some (L, xs, S) ∧
        NodFunAt (c.withHooks H) I L xs S) ∧
      (∀ i ∈ funValIdx, ∃ ad ∈ sents, ad.index = i ∧ ∃ L xs S, nodFunctionalAt? ad.ax = some (L, xs, S) ∧
        NodFunAt (c.withHooks H) I L xs S) :=
  nod_funv_lacked_of_model (c.withHooks H) ((Semantics.coreOK_withHooks c H).trans hc) Nm msrc eqs cells names
    order sents eqIdx funIdx fs fv funAtIdx funValIdx hR hord
    ((nodOrderB_withHooks c H names eqs order).trans hchk) ((nodFixedB_withHooks c H).trans hfix)
    (by rw [show nodSentEqB Nm msrc eqs (c.withHooks H) cells names order sents = nodSentEqB Nm msrc eqs c cells names order sents from funext (nodSentEqB_withHooks c H Nm msrc eqs cells names order sents)]; exact heq)
    (by rw [show nodSentFunB (c.withHooks H) eqs names order sents = nodSentFunB c eqs names order sents from funext (nodSentFunB_withHooks c H eqs names order sents)]; exact hfun)
    ((nodFunsLackedB_withHooks c H names fs fv).trans hfs)
    (by rw [show nodSentFunAtB (c.withHooks H) fs sents = nodSentFunAtB c fs sents from funext (nodSentFunAtB_withHooks c H fs sents)]; exact hat)
    (by rw [show nodSentFunValB (c.withHooks H) fs fv sents = nodSentFunValB c fs fv sents from funext (nodSentFunValB_withHooks c H hr fs fv sents)]; exact hval)
    hM'

/-! ## A constant's equation to a domain value, and an equation to another name's application -/

/-- `armDv` reads no interpretation where no parameter is an open generator. -/
theorem armDv_withHooks (c : Semantics) (H : HookParams) (hr : ∀ k ∈ c.params, k.raw = false) (S : Kore.KSort)
    (text : String) : armDv (c.withHooks H) S text = armDv c S text := by
  unfold armDv
  rw [Semantics.sortOf_withHooks c H hr]
  rfl

/-- A domain value `armDv` reads at `S` is of the sort of `S`. -/
theorem armDv_sortOf {c : Semantics} {S : Kore.KSort} {text : String} {v : GroundTerm}
    (hd : armDv c S text = some v) {s : Srt} (hS : armSrt c S = some s) : c.sortOf v = some s := by
  unfold armDv at hd
  rw [hS] at hd
  dsimp only at hd
  cases hl : Parse.lit? s text with
  | none => rw [hl] at hd; cases hd
  | some l =>
    rw [hl] at hd
    dsimp only at hd
    split at hd
    · rename_i hcond
      cases hd
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      have h2 := hcond.2
      rw [nod_sortOf_dv] at h2 ⊢
      split at h2
      · rename_i hok; rw [if_pos_walk hok]
      · cases h2
    · cases hd

/-- **The arm's value of a constant of `order` whose equation's right side is a domain value is
that value.** -/
theorem nod_order_dv {c : Semantics} {eqs : List Parse.RawEqn} {names order : List String}
    (hR : armRankB order eqs = true) {n : String} {e : Parse.RawEqn} (he : armLook order eqs n = some e)
    (hp : e.pats = []) {S : Kore.KSort} {text : String} (hrhs : e.rhs = .dv S text) :
    armGOf c eqs names order (armBase c eqs) n [] = armDv c S text := by
  have hx : Parse.distinctEVars? e.pats = some [] := by rw [hp]; rfl
  rw [armGOf, armG_fix c _ _ order eqs _ hR he hx [], hrhs, armVal]
  cases armDv c S text <;> rfl

section ConstEqn

variable {c : Semantics} {N : String → Prop} {ar : String → Nat} {G : String → List GroundTerm → Option GroundTerm}
  {I : Interpretation KoreAML.Sym Elem} (hM : InitModel c N ar G I)
include hM

/-- **A constant's equation to a domain value holds** where the model gives the constant that
value: `L() = \dv{S}(text)`. -/
theorem nod_const_dv_eqn (hc : c.coreOK = true) {e : Parse.RawEqn} {S : Kore.KSort} {text : String} {v : GroundTerm}
    (hp : e.pats = []) (hrhs : e.rhs = .dv S text) (hN : N e.fn) (har : ar e.fn = 0) (hG : G e.fn [] = some v)
    (hd : armDv c S text = some v) : NodEqn c I e := by
  have hx : Parse.distinctEVars? e.pats = some [] := by rw [hp]; rfl
  intro ws hws
  have hvars : armVarsL e.pats = [] := by rw [hp]; rfl
  rw [hvars] at hws ⊢
  cases hws
  have hs := armVal_sound hM hc (isN := fun _ => false) (fun _ h => by cases h) (σ := armZip [] [])
    (fun _ _ h => by cases h) (.dv S text)
  rw [armVal, hd] at hs
  rw [armLhs_den c hx (ws := []) rfl, hrhs]
  exact hM.eqn (hM.name hN .nil har.symm hG hs.1.choose_spec) hs

/-- **A constant's `functional` axiom holds** where the model gives the constant a domain value
read at the axiom's sort. -/
theorem nod_const_dv_functional {L : String} {S : Kore.KSort} {text : String} {v : GroundTerm} (hN : N L)
    (har : ar L = 0) (hG : G L [] = some v) (hd : armDv c S text = some v) : NodFun c I L S := by
  intro s hS y
  have hsv := armDv_sortOf hd hS
  exact hM.functional (hM.name hN .nil har.symm hG hsv) hsv y

/-- **An equation of a name to another name applied to the same variable and a domain value
holds**, `L(x) = L₂(x, \dv{S}(text))`, where the model gives `L` at a value what it gives `L₂` at
that value and the domain value, a value of a sort or nothing. -/
theorem nod_alias_dv_eqn (hc : c.coreOK = true) {e : Parse.RawEqn} {x : Kore.EVar} {n2 : String} {S : Kore.KSort}
    {text : String} {d : GroundTerm} (hp : e.pats = [.var (.evar x)])
    (hrhs : e.rhs = .app ⟨⟨n2⟩⟩ [] [.var (.evar x), .dv S text]) (hne : (n2 == "inj") = false)
    (hN : N e.fn) (hN2 : N n2) (har : ar e.fn = 1) (har2 : ar n2 = 2) (hd : armDv c S text = some d)
    (hG : ∀ a, G e.fn [a] = G n2 [a, d]) (hGs : ∀ a v, G n2 [a, d] = some v → ∃ s, c.sortOf v = some s) :
    NodEqn c I e := by
  have hx : Parse.distinctEVars? e.pats = some [x] := by rw [hp]; rfl
  intro ws hws
  have hvars : armVarsL e.pats = [x] := by rw [hp]; rfl
  rw [hvars] at hws ⊢
  obtain ⟨a, rfl⟩ : ∃ a, ws = [a] := by
    cases hws with
    | cons _ hr => cases hr; exact ⟨_, rfl⟩
  have hsa : ∃ s, c.sortOf a = some s := nodVals_sorted hws a (List.mem_singleton_self a)
  have hs := armVal_sound hM hc (isN := fun n => n == n2) (fun n h => by rw [beq_iff_eq.mp h]; exact hN2)
    (σ := armZip [x] [a]) (fun y w h => by
      have := (List.of_mem_zip (armLookup_mem h)).2
      rw [List.mem_singleton.mp this]; exact hsa) e.rhs
  have hval : armVal c (fun n => n == n2) ar G (armZip [x] [a]) e.rhs =
      match G n2 [a, d] with
      | some v => if (c.sortOf v).isSome then some (some v) else none
      | none => some none := by
    rw [hrhs]
    simp [armVal, armVals, hne, armApp, armEmpty, armWs, armHead, har2, hd, armLookup, armZip]
    cases G n2 [a, d] <;> rfl
  rw [hval] at hs
  rw [armLhs_den c hx (ws := [a]) rfl]
  have hda : All2 (DenV c I) ([a].map (den c)) [a] := armVals_den hM (nodVals_sorted hws)
  cases hg : G n2 [a, d] with
  | none =>
    rw [hg] at hs
    exact hM.eqn_none (hM.name_none hN hda har.symm ((hG a).trans hg)) hs
  | some v =>
    obtain ⟨s, hsv⟩ := hGs a v hg
    rw [hg] at hs
    simp only [hsv, Option.isSome_some, ite_true] at hs
    exact hM.eqn (hM.name hN hda har.symm ((hG a).trans hg) hsv) hs

end ConstEqn

end GenEqs

end KCore
