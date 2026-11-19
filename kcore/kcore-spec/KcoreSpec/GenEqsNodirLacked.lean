/-
  The arm's names (`KcoreSpec/GenEqsNodir.lean`) checked by the symbols of the semantics alone:
  a name no symbol of the semantics bears occurs in no premise of the theory, whatever symbols the
  registry numbers. This takes, beside the generated symbols, a constant of the library that the
  theory lacks because no read sentence applies it (K-IO's `#stdin`, `#stdout`, applied by the
  stream cells' initializers), and the registry's projections, with no decision over the theory's
  premises.

  - **The check (`nodLackedB`).** The name is neither `inj` nor `Lblite`, and no symbol of
    `kernelSyms c` has it.
  - **What it gives (`nodLacked_free`).** Every symbol of a premise is `inj` or a head the
    semantics applies (`premise_symbol_names`), whose name is a symbol's name or `Lblite`
    (`gammaHead`): so such a name occurs in no premise and no symbol resolves to it, what
    `model_with_inits_arm` asks of each name. The model may give it any meaning; placed in `order`
    with its equation, the arm gives it its right side's value.
  - **The instance (`nod_instance_lacked`, `nod_instance_lacked_withHooks`).** `nod_instance` at
    these names: one model of the theory whose steps are the semantics', in which each listed
    equation holds at every list of values of its variables' sorts and each listed `functional`
    axiom holds; for every interpretation of the parameters, the checks decided once on the data.
-/
import KcoreSpec.GenEqsNodir
import KcoreSpec.TieHeadsComplete

set_option autoImplicit false

namespace KCore

open ML Faithful

namespace GenEqs

open Faithful.Model

/-- The name is neither `inj` nor `Lblite`, and no symbol of the semantics bears it. -/
def nodLackedB (c : Semantics) (n : String) : Bool :=
  n != "inj" && n != "Lblite" && (kernelSyms c).all (fun k => c.symName k.name != n)

/-- **A name `nodLackedB` accepts occurs in no premise of the theory and no symbol resolves to
it.** -/
theorem nodLacked_free {c : Semantics} (hc : c.coreOK = true) {n : String} (h : nodLackedB c n = true) :
    (∀ φ, (Γc c ∪ Γstep c) φ → KoreAML.Sym.symbol n ∉ psyms φ) ∧ unresolvedB c n = true := by
  unfold nodLackedB at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨hinj, hl⟩, hall⟩ := h
  have hk : ∀ k ∈ kernelSyms c, c.symName k.name ≠ n := fun k hk =>
    bne_iff_ne.mp (List.all_eq_true.mp hall k hk)
  refine ⟨fun φ hφ hm => ?_, ?_⟩
  · rcases GHComplete.premise_symbol_names c hc φ hφ n hm with h1 | ⟨k, hk', he⟩
    · exact hinj h1
    · unfold gammaHead at he
      split at he
      · exact hl he
      · exact hk k hk' he.symm
  · have hres : Faithful.Model.resolve c n [] = none := by
      rw [Faithful.Model.resolve_nil, Option.map_eq_none_iff, List.find?_eq_none]
      intro k hk' hn
      exact hk k hk' (beq_iff_eq.mp hn)
    simp only [unresolvedB, hres, Option.isNone_none, Bool.and_true, Bool.and_eq_true, bne_iff_ne, ne_eq]
    exact ⟨hinj, hl⟩

/-- **`nod_instance` at names `nodLackedB` accepts.** -/
theorem nod_instance_lacked (c : Semantics) (hc : c.coreOK = true) (hf : FnHyp c) (Nm : Parse.Names)
    (msrc : String) (eqs : List Parse.RawEqn) (cells : List Cell) (names order : List String)
    (sents : List KoreAML.AxiomDecl) (eqIdx funIdx : List Nat)
    (hnames : names.all (nodLackedB c) = true)
    (hR : armRankB order eqs = true)
    (hord : order.all names.contains = true) (hchk : nodOrderB c names eqs order = true)
    (hfix : nodFixedB c = true)
    (heq : eqIdx.all (nodSentEqB Nm msrc eqs c cells names order sents) = true)
    (hfun : funIdx.all (nodSentFunB c eqs names order sents) = true) :
    ∃ I : Interpretation KoreAML.Sym Elem, (I ⊧ᴵP (Γc c ∪ Γstep c)) ∧
      (∀ x y : Config c, Step c x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val)))) ∧
      (∀ i ∈ eqIdx, ∃ ad ∈ sents, ad.index = i ∧ ∃ e, Parse.scanEqn (.axiom ad.ax) = some e ∧ NodEqn c I e) ∧
      (∀ i ∈ funIdx, ∃ ad ∈ sents, ad.index = i ∧ ∃ L S, nodFunctional? ad.ax = some (L, S) ∧ NodFun c I L S) := by
  obtain ⟨I, hM, hstep⟩ := model_with_inits_arm c hc hf (fun n => names.contains n = true) (armAr eqs)
    (armG c names.contains (armAr eqs) order eqs (armBase c eqs) order.length)
    (fun n hn => nodLacked_free hc (List.all_eq_true.mp hnames n (List.contains_iff_mem.mp hn)))
  have hk : lookupSig c.ctorSigs kseq = some ⟨kseq, [Srt.kitem, Srt.k], Srt.k⟩ := by
    simp only [nodFixedB, Bool.and_eq_true, decide_eq_true_eq] at hfix; exact hfix.1.2
  refine ⟨I, hM.sat, hstep, fun i hi => ?_, fun i hi => ?_⟩
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

kernel_rfl nodLackedB_withHooks : ∀ (c : Semantics) (H : HookParams) (n : String),
  nodLackedB (c.withHooks H) n = nodLackedB c n

/-- **`nod_instance_lacked` under every interpretation `H` of the parameters**, its checks decided
once on the data: each reads no interpretation. -/
theorem nod_instance_lacked_withHooks (c : Semantics) (hc : c.coreOK = true) (hf : ∀ H, FnHyp (c.withHooks H))
    (Nm : Parse.Names) (msrc : String) (eqs : List Parse.RawEqn) (cells : List Cell) (names order : List String)
    (sents : List KoreAML.AxiomDecl) (eqIdx funIdx : List Nat)
    (hnames : names.all (nodLackedB c) = true)
    (hR : armRankB order eqs = true)
    (hord : order.all names.contains = true) (hchk : nodOrderB c names eqs order = true)
    (hfix : nodFixedB c = true)
    (heq : eqIdx.all (nodSentEqB Nm msrc eqs c cells names order sents) = true)
    (hfun : funIdx.all (nodSentFunB c eqs names order sents) = true) (H : HookParams) :
    ∃ I : Interpretation KoreAML.Sym Elem, (I ⊧ᴵP (Γc (c.withHooks H) ∪ Γstep (c.withHooks H))) ∧
      (∀ x y : Config (c.withHooks H),
        Step (c.withHooks H) x y ↔ ¬ (I ⊧ᴵ (den (c.withHooks H) x.val ⇒ ∼ KoreAML.sNext (den (c.withHooks H) y.val)))) ∧
      (∀ i ∈ eqIdx, ∃ ad ∈ sents, ad.index = i ∧ ∃ e, Parse.scanEqn (.axiom ad.ax) = some e ∧
        NodEqn (c.withHooks H) I e) ∧
      (∀ i ∈ funIdx, ∃ ad ∈ sents, ad.index = i ∧ ∃ L S, nodFunctional? ad.ax = some (L, S) ∧
        NodFun (c.withHooks H) I L S) :=
  nod_instance_lacked (c.withHooks H) ((Semantics.coreOK_withHooks c H).trans hc) (hf H) Nm msrc eqs cells names
    order sents eqIdx funIdx
    (by rw [show nodLackedB (c.withHooks H) = nodLackedB c from funext (nodLackedB_withHooks c H)]; exact hnames)
    hR hord ((nodOrderB_withHooks c H names eqs order).trans hchk) ((nodFixedB_withHooks c H).trans hfix)
    (by rw [show nodSentEqB Nm msrc eqs (c.withHooks H) cells names order sents = nodSentEqB Nm msrc eqs c cells names order sents from funext (nodSentEqB_withHooks c H Nm msrc eqs cells names order sents)]; exact heq)
    (by rw [show nodSentFunB (c.withHooks H) eqs names order sents = nodSentFunB c eqs names order sents from funext (nodSentFunB_withHooks c H eqs names order sents)]; exact hfun)

end GenEqs

end KCore
