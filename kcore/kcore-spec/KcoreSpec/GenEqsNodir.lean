/-
  The equations of the generated symbols no read sentence applies (the cell initializers, the
  counter's getter, the sorts' projections) and the initializers' `functional` axioms, at every
  list of values of their variables' sorts, in the model of the account's arm
  (`KcoreSpec/GenEqsInitArm.lean`).

  - **The sorts of a right side (`nodTy`).** A KORE right side, its variables given sorts, is given
    a sort and whether it has a value at every list of values of those sorts: a variable, a
    literal, `inj` over a sort with no subsort (whose values are no injections), a constructor of
    the semantics at arguments of its argument sorts, an interpreted hook at arguments of its
    argument sorts with no silent point, a name at arguments of its argument sorts (`nA`), with the
    sort and totality given it (`nR`). Computed from the text; nothing is written by hand.
  - **What the sorts give (`nodTy_sound`).** Where every name applied gives, at values of its
    argument sorts, a value of its sort or nothing (and a value where total), the arm's reading
    (`armVal`) of the right side at values of the variables' sorts is never `none` (not read): it
    is a value of the sort, or nothing, and a value where total.
  - **The names' `G` (`nod_G_ok`).** The arm's `G` read from the text (`armGOf`) gives each name a
    value of its sort or nothing: a name of `order` by its equation's right side (`armG_fix`, by
    induction along `order`, `armRankB`), the getter and the projections by `armBase` (`argFn`,
    `projFn`, `itemFn`, the identity).
  - **The equations (`nod_init_eqn`, `nod_proj_eqn`, `nod_projK_eqn`, `nod_projKItem_eqn`,
    `nod_getter_eqn`).** In the arm's model, for every list of values of the variables' sorts: an
    initializer's equation `L(xs) = rhs`, the projection `project:X(kseq(inj{X,KItem}(V), dotk)) = V`
    (an injection over a value that is itself an injection denotes the normalised one, by the
    theory's injection coherence, `InitModel.injN`), `project:K(V) = V`,
    `project:KItem(kseq(V, dotk)) = V`, and `getGeneratedCounterCell(<generatedTop>(…, V)) = V`.
    A constant initializer's `functional` axiom `∃y:s. y = L()` (`nod_const_functional`).
  - **By sentence (`nod_instance`).** For lists of sentence indices, each sentence's equation as
    the account's scan reads it (`Parse.scanEqn`), or its `functional` axiom (`nodFunctional?`), and
    a check that it is one of the shapes above (`nodEqB`, `nodFunB`): one model of the theory whose
    steps are the semantics' in which each holds at every list of values of its variables' sorts.
  - **One freeness check for the names (`nod_names_reg`, `nod_instance_reg`).** `freeB` at a list
    of symbols gives `freeB` at each of them (`nodFreeB_sub`): a name of fewer symbols is a name of
    the list, and no item is a hook's arity when no hook is among them. So the names `armNameB`
    accepts are had from one `freeB` at the registry numbers of the sorts' projections among them
    (`nodRegKs`) and, for each name, `armNameB`'s other checks (`nodNameB`).
-/
import KcoreSpec.GenEqsInitArm
import KcoreSpec.InjValue
import KcoreSpec.DataCmd
import KcoreSpec.FnObligations

set_option autoImplicit false

namespace KCore

open ML Faithful

namespace GenEqs

open Faithful.Model

/-! ## The sorts of a right side -/

/-- The sort `vs` gives the variable `x`, the first. -/
def nodLook (vs : List (Kore.EVar × Srt)) (x : Kore.EVar) : Option Srt :=
  (vs.find? fun p => decide (p.1 = x)).map (·.2)

/-- The sort of a literal the arm reads (`armDv`): its sort, where its text is the value's own and
the library admits it. -/
def nodDv (c : Semantics) (S : Kore.KSort) (text : String) : Option Srt :=
  match armSrt c S with
  | some s => match Parse.lit? s text with
    | some l => if decide ((GroundTerm.dv s l).kore c = .dv S text) && dvOK c.lib s l then some s else none
    | none => none
  | none => none

/-- The head `h` at arguments of the sorts `ts` (with their totality): a name of its argument
sorts `nA h`, of the sort `nR h`; a constructor of `c` at its argument sorts; an interpreted hook
at its argument sorts with no silent point (`silentKey`), total where it is a constant with a value. -/
def nodHead (c : Semantics) (isN : String → Bool) (ar : String → Nat) (nA : String → List Srt)
    (nR : String → Option (Srt × Bool)) (h : String) (ts : List (Srt × Bool)) : Option (Srt × Bool) :=
  if isN h then
    if decide (ts.map (·.1) = nA h) && decide (ts.length = ar h) then
      (nR h).map fun st => (st.1, st.2 && ts.all (·.2))
    else none
  else match c.ctorSigs.find? (fun k => c.symName k.name == h) with
  | some k =>
    if decide (lookupSig c.ctorSigs k.name = some k) && decide (ts.map (·.1) = k.args) then
      some (k.result, ts.all (·.2))
    else none
  | none => match hookSigs.find? (fun k => c.symName k.name == h) with
    | some k =>
      if decide (iteSort? h = none) && decide (lookupSig hookSigs k.name = some k) &&
          decide (ts.map (·.1) = k.args) && !silentKey k.name && isHook k.name && decide (k.name ≠ rmKeys) then
        some (k.result, ts.isEmpty && (match hook k.name [] with | some (some _) => true | _ => false))
      else none
    | none => none

/-- `inj{A, B}` over an argument of the sort `A`, a sort with no subsort (no value of it is an
injection), and a subsort of `B`: of the sort `B`. -/
def nodInjTy (c : Semantics) : List Kore.KSort → Option (List (Srt × Bool)) → Option (Srt × Bool)
  | sA :: sB :: [], some (st :: []) => match armSrt c sA, armSrt c sB with
    | some a, some b =>
      if decide (st.1 = a) && c.subsorts.contains (a, b) && c.subsorts.all (·.2 != a) then some (b, st.2)
      else none
    | _, _ => none
  | _, _ => none

mutual
  /-- **The sort of a KORE right side, its variables given the sorts `vs`**, and whether it has a
  value at every list of values of those sorts; `none` where it is not of a sort so read. -/
  def nodTy (c : Semantics) (isN : String → Bool) (ar : String → Nat) (nA : String → List Srt)
      (nR : String → Option (Srt × Bool)) (vs : List (Kore.EVar × Srt)) : Kore.Pattern → Option (Srt × Bool)
    | .var (.evar x) => (nodLook vs x).map fun s => (s, true)
    | .dv S text => (nodDv c S text).map fun s => (s, true)
    | .app h ss ps =>
      if h.ident.name == "inj" then nodInjTy c ss (nodTys c isN ar nA nR vs ps)
      else if ss.isEmpty then (nodTys c isN ar nA nR vs ps).bind (nodHead c isN ar nA nR h.ident.name)
      else none
    | _ => none
    termination_by structural p => p
  /-- `nodTy` of each pattern, where each is of a sort. -/
  def nodTys (c : Semantics) (isN : String → Bool) (ar : String → Nat) (nA : String → List Srt)
      (nR : String → Option (Srt × Bool)) (vs : List (Kore.EVar × Srt)) : List Kore.Pattern → Option (List (Srt × Bool))
    | [] => some []
    | p :: ps => match nodTy c isN ar nA nR vs p, nodTys c isN ar nA nR vs ps with
      | some st, some sts => some (st :: sts)
      | _, _ => none
    termination_by structural ps => ps
end

/-- A reading `r` of the sort and totality `st`: read, a value of the sort or nothing, a value
where total. -/
def NodOK (c : Semantics) (r : Option (Option GroundTerm)) (st : Srt × Bool) : Prop :=
  ∃ o, r = some o ∧ (∀ v, o = some v → c.sortOf v = some st.1) ∧ (st.2 = true → o.isSome = true)

/-- A partial function `G n` of the sorts and totality `nA n`, `nR n`: at values of the argument
sorts, a value of its sort or nothing, a value where total. -/
def NodGOK (c : Semantics) (nA : String → List Srt) (nR : String → Option (Srt × Bool))
    (G : String → List GroundTerm → Option GroundTerm) (n : String) : Prop :=
  ∀ ws, c.sortsOf ws = some (nA n) → ∀ st, nR n = some st →
    (∀ v, G n ws = some v → c.sortOf v = some st.1) ∧ (st.2 = true → (G n ws).isSome = true)

theorem nod_sortsOf_cons {c : Semantics} {w : GroundTerm} {ws : List GroundTerm} {s : Srt} {ss : List Srt}
    (h1 : c.sortOf w = some s) (h2 : c.sortsOf ws = some ss) : c.sortsOf (w :: ws) = some (s :: ss) := by
  rw [Semantics.sortsOf, h1, h2]

theorem nod_sortsOf_cons_inv {c : Semantics} {w : GroundTerm} {ws : List GroundTerm} {ss : List Srt}
    (h : c.sortsOf (w :: ws) = some ss) :
    ∃ s ss', ss = s :: ss' ∧ c.sortOf w = some s ∧ c.sortsOf ws = some ss' := by
  rw [Semantics.sortsOf] at h
  cases h1 : c.sortOf w with
  | none => rw [h1] at h; cases h
  | some s =>
    cases h2 : c.sortsOf ws with
    | none => rw [h1, h2] at h; cases h
    | some ss' => rw [h1, h2] at h; cases h; exact ⟨s, ss', rfl, rfl, rfl⟩

/-- Readings of the sorts `sts`: some is nothing and not all are total, or all are values, of the
sorts. -/
theorem nod_args {c : Semantics} :
    ∀ {rs : List (Option (Option GroundTerm))} {sts : List (Srt × Bool)}, All2 (NodOK c) rs sts →
      (armEmpty rs = true ∧ sts.all (·.2) = false) ∨
        (armEmpty rs = false ∧ ∃ ws, armWs rs = some ws ∧ c.sortsOf ws = some (sts.map (·.1)))
  | [], [], .nil => .inr ⟨rfl, [], rfl, rfl⟩
  | _ :: rs, st :: sts, .cons ⟨o, rfl, hv, ht⟩ hs => by
    cases o with
    | none =>
      refine .inl ⟨rfl, ?_⟩
      cases hst : st.2
      · simp [hst]
      · have := ht hst; cases this
    | some v =>
      rcases nod_args hs with ⟨he, hall⟩ | ⟨he, ws, hws, hss⟩
      · exact .inl ⟨by simpa [armEmpty] using he, by simp [hall]⟩
      · refine .inr ⟨by simpa [armEmpty] using he, v :: ws, by simp [armWs, hws], ?_⟩
        exact nod_sortsOf_cons (hv v rfl) hss

theorem nod_sortsOf_length {c : Semantics} : ∀ {ws : List GroundTerm} {ss : List Srt},
    c.sortsOf ws = some ss → ws.length = ss.length
  | [], ss, h => by rw [Semantics.sortsOf] at h; cases h; rfl
  | _ :: _, _, h => by
    obtain ⟨_, _, rfl, -, h2⟩ := nod_sortsOf_cons_inv h
    simp [nod_sortsOf_length h2]

theorem nod_sortOf_ctor {c : Semantics} {f : Sym} {k : CtorSig} {ws : List GroundTerm}
    (hk : lookupSig c.ctorSigs f = some k) (hws : c.sortsOf ws = some k.args) :
    c.sortOf (.ctor f ws) = some k.result := by
  rw [Semantics.sortOf, hk]
  simp [hws]

theorem nod_sortOf_dv {c : Semantics} {s : Srt} {l : Lit} : c.sortOf (.dv s l) = if dvOK c.lib s l then some s else none := by
  rw [Semantics.sortOf]

theorem nodOK_none {c : Semantics} {s : Srt} {t : Bool} (ht : t = false) : NodOK c (some none) (s, t) := by
  subst ht; exact ⟨none, rfl, (fun _ h => nomatch h), (fun h => nomatch h)⟩

theorem nodOK_some {c : Semantics} {v : GroundTerm} {s : Srt} {t : Bool} (hs : c.sortOf v = some s) :
    NodOK c (some (some v)) (s, t) :=
  ⟨some v, rfl, (fun _ h => by cases h; exact hs), (fun _ => rfl)⟩

theorem nod_all2_nil {α β : Type} {R : α → β → Prop} {xs : List α} (h : All2 R xs ([] : List β)) : xs = [] := by
  cases h; rfl

section Sound

variable {c : Semantics} {isN : String → Bool} {ar : String → Nat} {nA : String → List Srt}
  {nR : String → Option (Srt × Bool)} {G : String → List GroundTerm → Option GroundTerm}
  {vs : List (Kore.EVar × Srt)} {σ : List (Kore.EVar × GroundTerm)}

/-- **`nodHead` gives `armHead`'s reading its sort.** -/
theorem nodHead_sound {h : String} (hG : isN h = true → NodGOK c nA nR G h) {ts : List (Srt × Bool)} {st : Srt × Bool}
    (ht : nodHead c isN ar nA nR h ts = some st) {ws : List GroundTerm} (hws : c.sortsOf ws = some (ts.map (·.1))) :
    NodOK c (armHead c isN ar G h ws) (st.1, st.2) := by
  unfold nodHead at ht
  unfold armHead
  by_cases hn : isN h = true
  · rw [if_pos_walk hn] at ht ⊢
    by_cases hc : (decide (ts.map (·.1) = nA h) && decide (ts.length = ar h)) = true
    · rw [if_pos_walk hc] at ht
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      have hl : ws.length = ar h := by rw [nod_sortsOf_length hws, List.length_map, hc.2]
      rw [if_pos_walk hl]
      obtain ⟨st', hst', rfl⟩ := Option.map_eq_some_iff.mp ht
      have hws' : c.sortsOf ws = some (nA h) := by rw [hws, hc.1]
      obtain ⟨hv, htot⟩ := hG hn ws hws' st' hst'
      cases hg : G h ws with
      | some v =>
        refine ⟨some v, ?_, (fun v' hv' => ?_), (fun _ => rfl)⟩
        · dsimp only; rw [hv v hg]; rfl
        · cases hv'; exact hv v hg
      | none =>
        refine ⟨none, rfl, (fun v' hv' => nomatch hv'), (fun htt => ?_)⟩
        simp only [Bool.and_eq_true] at htt
        have := htot htt.1; rw [hg] at this; cases this
    · rw [if_neg_arm hc] at ht; cases ht
  · rw [if_neg_arm hn] at ht ⊢
    cases hk : c.ctorSigs.find? (fun k => c.symName k.name == h) with
    | some k =>
      rw [hk] at ht; dsimp only at ht ⊢
      by_cases hc : (decide (lookupSig c.ctorSigs k.name = some k) && decide (ts.map (·.1) = k.args)) = true
      · rw [if_pos_walk hc] at ht
        cases ht
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        have hs := nod_sortOf_ctor hc.1 (by rw [hws, hc.2])
        rw [hs]
        exact nodOK_some hs
      · rw [if_neg_arm hc] at ht; cases ht
    | none =>
      rw [hk] at ht; dsimp only at ht ⊢
      cases hk' : hookSigs.find? (fun k => c.symName k.name == h) with
      | none => rw [hk'] at ht; cases ht
      | some k =>
        rw [hk'] at ht; dsimp only at ht ⊢
        by_cases hc : (decide (iteSort? h = none) && decide (lookupSig hookSigs k.name = some k) &&
            decide (ts.map (·.1) = k.args) && !silentKey k.name && isHook k.name && decide (k.name ≠ rmKeys)) = true
        · rw [if_pos_walk hc] at ht
          cases ht
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
          obtain ⟨⟨⟨⟨⟨hi, hl⟩, ha⟩, hsil⟩, hh⟩, hrm⟩ := hc
          have hws' : c.sortsOf ws = some k.args := by rw [hws, ha]
          rw [if_pos_walk (⟨hi, hws'⟩ : iteSort? h = none ∧ c.sortsOf ws = some k.args)]
          obtain ⟨o, ho⟩ := Faithful.hook_some hh ws
          rw [ho]
          cases o with
          | none =>
            dsimp only
            rw [if_pos_walk (silent_of_not_silentKey hsil ws)]
            refine nodOK_none ?_
            cases hte : ts.isEmpty
            · rfl
            · have hts : ts = [] := List.isEmpty_iff.mp hte
              subst hts
              have hw0 : ws = [] := List.eq_nil_of_length_eq_zero (by rw [nod_sortsOf_length hws]; rfl)
              subst hw0
              simp [ho]
          | some v =>
            dsimp only
            have hs := hook_sorted (c := c) (fun he => absurd he hrm) hl hws' ho
            rw [hs]
            exact nodOK_some hs
        · rw [if_neg_arm hc] at ht; cases ht

theorem nodDv_sound {S : Kore.KSort} {text : String} {s : Srt} (h : nodDv c S text = some s) :
    ∃ v, armDv c S text = some v ∧ c.sortOf v = some s := by
  unfold nodDv at h
  unfold armDv
  cases ha : armSrt c S with
  | none => rw [ha] at h; cases h
  | some a =>
    dsimp only at h ⊢
    rw [ha] at h; dsimp only at h
    cases hl : Parse.lit? a text with
    | none => rw [hl] at h; cases h
    | some l =>
      rw [hl] at h; dsimp only at h ⊢
      by_cases hc : (decide ((GroundTerm.dv a l).kore c = .dv S text) && dvOK c.lib a l) = true
      · rw [if_pos_walk hc] at h
        cases h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        have hs : c.sortOf (.dv s l) = some s := by rw [nod_sortOf_dv, if_pos_walk hc.2]
        have hc' : (decide ((GroundTerm.dv s l).kore c = .dv S text) && (c.sortOf (.dv s l)).isSome) = true := by
          simp only [hs, Option.isSome_some, Bool.and_true, decide_eq_true_eq]; exact hc.1
        rw [if_pos_walk hc']
        exact ⟨_, rfl, hs⟩
      · rw [if_neg_arm hc] at h; cases h

/-- The inj of a reading of a sort with no subsort. -/
theorem nodInj_sound {A B : Kore.KSort} {a b : Srt} (hA : armSrt c A = some a) (hB : armSrt c B = some b)
    {r : Option (Option GroundTerm)} {st : Srt × Bool} (hr : NodOK c r st) (hsa : st.1 = a)
    (hab : c.subsorts.contains (a, b) = true) (hno : c.subsorts.all (·.2 != a) = true) :
    NodOK c (armInj c [A, B] [r]) (b, st.2) := by
  obtain ⟨o, rfl, hv, ht⟩ := hr
  cases o with
  | none =>
    simp only [armInj, hA, hB]
    exact ⟨none, rfl, (fun v h => nomatch h), (fun h => by have := ht h; cases this)⟩
  | some w =>
    have hw := hv w rfl
    rw [hsa] at hw
    have hni : w.isInj = false := by
      cases w with
      | inj a' b' u =>
        obtain ⟨hmem, -, -, rfl⟩ := sortOf_inj.mp hw
        have := List.all_eq_true.mp hno _ hmem
        simp at this
      | _ => rfl
    have hs : c.sortOf (.inj a b w) = some b := sortOf_inj.mpr ⟨List.contains_iff_mem.mp hab, hni, hw, rfl⟩
    simp only [armInj, hA, hB, hs, Option.isSome_some, ↓reduceIte]
    exact nodOK_some hs

theorem nodInjTy_sound {ss : List Kore.KSort} {tys : Option (List (Srt × Bool))}
    {rs : List (Option (Option GroundTerm))} (hrs : ∀ sts, tys = some sts → All2 (NodOK c) rs sts)
    {st : Srt × Bool} (h : nodInjTy c ss tys = some st) : NodOK c (armInj c ss rs) st := by
  unfold nodInjTy at h
  split at h
  · rename_i sA sB st0
    have hall := hrs [st0] rfl
    match rs, hall with
    | [_], .cons h1 .nil =>
      cases hA : armSrt c sA with
      | none => rw [hA] at h; cases h
      | some a =>
        cases hB : armSrt c sB with
        | none => rw [hA, hB] at h; cases h
        | some b =>
          rw [hA, hB] at h; dsimp only at h
          by_cases hc : (decide (st0.1 = a) && c.subsorts.contains (a, b) && c.subsorts.all (·.2 != a)) = true
          · rw [if_pos_walk hc] at h
            cases h
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
            exact nodInj_sound hA hB h1 hc.1.1 hc.1.2 hc.2
          · rw [if_neg_arm hc] at h; cases h
  · cases h

end Sound

mutual
  /-- **What the sorts give**: where every name the right side applies is of its sorts, the arm
  reads the right side at values of the variables' sorts as a value of its sort, or nothing, and
  as a value where total. -/
  theorem nodTy_sound {c : Semantics} {isN : String → Bool} {ar : String → Nat} {nA : String → List Srt}
      {nR : String → Option (Srt × Bool)} {G : String → List GroundTerm → Option GroundTerm}
      {vs : List (Kore.EVar × Srt)} {σ : List (Kore.EVar × GroundTerm)}
      (hσ : ∀ x s, nodLook vs x = some s → ∃ w, armLookup σ x = some w ∧ c.sortOf w = some s) :
      ∀ p : Kore.Pattern, (∀ n ∈ armHeads p, isN n = true → NodGOK c nA nR G n) → ∀ st,
        nodTy c isN ar nA nR vs p = some st → NodOK c (armVal c isN ar G σ p) st
    | .var (.evar x), _, st, h => by
      rw [nodTy] at h
      obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨w, hw, hws⟩ := hσ x s hs
      rw [armVal, hw]
      exact nodOK_some hws
    | .dv S text, _, st, h => by
      rw [nodTy] at h
      obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨v, hv, hvs⟩ := nodDv_sound hs
      show NodOK c ((armDv c S text).map some) (s, true)
      rw [hv]
      exact nodOK_some hvs
    | .app h ss ps, hG, st, ht => by
      have hGs : ∀ n ∈ armHeadsL ps, isN n = true → NodGOK c nA nR G n :=
        fun n hn => hG n (by rw [armHeads]; exact List.mem_cons_of_mem _ hn)
      rw [nodTy] at ht
      rw [armVal]
      by_cases hi : (h.ident.name == "inj") = true
      · rw [if_pos_walk hi] at ht ⊢
        rw [armVals_eq]
        exact nodInjTy_sound (fun sts h => nodTys_sound hσ ps hGs sts h) ht
      · rw [if_neg_arm hi] at ht ⊢
        by_cases hs : ss.isEmpty = true
        · rw [if_pos_walk hs] at ht ⊢
          obtain ⟨sts, hts, hh⟩ := Option.bind_eq_some_iff.mp ht
          have hall := nodTys_sound hσ ps hGs sts hts
          rw [← armVals_eq] at *
          unfold armApp
          rcases nod_args hall with ⟨he, htot⟩ | ⟨he, ws, hws, hss⟩
          · rw [if_pos_walk he]
            refine ⟨none, rfl, (fun v hv => nomatch hv), (fun h2 => ?_)⟩
            exfalso
            unfold nodHead at hh
            split at hh
            · split at hh
              · obtain ⟨st', -, rfl⟩ := Option.map_eq_some_iff.mp hh
                simp only [Bool.and_eq_true] at h2
                rw [htot] at h2; exact absurd h2.2 (by decide)
              · cases hh
            · split at hh
              · split at hh
                · cases hh; rw [htot] at h2; cases h2
                · cases hh
              · split at hh
                · split at hh
                  · cases hh
                    cases sts with
                    | nil =>
                      have h0 := nod_all2_nil hall
                      rw [h0] at he; simp [armEmpty] at he
                    | cons _ _ => simp at h2
                  · cases hh
                · cases hh
          · rw [if_neg_arm (by rw [he]; decide), hws]
            dsimp only
            have hG' : isN h.ident.name = true → NodGOK c nA nR G h.ident.name :=
              hG h.ident.name (by rw [armHeads]; exact List.mem_cons_self ..)
            exact nodHead_sound hG' hh hss
        · rw [if_neg_arm hs] at ht; cases ht
    | .var (.svar _), _, _, h => by simp [nodTy] at h
    | .string _, _, _, h => by simp [nodTy] at h
    | .top _, _, _, h => by simp [nodTy] at h
    | .bottom _, _, _, h => by simp [nodTy] at h
    | .not _ _, _, _, h => by simp [nodTy] at h
    | .and _ _, _, _, h => by simp [nodTy] at h
    | .or _ _, _, _, h => by simp [nodTy] at h
    | .implies _ _ _, _, _, h => by simp [nodTy] at h
    | .iff _ _ _, _, _, h => by simp [nodTy] at h
    | .exist _ _ _, _, _, h => by simp [nodTy] at h
    | .forall _ _ _, _, _, h => by simp [nodTy] at h
    | .mu _ _, _, _, h => by simp [nodTy] at h
    | .nu _ _, _, _, h => by simp [nodTy] at h
    | .ceil _ _ _, _, _, h => by simp [nodTy] at h
    | .floor _ _ _, _, _, h => by simp [nodTy] at h
    | .equals _ _ _ _, _, _, h => by simp [nodTy] at h
    | .in _ _ _ _, _, _, h => by simp [nodTy] at h
    | .next _ _, _, _, h => by simp [nodTy] at h
    | .rewrites _ _ _, _, _, h => by simp [nodTy] at h
    | .leftAssoc _ _ _, _, _, h => by simp [nodTy] at h
    | .rightAssoc _ _ _, _, _, h => by simp [nodTy] at h
    termination_by structural p => p
  theorem nodTys_sound {c : Semantics} {isN : String → Bool} {ar : String → Nat} {nA : String → List Srt}
      {nR : String → Option (Srt × Bool)} {G : String → List GroundTerm → Option GroundTerm}
      {vs : List (Kore.EVar × Srt)} {σ : List (Kore.EVar × GroundTerm)}
      (hσ : ∀ x s, nodLook vs x = some s → ∃ w, armLookup σ x = some w ∧ c.sortOf w = some s) :
      ∀ ps : List Kore.Pattern, (∀ n ∈ armHeadsL ps, isN n = true → NodGOK c nA nR G n) → ∀ sts,
        nodTys c isN ar nA nR vs ps = some sts → All2 (NodOK c) (ps.map (armVal c isN ar G σ)) sts
    | [], _, sts, h => by rw [nodTys] at h; cases h; exact .nil
    | p :: ps, hG, sts, h => by
      rw [nodTys] at h
      cases h1 : nodTy c isN ar nA nR vs p with
      | none => rw [h1] at h; cases h
      | some st =>
        cases h2 : nodTys c isN ar nA nR vs ps with
        | none => rw [h1, h2] at h; cases h
        | some sts' =>
          rw [h1, h2] at h; cases h
          exact .cons (nodTy_sound hσ p (fun n hn => hG n (by rw [armHeadsL]; exact List.mem_append_left _ hn)) st h1)
            (nodTys_sound hσ ps (fun n hn => hG n (by rw [armHeadsL]; exact List.mem_append_right _ hn)) sts' h2)
    termination_by structural ps => ps
end

/-! ## Facts of lists of values -/

theorem nod_sortsOf_get {c : Semantics} : ∀ {ts : List GroundTerm} {ss : List Srt},
    c.sortsOf ts = some ss → ∀ (i : Nat) (v : GroundTerm), ts[i]? = some v → c.sortOf v = ss[i]?
  | [], _, _, _, _, hv => by simp at hv
  | t :: ts, ss, h, i, v, hv => by
    obtain ⟨s, ss', rfl, h1, h2⟩ := nod_sortsOf_cons_inv h
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hv; subst hv; simpa using h1
    | succ i => simpa using nod_sortsOf_get h2 i v (by simpa using hv)

theorem nod_ctor_inv {c : Semantics} {f : Sym} {ts : List GroundTerm} {s : Srt} {k : CtorSig}
    (hk : lookupSig c.ctorSigs f = some k) (h : c.sortOf (.ctor f ts) = some s) :
    c.sortsOf ts = some k.args ∧ s = k.result := by
  rw [Semantics.sortOf, hk] at h
  dsimp only at h
  split at h
  · rename_i hb; cases h; exact ⟨beq_iff_eq.mp hb, rfl⟩
  · cases h

/-- Values of the variables' sorts: one for each variable, of its sort. -/
def NodVals (c : Semantics) (xs : List Kore.EVar) (ws : List GroundTerm) : Prop :=
  All2 (fun (x : Kore.EVar) w => ∃ s, armSrt c x.sort = some s ∧ c.sortOf w = some s) xs ws

theorem nodVals_sorts {c : Semantics} : ∀ {xs : List Kore.EVar} {ws : List GroundTerm}, NodVals c xs ws →
    c.sortsOf ws = some (xs.filterMap fun x => armSrt c x.sort) ∧ ws.length = xs.length
  | [], [], .nil => ⟨rfl, rfl⟩
  | x :: _, w :: _, .cons ⟨s, hx, hw⟩ hs => by
    obtain ⟨h1, h2⟩ := nodVals_sorts hs
    refine ⟨?_, by simp [h2]⟩
    rw [List.filterMap_cons, hx]
    exact nod_sortsOf_cons hw h1

theorem nod_zip_look {c : Semantics} : ∀ {xs : List Kore.EVar} {ss : List Srt} {ws : List GroundTerm},
    xs.length = ss.length → c.sortsOf ws = some ss →
    ∀ x s, nodLook (xs.zip ss) x = some s → ∃ w, armLookup (armZip xs ws) x = some w ∧ c.sortOf w = some s
  | [], _, _, _, _, x, s, h => by simp [nodLook] at h
  | y :: xs, [], _, hl, _, _, _, _ => by cases hl
  | y :: xs, t :: ss, ws, hl, hws, x, s, h => by
    cases ws with
    | nil => rw [Semantics.sortsOf] at hws; cases hws
    | cons w ws =>
      obtain ⟨t', ss', he, h1, h2⟩ := nod_sortsOf_cons_inv hws
      cases he
      by_cases hxy : y = x
      · subst hxy
        simp only [nodLook, List.zip_cons_cons, List.find?_cons, decide_true, Option.map_some,
          Option.some.injEq] at h
        subst h
        exact ⟨w, by simp [armZip, armLookup], h1⟩
      · have h' : nodLook (xs.zip ss) x = some s := by
          simpa [nodLook, List.zip_cons_cons, List.find?_cons, hxy] using h
        obtain ⟨w', hw', hs'⟩ := nod_zip_look (by simpa using hl) h2 x s h'
        refine ⟨w', ?_, hs'⟩
        simp only [armZip, List.zip_cons_cons]
        rw [armLookup_cons_ne (Ne.symm hxy)]
        exact hw'

theorem nod_armVarsL_vars : ∀ xs : List Kore.EVar, armVarsL (xs.map fun x => Kore.Pattern.var (.evar x)) = xs
  | [] => by rw [List.map_nil, armVarsL]
  | x :: xs => by rw [List.map_cons, armVarsL, nod_armVarsL_vars xs, armVars]; rfl

/-- `armLookup` at a distinct variable list's `i`-th variable is the `i`-th value. -/
theorem nod_lookup_idx : ∀ {xs : List Kore.EVar} {ws : List GroundTerm}, Parse.evarsDistinct xs = true →
    ws.length = xs.length → ∀ (i : Nat) (x : Kore.EVar), xs[i]? = some x → armLookup (armZip xs ws) x = ws[i]?
  | [], _, _, _, _, _, hx => by simp at hx
  | y :: xs, [], _, hl, _, _, _ => by cases hl
  | y :: xs, w :: ws, hd, hl, i, x, hx => by
    simp only [Parse.evarsDistinct, Bool.and_eq_true, Bool.not_eq_true'] at hd
    simp only [armZip, List.zip_cons_cons]
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      rw [armLookup_cons_self]; rfl
    | succ i =>
      simp only [List.getElem?_cons_succ] at hx ⊢
      have hne : x ≠ y := by
        rintro rfl
        have : Parse.evarIn xs x = true :=
          List.any_eq_true.mpr ⟨x, List.mem_of_getElem? hx, decide_eq_true rfl⟩
        rw [hd.1] at this; cases this
      rw [armLookup_cons_ne hne]
      exact nod_lookup_idx hd.2 (by simpa using hl) i x hx

/-! ## The names' sorts -/

/-- A name's argument sorts: an initializer's, its equation's variables' sorts; the getter's, the
configuration's sort; a projection's, `K`. -/
def nodA (c : Semantics) (eqs : List Parse.RawEqn) (order : List String) (n : String) : List Srt :=
  match armLook order eqs n with
  | some e => match Parse.distinctEVars? e.pats with
    | some xs => xs.filterMap fun x => armSrt c x.sort
    | none => []
  | none => if n == Parse.getterName then [topCellSort] else [Srt.k]

/-- The sort and totality of a name `armBase` gives a meaning: the getter, the argument sort of
the top cell's constructor its equation's pattern reads (not total); `project:K`, `K` (total);
`project:KItem`, `KItem`; `project:X`, the sort `X`. -/
def nodBaseR (c : Semantics) (eqs : List Parse.RawEqn) (n : String) : Option (Srt × Bool) :=
  if n == Parse.getterName then
    match eqs.find? (·.fn == Parse.getterName) with
    | some e => match e.pats with
      | [.app _ _ args] => ((lookupSig c.ctorSigs topLabel).bind fun k => k.args[args.length - 1]?).map fun s => (s, false)
      | _ => none
    | none => none
  else match KoreAML.Parse.dropPrefix? "Lblproject'Coln'" n with
    | some X =>
      if X == "K" then some (Srt.k, true)
      else if X == "KItem" then some (Srt.kitem, false)
      else (armSrt c (KoreAML.srt X)).map fun s => (s, false)
    | none => none

/-- The names' sorts, read along `order` (`k` the depth): a name of `order`, its right side's;
another, `nodBaseR`. -/
def nodRAt (c : Semantics) (isN : String → Bool) (ar : String → Nat) (nA : String → List Srt)
    (eqs : List Parse.RawEqn) (order : List String) : Nat → String → Option (Srt × Bool)
  | 0 => nodBaseR c eqs
  | k + 1 => fun n => match armLook order eqs n with
    | some e => match Parse.distinctEVars? e.pats with
      | some xs => nodTy c isN ar nA (nodRAt c isN ar nA eqs order k) (xs.zip (nA n)) e.rhs
      | none => none
    | none => nodBaseR c eqs n

/-- The names' sorts at the depth of `order`. -/
def nodR (c : Semantics) (names : List String) (eqs : List Parse.RawEqn) (order : List String) :
    String → Option (Srt × Bool) :=
  nodRAt c names.contains (armAr eqs) (nodA c eqs order) eqs order order.length

/-- **The check of the names of `order`**: where `nodR` gives a name a sort, its equation's
variables are each of a sort and its right side is of that sort. -/
def nodOrderB (c : Semantics) (names : List String) (eqs : List Parse.RawEqn) (order : List String) : Bool :=
  order.all fun n => match armLook order eqs n with
    | some e => match Parse.distinctEVars? e.pats with
      | some xs => match nodR c names eqs order n with
        | some _ => decide ((xs.filterMap fun x => armSrt c x.sort).length = xs.length) &&
          decide (nodTy c names.contains (armAr eqs) (nodA c eqs order) (nodR c names eqs order)
            (xs.zip (nodA c eqs order n)) e.rhs = nodR c names eqs order n)
        | none => true
      | none => true
    | none => true

/-- The registry's symbols the projections' and the getter's values are built with, as the
semantics names and sorts them. -/
def nodFixedB (c : Semantics) : Bool :=
  decide (c.symName kseq = "kseq") && decide (c.symName dotk = "dotk") && decide (c.sortName Srt.kitem = "KItem") &&
  decide (lookupSig c.ctorSigs kseq = some ⟨kseq, [Srt.kitem, Srt.k], Srt.k⟩) &&
  decide (lookupSig c.ctorSigs dotk = some ⟨dotk, [], Srt.k⟩)

theorem nodRAt_none {c : Semantics} {isN : String → Bool} {ar : String → Nat} {nA : String → List Srt}
    {eqs : List Parse.RawEqn} {order : List String} {n : String} (hn : armLook order eqs n = none) :
    ∀ k, nodRAt c isN ar nA eqs order k n = nodBaseR c eqs n
  | 0 => rfl
  | k + 1 => by simp only [nodRAt, hn]

theorem nod_unique_ws {c : Semantics} {ws : List GroundTerm} {s : Srt} (h : c.sortsOf ws = some [s]) :
    ∃ w, ws = [w] ∧ c.sortOf w = some s := by
  cases ws with
  | nil => rw [Semantics.sortsOf] at h; cases h
  | cons w ws =>
    obtain ⟨s', ss', he, h1, h2⟩ := nod_sortsOf_cons_inv h
    cases he
    cases ws with
    | nil => exact ⟨w, rfl, h1⟩
    | cons w' ws' =>
      obtain ⟨_, _, he', -, -⟩ := nod_sortsOf_cons_inv h2
      cases he'

/-- **`armBase` is of the sorts `nodBaseR` gives**: the getter's value the top cell's argument,
of its argument sort; `project:K`'s the value, `project:KItem`'s the item, of `KItem`;
`project:X`'s (`projFn`) of the sort `X`. -/
theorem nod_base_ok {c : Semantics} {eqs : List Parse.RawEqn} {order : List String}
    (hk : lookupSig c.ctorSigs kseq = some ⟨kseq, [Srt.kitem, Srt.k], Srt.k⟩) {n : String}
    (hn : armLook order eqs n = none) : NodGOK c (nodA c eqs order) (nodBaseR c eqs) (armBase c eqs) n := by
  intro ws hws st hst
  by_cases hg : (n == Parse.getterName) = true
  · have hA : nodA c eqs order n = [topCellSort] := by simp only [nodA, hn, hg, ↓reduceIte]
    rw [hA] at hws
    obtain ⟨w, rfl, hw⟩ := nod_unique_ws hws
    have hgn : n = Parse.getterName := beq_iff_eq.mp hg
    subst hgn
    unfold nodBaseR at hst
    rw [if_pos_walk hg] at hst
    unfold armBase
    dsimp only
    rw [if_pos_walk hg]
    cases hf : eqs.find? (·.fn == Parse.getterName) with
    | none => rw [hf] at hst; cases hst
    | some e =>
      rw [hf] at hst
      dsimp only at hst ⊢
      split at hst
      · rename_i h' ss args hpats
        rw [hpats]
        dsimp only
        obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp hst
        obtain ⟨k, hk', hks⟩ := Option.bind_eq_some_iff.mp hs
        refine ⟨fun v hv => ?_, fun h => by cases h⟩
        cases w with
        | ctor f ts =>
          simp only [argFn] at hv
          split at hv
          · rename_i hf'
            subst hf'
            have := (nod_ctor_inv hk' hw).1
            rw [nod_sortsOf_get this _ v hv, hks]
          · cases hv
        | _ => simp [argFn] at hv
      · cases hst
  · have hA : nodA c eqs order n = [Srt.k] := by simp only [nodA, hn, hg, ↓reduceIte, Bool.false_eq_true]
    rw [hA] at hws
    obtain ⟨w, rfl, hw⟩ := nod_unique_ws hws
    unfold nodBaseR at hst
    rw [if_neg_arm hg] at hst
    unfold armBase
    dsimp only
    rw [if_neg_arm hg]
    cases hX : KoreAML.Parse.dropPrefix? "Lblproject'Coln'" n with
    | none => rw [hX] at hst; cases hst
    | some X =>
      rw [hX] at hst; dsimp only at hst ⊢
      by_cases hK : (X == "K") = true
      · rw [if_pos_walk hK] at hst ⊢
        cases hst
        exact ⟨fun v hv => by cases hv; exact hw, fun _ => rfl⟩
      · rw [if_neg_arm hK] at hst ⊢
        by_cases hI : (X == "KItem") = true
        · rw [if_pos_walk hI] at hst ⊢
          cases hst
          refine ⟨fun v hv => ?_, fun h => by cases h⟩
          unfold itemFn at hv
          split at hv
          · rename_i f i f'
            split at hv
            · rename_i hc
              obtain ⟨rfl, rfl⟩ := hc
              cases hv
              have := (nod_ctor_inv hk hw).1
              exact nod_sortsOf_get this 0 v rfl
            · cases hv
          · cases hv
        · rw [if_neg_arm hI] at hst ⊢
          obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hst
          rw [hx]
          refine ⟨fun v hv => ?_, fun h => by cases h⟩
          unfold projFn at hv
          split at hv
          · rename_i f a b u f'
            split at hv
            · rename_i hc
              obtain ⟨rfl, rfl, rfl⟩ := hc
              have hss := (nod_ctor_inv hk hw).1
              have hu := nod_sortsOf_get hss 0 _ rfl
              simp only [List.getElem?_cons_zero] at hu
              obtain ⟨hab, hni, hua, -⟩ := sortOf_inj.mp hu
              change (if a = x then some u else if c.subsorts.contains (a, x) = true then some (GroundTerm.inj a x u)
                else none) = some v at hv
              split at hv
              · rename_i hax; cases hv; rw [hua, hax]
              · split at hv
                · rename_i hsub
                  cases hv
                  exact sortOf_inj.mpr ⟨List.contains_iff_mem.mp hsub, hni, hua, rfl⟩
                · cases hv
            · cases hv
          · cases hv

theorem nod_armG_nodist {c : Semantics} {isN : String → Bool} {ar : String → Nat} {order : List String}
    {eqs : List Parse.RawEqn} {base : String → List GroundTerm → Option GroundTerm} {n : String} {e : Parse.RawEqn}
    (he : armLook order eqs n = some e) (hx : Parse.distinctEVars? e.pats = none) (ws : List GroundTerm) :
    armG c isN ar order eqs base order.length n ws = none := by
  have hn := armLook_order order eqs he
  obtain ⟨K, hK⟩ : ∃ K, order.length = K + 1 :=
    ⟨order.length - 1, by have := List.idxOf_lt_length_of_mem (List.contains_iff_mem.mp hn); omega⟩
  rw [hK]
  simp only [armG, he, hx]

theorem nodR_nodist {c : Semantics} {names : List String} {eqs : List Parse.RawEqn} {order : List String}
    {n : String} {e : Parse.RawEqn} (he : armLook order eqs n = some e) (hx : Parse.distinctEVars? e.pats = none) :
    nodR c names eqs order n = none := by
  have hn := armLook_order order eqs he
  obtain ⟨K, hK⟩ : ∃ K, order.length = K + 1 :=
    ⟨order.length - 1, by have := List.idxOf_lt_length_of_mem (List.contains_iff_mem.mp hn); omega⟩
  unfold nodR; rw [hK]
  simp only [nodRAt, he, hx]

/-- **The names' `G` read from the text is of the names' sorts**, for every name. -/
theorem nod_G_ok {c : Semantics} {eqs : List Parse.RawEqn} {names order : List String}
    (hk : lookupSig c.ctorSigs kseq = some ⟨kseq, [Srt.kitem, Srt.k], Srt.k⟩) (hR : armRankB order eqs = true)
    (hchk : nodOrderB c names eqs order = true) :
    ∀ n, NodGOK c (nodA c eqs order) (nodR c names eqs order) (armGOf c eqs names order (armBase c eqs)) n := by
  have hnone : ∀ n, armLook order eqs n = none →
      NodGOK c (nodA c eqs order) (nodR c names eqs order) (armGOf c eqs names order (armBase c eqs)) n := by
    intro n hn ws hws st hst
    rw [nodR, nodRAt_none hn] at hst
    rw [armGOf, armG_base c _ _ order eqs _ hn]
    exact nod_base_ok hk hn ws hws st hst
  intro n
  generalize hm : order.idxOf n = m
  induction m using Nat.strongRecOn generalizing n with
  | _ m ih =>
    cases hl : armLook order eqs n with
    | none => exact hnone n hl
    | some e =>
      have hn := armLook_order order eqs hl
      cases hx : Parse.distinctEVars? e.pats with
      | none =>
        intro ws _ st hst
        rw [nodR_nodist hl hx] at hst; cases hst
      | some xs =>
        intro ws hws st hst
        have hc := List.all_eq_true.mp hchk n (List.contains_iff_mem.mp hn)
        rw [hl] at hc; dsimp only at hc; rw [hx] at hc; dsimp only at hc; rw [hst] at hc; dsimp only at hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨hlen, hty⟩ := hc
        have hfix := armG_fix c names.contains (armAr eqs) order eqs (armBase c eqs) hR hl hx ws
        have hA : nodA c eqs order n = xs.filterMap fun x => armSrt c x.sort := by simp only [nodA, hl, hx]
        have hσ := nod_zip_look (c := c) (xs := xs) (ws := ws) (by rw [hA, hlen]) hws
        have hG : ∀ h ∈ armHeads e.rhs, names.contains h = true →
            NodGOK c (nodA c eqs order) (nodR c names eqs order) (armGOf c eqs names order (armBase c eqs)) h := by
          intro h hh _
          cases hl' : armLook order eqs h with
          | none => exact hnone h hl'
          | some _ =>
            exact ih _ (by rw [← hm]; exact armRank_of order eqs hR hl hh (armLook_order order eqs hl')) h rfl
        obtain ⟨o, ho, hv, ht⟩ := nodTy_sound hσ e.rhs hG st (by rw [hty])
        have hGn : armGOf c eqs names order (armBase c eqs) n ws = o := by
          rw [armGOf, hfix, ho]; rfl
        rw [hGn]
        exact ⟨hv, ht⟩

/-! ## The model, and an injection over an injection -/

/-- **An injection over a value of a subsort denotes its normalised injection** (`injNormal`), by
the theory's injection coherence (`den_inj_gs`, `den_injNormal_gs`), the value itself an
injection or not. -/
theorem nod_injN {c : Semantics} {N : String → Prop} {ar : String → Nat} {G : String → List GroundTerm → Option GroundTerm}
    {I : Interpretation KoreAML.Sym Elem} (hM : InitModel c N ar G I) (hc : c.coreOK = true) {a b : Srt}
    {ψ : KoreAML.P} {w : GroundTerm} (h : DenV c I ψ w) (hw : c.sortOf w = some a) (hab : (a, b) ∈ c.subsorts) :
    DenV c I (KoreAML.appList (KoreAML.sym (.symbol "inj"))
      [KoreAML.Cons.sortP (c.sortName a), KoreAML.Cons.sortP (c.sortName b), ψ]) (injNormal a b w) := by
  haveI : OvlOK c := ovlOK_of_core hc
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hM.sat φ (Or.inl (Or.inl hφ))
  have htr := CE.injValue_subsorts_trans hc
  have hs := sortOf_injNormal htr hab hw
  refine ⟨⟨b, hs⟩, fun ρ m => ?_⟩
  rw [inj_den a b (fun m => (h.2 ρ m).trans (hM.vals w a hw ρ m).symm) m]
  rw [Faithful.den_inj_gs hI hw ρ m, ← Faithful.den_injNormal_gs hI htr hab hw ρ m]
  exact hM.vals _ b hs ρ m

/-! ## The equations at every list of values -/

/-- **The text's equation `e` holds at every list of values of its variables' sorts**: `xs` the
element variables of its patterns, for values `ws` of their sorts, one for each,
`f(ps[ws/xs]) = rhs[ws/xs]`, both sides translated with the variables replaced by the values' KORE
terms. -/
def NodEqn (c : Semantics) (I : Interpretation KoreAML.Sym Elem) (e : Parse.RawEqn) : Prop :=
  ∀ ws, NodVals c (armVarsL e.pats) ws →
    I ⊧ᴵ (KoreAML.den (armSubst c (armZip (armVarsL e.pats) ws) (armLhs e)) ≡
      KoreAML.den (armSubst c (armZip (armVarsL e.pats) ws) e.rhs))

/-- **The `functional` axiom of the constant `L` at the sort `S` holds**: `∃y:S. y = L()`. -/
def NodFun (c : Semantics) (I : Interpretation KoreAML.Sym Elem) (L : String) (S : Kore.KSort) : Prop :=
  ∀ s, armSrt c S = some s → ∀ y : EVar,
    I ⊧ᴵ KoreAML.sExists y (KoreAML.Cons.sortP (c.sortName s)) (.evar y ≡ KoreAML.appList (symP L) [])

theorem nodEqn_congr {c : Semantics} {I : Interpretation KoreAML.Sym Elem} {e e' : Parse.RawEqn}
    (hf : e'.fn = e.fn) (hp : e'.pats = e.pats) (hr : e'.rhs = e.rhs) (h : NodEqn c I e') : NodEqn c I e := by
  unfold NodEqn armLhs at *
  rw [← hf, ← hp, ← hr]
  exact h

theorem nodVals_sorted {c : Semantics} : ∀ {xs : List Kore.EVar} {ws : List GroundTerm}, NodVals c xs ws →
    ∀ w ∈ ws, ∃ s, c.sortOf w = some s
  | [], [], .nil, _, hw => by cases hw
  | _ :: _, _ :: _, .cons ⟨s, _, hs⟩ hr, w, hw => by
    rcases List.mem_cons.mp hw with rfl | hw
    · exact ⟨s, hs⟩
    · exact nodVals_sorted hr w hw

/-- `project:X`'s equation: `project:X(kseq(inj{X,KItem}(V), dotk)) = V`, `V` of `X`, a subsort of `KItem`. -/
def nodItemP (S : Kore.KSort) (p : Kore.Pattern) : Kore.Pattern :=
  .app ⟨⟨"kseq"⟩⟩ [] [.app ⟨⟨"inj"⟩⟩ [S, KoreAML.srt "KItem"] [p], .app ⟨⟨"dotk"⟩⟩ [] []]

def nodProjX (c : Semantics) (e : Parse.RawEqn) : Option (Kore.EVar × Srt) :=
  match KoreAML.Parse.dropPrefix? "Lblproject'Coln'" e.fn, e.rhs with
  | some X, .var (.evar v) =>
    if X != "K" && X != "KItem" && decide (v.sort = KoreAML.srt X) &&
        decide (e.pats = [nodItemP v.sort (.var (.evar v))]) then
      (armSrt c v.sort).bind fun x => if c.subsorts.contains (x, Srt.kitem) then some (v, x) else none
    else none
  | _, _ => none

/-- `project:K`'s equation: `project:K(V) = V`, `V` of `K`. -/
def nodProjKB (c : Semantics) (e : Parse.RawEqn) : Bool :=
  match e.rhs with
  | .var (.evar v) => e.fn == "Lblproject'Coln'K" && decide (e.pats = [.var (.evar v)]) &&
      decide (armSrt c v.sort = some Srt.k)
  | _ => false

/-- `project:KItem`'s equation: `project:KItem(kseq(V, dotk)) = V`, `V` of `KItem`. -/
def nodProjKItemB (c : Semantics) (e : Parse.RawEqn) : Bool :=
  match e.rhs with
  | .var (.evar v) => e.fn == "Lblproject'Coln'KItem" &&
      decide (e.pats = [.app ⟨⟨"kseq"⟩⟩ [] [.var (.evar v), .app ⟨⟨"dotk"⟩⟩ [] []]]) &&
      decide (armSrt c v.sort = some Srt.kitem)
  | _ => false

/-- The getter's equation: `getGeneratedCounterCell(<generatedTop>(V₁, …, Vₙ)) = Vₙ`, the `Vᵢ`
distinct, of the top cell's argument sorts. -/
def nodGetterB (c : Semantics) (e : Parse.RawEqn) : Bool :=
  e.fn == Parse.getterName &&
  match e.pats, e.rhs with
  | [.app h ss ps], .var (.evar x) =>
    ss.isEmpty && h.ident.name == c.symName topLabel &&
    match Parse.distinctEVars? ps with
    | some xs => decide (xs.getLast? = some x) &&
        decide ((xs.filterMap fun y => armSrt c y.sort).length = xs.length) &&
        decide ((lookupSig c.ctorSigs topLabel).map (·.args) = some (xs.filterMap fun y => armSrt c y.sort))
    | none => false
  | _, _ => false

/-- The constant of a `functional` axiom `∃y:S. y = L()`, and its sort. -/
def nodFunctional? (a : Kore.Axiom) : Option (String × Kore.KSort) :=
  match a.pattern with
  | .exist _ v (.equals _ _ (.var (.evar w)) (.app f [] [])) =>
    if decide (v = w) then some (f.ident.name, v.sort) else none
  | _ => none

section Eqns

variable {c : Semantics} {eqs : List Parse.RawEqn} {names order : List String}
  {I : Interpretation KoreAML.Sym Elem}
  (hM : InitModel c (fun n => names.contains n = true) (armAr eqs) (armGOf c eqs names order (armBase c eqs)) I)
include hM

/-- **An initializer's equation the arm takes holds at every list of values of its variables'
sorts.** -/
theorem nod_init_eqn (hk : lookupSig c.ctorSigs kseq = some ⟨kseq, [Srt.kitem, Srt.k], Srt.k⟩)
    (hR : armRankB order eqs = true) (hord : order.all names.contains = true) (hchk : nodOrderB c names eqs order = true)
    {Nm : Parse.Names} {msrc : String} {x : Cell} {e : Parse.RawEqn} (he : e ∈ eqs)
    (hok : Parse.initEqnOK Nm msrc eqs c x e = true) (hL : order.contains (x.initLabel c) = true)
    (hsome : (nodR c names eqs order e.fn).isSome = true) : NodEqn c I e := by
  obtain ⟨hf, h1, xs, hx⟩ := armInitEqnOK_parts hok
  obtain ⟨xs', hx', hall⟩ := init_arm_eqn (base := armBase c eqs) hM hR hord he hok hL
  rw [hx] at hx'; cases hx'
  have hv : armVarsL e.pats = xs := by rw [(armDistinct_spec hx).1, nod_armVarsL_vars]
  intro ws hws
  rw [hv] at hws ⊢
  obtain ⟨hso, hl⟩ := nodVals_sorts hws
  have hn : order.contains e.fn = true := hf ▸ hL
  have hlook : armLook order eqs e.fn = some e := by
    unfold armLook; rw [if_pos_walk hn, armFind_of_unique rfl he (hf ▸ h1)]
  have hc := List.all_eq_true.mp hchk e.fn (List.contains_iff_mem.mp hn)
  obtain ⟨st, hst⟩ := Option.isSome_iff_exists.mp hsome
  rw [hlook] at hc; dsimp only at hc; rw [hx] at hc; dsimp only at hc; rw [hst] at hc; dsimp only at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hlen, hty⟩ := hc
  have hA : nodA c eqs order e.fn = xs.filterMap fun x => armSrt c x.sort := by simp only [nodA, hlook, hx]
  have hσ := nod_zip_look (c := c) (xs := xs) (ws := ws) (ss := nodA c eqs order e.fn) (by rw [hA, hlen])
    (by rw [hA]; exact hso)
  have hG := nod_G_ok (names := names) hk hR hchk
  obtain ⟨o, ho, -, -⟩ := nodTy_sound hσ e.rhs (fun n _ _ => hG n) st (by rw [hty])
  exact (hall ws hl (nodVals_sorted hws) o ho).2

omit hM in
theorem nod_G_base {n : String} (hn : armLook order eqs n = none) (ws : List GroundTerm) :
    armGOf c eqs names order (armBase c eqs) n ws = armBase c eqs n ws := by
  rw [armGOf, armG_base c _ _ order eqs _ hn]

omit hM in
theorem nod_den_inj (c : Semantics) {S : Kore.KSort} {a b : Srt} (hA : armSrt c S = some a) (hb : c.sortName b = "KItem")
    (p : Kore.Pattern) :
    KoreAML.den (.app ⟨⟨"inj"⟩⟩ [S, KoreAML.srt "KItem"] [p]) =
      KoreAML.appList (KoreAML.sym (.symbol "inj"))
        [KoreAML.Cons.sortP (c.sortName a), KoreAML.Cons.sortP (c.sortName b), KoreAML.den p] := by
  rw [armSrt_spec hA, ← hb]
  exact KoreAML.tr_injP (t := []) (c.sortName a) (c.sortName b) p

/-- **`project:X`'s equation holds at every value of `X`**, an injection or not. -/
theorem nod_proj_eqn (hc : c.coreOK = true) (hfix : nodFixedB c = true) {e : Parse.RawEqn}
    (hnm : names.contains e.fn = true) (hnl : armLook order eqs e.fn = none) (har : armAr eqs e.fn = 1)
    {v : Kore.EVar} {x : Srt} (hp : nodProjX c e = some (v, x)) : NodEqn c I e := by
  simp only [nodFixedB, Bool.and_eq_true, decide_eq_true_eq] at hfix
  obtain ⟨⟨⟨⟨hnk, hnd⟩, hnI⟩, hks⟩, hds⟩ := hfix
  unfold nodProjX at hp
  split at hp
  · rename_i X v0 hX hrhs
    split at hp
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hcond
      obtain ⟨⟨⟨hK, hKI⟩, hvs⟩, hpats⟩ := hcond
      obtain ⟨x', hx', hp'⟩ := Option.bind_eq_some_iff.mp hp
      by_cases hsub : c.subsorts.contains (x', Srt.kitem) = true
      · rw [if_pos_walk hsub] at hp'
        have hvars : armVarsL e.pats = [v0] := by rw [hpats]; rfl
        intro ws hws
        rw [hvars] at hws ⊢
        cases hws with
        | cons hw0 hnil =>
          cases hnil
          rename_i w
          obtain ⟨s, hs1, hws1⟩ := hw0
          rw [hx'] at hs1; cases hs1
          have hl : armSubst c (armZip [v0] [w]) (armLhs e) =
              .app ⟨⟨e.fn⟩⟩ [] [nodItemP v0.sort (w.kore c)] := by
            rw [armLhs, hpats]
            simp [armSubst, armSubsts, nodItemP, armZip, armLookup]
          have hr : armSubst c (armZip [v0] [w]) e.rhs = w.kore c := by
            rw [hrhs]; simp [armSubst, armZip, armLookup]
          rw [hl, hr]
          haveI : OvlOK c := ovlOK_of_core hc
          have htr := CE.injValue_subsorts_trans hc
          have hsub' : (x', Srt.kitem) ∈ c.subsorts := List.contains_iff_mem.mp hsub
          have d1 : DenV c I (KoreAML.den (w.kore c)) w := hM.val hws1
          have d2 := nod_injN hM hc d1 hws1 hsub'
          have hdot : c.sortOf (.ctor dotk []) = some Srt.k := nod_sortOf_ctor hds rfl
          have d3 : DenV c I (KoreAML.appList (symP (c.symName dotk)) []) (.ctor dotk []) := hM.ctor .nil hdot
          have hsK : c.sortOf (.ctor kseq [injNormal x' Srt.kitem w, .ctor dotk []]) = some Srt.k :=
            nod_sortOf_ctor hks (nod_sortsOf_cons (sortOf_injNormal htr hsub' hws1) (nod_sortsOf_cons hdot rfl))
          have d4 := hM.ctor (.cons d2 (.cons d3 .nil)) hsK
          have hgn : e.fn ≠ Parse.getterName := by
            intro h
            have h0 : KoreAML.Parse.dropPrefix? "Lblproject'Coln'" Parse.getterName = none := by decide
            rw [h, h0] at hX; cases hX
          have hG : armGOf c eqs names order (armBase c eqs) e.fn [.ctor kseq [injNormal x' Srt.kitem w, .ctor dotk []]] =
              some w := by
            rw [nod_G_base hnl]
            unfold armBase
            dsimp only
            rw [if_neg_arm (by simpa using hgn), hX]
            dsimp only
            rw [if_neg_arm (by simpa using hK), if_neg_arm (by simpa using hKI), ← hvs, hx']
            exact projFn_item c x' (OvlOK.irrefl x') hws1
          have d5 := hM.name hnm (.cons d4 .nil) har.symm hG hws1
          have hden : KoreAML.den (.app ⟨⟨e.fn⟩⟩ [] [nodItemP v0.sort (w.kore c)]) =
              KoreAML.appList (symP e.fn) [KoreAML.appList (symP (c.symName kseq))
                [KoreAML.appList (KoreAML.sym (.symbol "inj")) [KoreAML.Cons.sortP (c.sortName x'),
                  KoreAML.Cons.sortP (c.sortName Srt.kitem), KoreAML.den (w.kore c)],
                 KoreAML.appList (symP (c.symName dotk)) []]] := by
            rw [armDen_app0, nodItemP, List.map_cons, List.map_nil, armDen_app0, List.map_cons, List.map_cons,
              List.map_nil, nod_den_inj c hx' hnI, armDen_app0, List.map_nil, hnk, hnd]
          rw [hden]
          exact hM.eqn d5 d1
      · rw [if_neg_arm hsub] at hp'; cases hp'
    · cases hp
  · cases hp

/-- **`project:K`'s equation holds at every value of `K`.** -/
theorem nod_projK_eqn {e : Parse.RawEqn} (hnm : names.contains e.fn = true) (hnl : armLook order eqs e.fn = none)
    (har : armAr eqs e.fn = 1) (hp : nodProjKB c e = true) : NodEqn c I e := by
  unfold nodProjKB at hp
  split at hp
  · rename_i v hrhs
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
    obtain ⟨⟨hfn, hpats⟩, hsrt⟩ := hp
    have hvars : armVarsL e.pats = [v] := by rw [hpats]; rfl
    intro ws hws
    rw [hvars] at hws ⊢
    cases hws with
    | cons hw0 hnil =>
      cases hnil
      rename_i w
      obtain ⟨s, hs1, hws1⟩ := hw0
      rw [hsrt] at hs1; cases hs1
      have hl : armSubst c (armZip [v] [w]) (armLhs e) = .app ⟨⟨e.fn⟩⟩ [] [w.kore c] := by
        rw [armLhs, hpats]; simp [armSubst, armSubsts, armZip, armLookup]
      have hr : armSubst c (armZip [v] [w]) e.rhs = w.kore c := by
        rw [hrhs]; simp [armSubst, armZip, armLookup]
      rw [hl, hr, armDen_app0, List.map_cons, List.map_nil]
      have d1 : DenV c I (KoreAML.den (w.kore c)) w := hM.val hws1
      have hG : armGOf c eqs names order (armBase c eqs) e.fn [w] = some w := by
        rw [nod_G_base hnl, hfn]; rfl
      exact hM.eqn (hM.name hnm (.cons d1 .nil) har.symm hG hws1) d1
  · cases hp

/-- **`project:KItem`'s equation holds at every value of `KItem`.** -/
theorem nod_projKItem_eqn (hfix : nodFixedB c = true) {e : Parse.RawEqn} (hnm : names.contains e.fn = true)
    (hnl : armLook order eqs e.fn = none) (har : armAr eqs e.fn = 1) (hp : nodProjKItemB c e = true) :
    NodEqn c I e := by
  simp only [nodFixedB, Bool.and_eq_true, decide_eq_true_eq] at hfix
  obtain ⟨⟨⟨⟨hnk, hnd⟩, -⟩, hks⟩, hds⟩ := hfix
  unfold nodProjKItemB at hp
  split at hp
  · rename_i v hrhs
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
    obtain ⟨⟨hfn, hpats⟩, hsrt⟩ := hp
    have hvars : armVarsL e.pats = [v] := by rw [hpats]; rfl
    intro ws hws
    rw [hvars] at hws ⊢
    cases hws with
    | cons hw0 hnil =>
      cases hnil
      rename_i w
      obtain ⟨s, hs1, hws1⟩ := hw0
      rw [hsrt] at hs1; cases hs1
      have hl : armSubst c (armZip [v] [w]) (armLhs e) =
          .app ⟨⟨e.fn⟩⟩ [] [.app ⟨⟨"kseq"⟩⟩ [] [w.kore c, .app ⟨⟨"dotk"⟩⟩ [] []]] := by
        rw [armLhs, hpats]; simp [armSubst, armSubsts, armZip, armLookup]
      have hr : armSubst c (armZip [v] [w]) e.rhs = w.kore c := by
        rw [hrhs]; simp [armSubst, armZip, armLookup]
      rw [hl, hr, armDen_app0, List.map_cons, List.map_nil, armDen_app0, List.map_cons, List.map_cons, List.map_nil,
        armDen_app0, List.map_nil, ← hnk, ← hnd]
      have d1 : DenV c I (KoreAML.den (w.kore c)) w := hM.val hws1
      have hdot : c.sortOf (.ctor dotk []) = some Srt.k := nod_sortOf_ctor hds rfl
      have d3 : DenV c I (KoreAML.appList (symP (c.symName dotk)) []) (.ctor dotk []) := hM.ctor .nil hdot
      have hsK : c.sortOf (.ctor kseq [w, .ctor dotk []]) = some Srt.k :=
        nod_sortOf_ctor hks (nod_sortsOf_cons hws1 (nod_sortsOf_cons hdot rfl))
      have d4 := hM.ctor (.cons d1 (.cons d3 .nil)) hsK
      have hG : armGOf c eqs names order (armBase c eqs) e.fn [.ctor kseq [w, .ctor dotk []]] = some w := by
        rw [nod_G_base hnl, hfn]; exact itemFn_item w
      exact hM.eqn (hM.name hnm (.cons d4 .nil) har.symm hG hws1) d1
  · cases hp

/-- **The getter's equation holds at every list of values of the top cell's argument sorts.** -/
theorem nod_getter_eqn {e e' : Parse.RawEqn} (hnm : names.contains e.fn = true) (hnl : armLook order eqs e.fn = none)
    (har : armAr eqs e.fn = 1) (hfind : eqs.find? (·.fn == Parse.getterName) = some e') (hpe : e'.pats = e.pats)
    (hp : nodGetterB c e = true) : NodEqn c I e := by
  unfold nodGetterB at hp
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨hfn, hp⟩ := hp
  split at hp
  · rename_i h ss ps x hpats hrhs
    simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hp
    obtain ⟨⟨hss, hh⟩, hp⟩ := hp
    subst hss
    cases hx : Parse.distinctEVars? ps with
    | none => rw [hx] at hp; cases hp
    | some xs =>
      rw [hx] at hp
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
      obtain ⟨⟨hlast, hlen⟩, hargs⟩ := hp
      obtain ⟨k, hk, hka⟩ := Option.map_eq_some_iff.mp hargs
      obtain ⟨hps, hd⟩ := armDistinct_spec hx
      have hvars : armVarsL e.pats = xs := by
        rw [hpats, armVarsL, armVars, hps, nod_armVarsL_vars, armVarsL, List.append_nil]
      intro ws hws
      rw [hvars] at hws ⊢
      obtain ⟨hso, hl⟩ := nodVals_sorts hws
      have hl' : armSubst c (armZip xs ws) (armLhs e) =
          .app ⟨⟨e.fn⟩⟩ [] [.app h [] (ws.map (GroundTerm.kore c))] := by
        rw [armLhs, hpats, armSubst, armSubsts, armSubsts, armSubst, armSubsts_eq, hps, armSubsts_vars c hd hl]
      obtain ⟨i, hi, hxi⟩ : ∃ i, i = xs.length - 1 ∧ xs[i]? = some x := by
        refine ⟨_, rfl, ?_⟩
        rw [List.getLast?_eq_getElem?] at hlast; exact hlast
      have hwi := nod_lookup_idx hd hl i x hxi
      have hlt : i < ws.length := by
        have : i < xs.length := (List.getElem?_eq_some_iff.mp hxi).1
        omega
      obtain ⟨wl, hwl⟩ : ∃ wl, ws[i]? = some wl := ⟨ws[i], List.getElem?_eq_getElem hlt⟩
      have hs := nod_sortsOf_get hso i wl hwl
      obtain ⟨sl, hsl⟩ : ∃ sl, c.sortOf wl = some sl := by
        rw [hs]; exact ⟨_, List.getElem?_eq_getElem (by rw [hlen]; omega)⟩
      have hG : armGOf c eqs names order (armBase c eqs) e.fn [.ctor topLabel ws] = some wl := by
        rw [nod_G_base hnl, hfn]
        unfold armBase
        dsimp only
        rw [if_pos_walk (by decide : (Parse.getterName == Parse.getterName) = true), hfind]
        dsimp only
        rw [hpe, hpats]
        dsimp only
        rw [argFn_ctor, hps, List.length_map, ← hi]
        exact hwl
      have hr : armSubst c (armZip xs ws) e.rhs = wl.kore c := by
        rw [hrhs, armSubst, hwi, hwl]
      rw [hl', hr, armDen_app0, List.map_cons, List.map_nil, armDen_app0, hh, List.map_map]
      have d_args : All2 (DenV c I) (ws.map (den c)) ws := armVals_den hM (nodVals_sorted hws)
      have hsT : c.sortOf (.ctor topLabel ws) = some k.result := nod_sortOf_ctor hk (by rw [hso, hka])
      have d_top := hM.ctor d_args hsT
      have d5 := hM.name hnm (.cons d_top .nil) har.symm hG hsl
      exact hM.eqn d5 (hM.val hsl)
  · cases hp

/-- **A constant initializer's `functional` axiom holds**, where its right side is of a sort and
always has a value. -/
theorem nod_const_functional (hk : lookupSig c.ctorSigs kseq = some ⟨kseq, [Srt.kitem, Srt.k], Srt.k⟩)
    (hR : armRankB order eqs = true) (hchk : nodOrderB c names eqs order = true) {L : String} {e : Parse.RawEqn}
    (hn : names.contains L = true) (hlk : armLook order eqs L = some e) (hx : Parse.distinctEVars? e.pats = some [])
    (har : armAr eqs L = 0) {s : Srt} (hs : nodR c names eqs order L = some (s, true)) (y : EVar) :
    I ⊧ᴵ KoreAML.sExists y (KoreAML.Cons.sortP (c.sortName s)) (.evar y ≡ KoreAML.appList (symP L) []) := by
  have hA : nodA c eqs order L = [] := by simp only [nodA, hlk, hx, List.filterMap_nil]
  obtain ⟨hv, ht⟩ := nod_G_ok (names := names) hk hR hchk L [] (by rw [hA]; rfl) (s, true) hs
  obtain ⟨v, hgv⟩ := Option.isSome_iff_exists.mp (ht rfl)
  have hsv := hv v hgv
  exact hM.functional (hM.name hn .nil har.symm hgv hsv) hsv y

end Eqns

/-! ## The names, one by one -/

/-- A name that is no symbol of the registry or of the semantics is one `armNameB` accepts. -/
theorem nod_name_unnumbered {Nm : Parse.Names} {msrc : String} {eqs : List Parse.RawEqn} {c : Semantics} {n : String}
    (h : (!(regSymNames ++ c.symNames).contains n && n != "" && n != "inj" && n != "Lblite") = true) :
    armNameB Nm msrc eqs c n = true := by
  unfold armNameB; rw [h]; rfl

/-- A registry-numbered projection free of the theory, with an equation `predProjOK?` accepts, is
one `armNameB` accepts. -/
theorem nod_name_reg {Nm : Parse.Names} {msrc : String} {eqs : List Parse.RawEqn} {c : Semantics} {n : String}
    {i : Nat} (hi : regSymNames.idxOf? n = some i) (hf : freeB c [i] = true)
    (hp : (eqs.find? fun e => e.fn == n && Parse.predProjOK? Nm msrc eqs c e == some true).isSome = true)
    (hX : (KoreAML.Parse.dropPrefix? "Lblproject'Coln'" n).isSome = true) : armNameB Nm msrc eqs c n = true := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hp
  have hq := List.find?_some he
  simp only [Bool.and_eq_true, beq_iff_eq] at hq
  obtain ⟨hfn, hok⟩ := hq
  rw [← hfn]
  exact armNameB_of_proj (List.mem_of_find?_eq_some he) (by rw [hfn]; exact hX) hok (by rw [hfn]; exact hi) hf

theorem nod_names_ok {Nm : Parse.Names} {msrc : String} {eqs : List Parse.RawEqn} {c : Semantics}
    {names ns : List String} (hsub : names.all ns.contains = true) (hns : ns.all (armNameB Nm msrc eqs c) = true) :
    names.all (armNameB Nm msrc eqs c) = true :=
  List.all_eq_true.mpr fun n hn =>
    List.all_eq_true.mp hns n (List.contains_iff_mem.mp (List.all_eq_true.mp hsub n hn))

/-! ## By sentence -/

/-- **An equation of the text one of the lemmas above holds of**: the text's equation of its symbol
(the first) has its symbol, patterns and right side, the symbol is a name, and it is an
initializer's the arm takes, or a projection's or the getter's of the shapes above. -/
def nodEqB (Nm : Parse.Names) (msrc : String) (eqs : List Parse.RawEqn) (c : Semantics) (cells : List Cell)
    (names order : List String) (e : Parse.RawEqn) : Bool :=
  match eqs.find? (·.fn == e.fn) with
  | some e' => decide (e'.fn = e.fn ∧ e'.pats = e.pats ∧ e'.rhs = e.rhs) && names.contains e.fn &&
      ((order.contains e.fn && armAccB Nm msrc eqs c cells e.fn && (nodR c names eqs order e.fn).isSome) ||
        ((armLook order eqs e.fn).isNone && decide (armAr eqs e.fn = 1) &&
          ((nodProjX c e).isSome || nodProjKB c e || nodProjKItemB c e || nodGetterB c e)))
  | none => false

/-- The sentence of index `i` is an equation (as the account's scan reads it) `nodEqB` takes. -/
def nodSentEqB (Nm : Parse.Names) (msrc : String) (eqs : List Parse.RawEqn) (c : Semantics) (cells : List Cell)
    (names order : List String) (sents : List KoreAML.AxiomDecl) (i : Nat) : Bool :=
  match sents.find? (·.index == i) with
  | some ad => match Parse.scanEqn (.axiom ad.ax) with
    | some e => nodEqB Nm msrc eqs c cells names order e
    | none => false
  | none => false

/-- The sentence of index `i` is the `functional` axiom `∃y:S. y = L()` of a constant initializer
`L` whose right side is of the sort `S` and always has a value. -/
def nodSentFunB (c : Semantics) (eqs : List Parse.RawEqn) (names order : List String) (sents : List KoreAML.AxiomDecl)
    (i : Nat) : Bool :=
  match sents.find? (·.index == i) with
  | some ad => match nodFunctional? ad.ax with
    | some (L, S) => names.contains L && decide (armAr eqs L = 0) &&
        (match armLook order eqs L with
         | some e => decide (Parse.distinctEVars? e.pats = some [])
         | none => false) &&
        (match nodR c names eqs order L, armSrt c S with
         | some (s, true), some s' => decide (s = s')
         | _, _ => false)
    | none => false
  | none => false

theorem nod_eqB {c : Semantics} {Nm : Parse.Names} {msrc : String} {eqs : List Parse.RawEqn} {cells : List Cell}
    {names order : List String} {I : Interpretation KoreAML.Sym Elem}
    (hM : InitModel c (fun n => names.contains n = true) (armAr eqs) (armGOf c eqs names order (armBase c eqs)) I)
    (hc : c.coreOK = true) (hfix : nodFixedB c = true) (hR : armRankB order eqs = true)
    (hord : order.all names.contains = true) (hchk : nodOrderB c names eqs order = true) {e : Parse.RawEqn}
    (h : nodEqB Nm msrc eqs c cells names order e = true) : NodEqn c I e := by
  have hk : lookupSig c.ctorSigs kseq = some ⟨kseq, [Srt.kitem, Srt.k], Srt.k⟩ := by
    simp only [nodFixedB, Bool.and_eq_true, decide_eq_true_eq] at hfix; exact hfix.1.2
  unfold nodEqB at h
  cases hf : eqs.find? (·.fn == e.fn) with
  | none => rw [hf] at h; cases h
  | some e' =>
    rw [hf] at h; dsimp only at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hfn, hpa, hrh⟩, hnm⟩, h⟩ := h
    have he' : e' ∈ eqs := List.mem_of_find?_eq_some hf
    rcases h with ⟨⟨hin, hacc⟩, hsome⟩ | ⟨⟨hnl, har⟩, hsh⟩
    · unfold armAccB at hacc
      cases hx : cells.find? (·.initLabel c == e.fn) with
      | none => rw [hx] at hacc; cases hacc
      | some x =>
        rw [hx, hf] at hacc
        have hxL : x.initLabel c = e.fn := by have := List.find?_some hx; exact beq_iff_eq.mp this
        exact nodEqn_congr hfn hpa hrh (nod_init_eqn hM hk hR hord hchk he' hacc (by rw [hxL]; exact hin) (by rw [hfn]; exact hsome))
    · have hnl' : armLook order eqs e.fn = none := Option.isNone_iff_eq_none.mp hnl
      rcases hsh with ((hp | hp) | hp) | hp
      · obtain ⟨⟨v, x⟩, hvx⟩ := Option.isSome_iff_exists.mp hp
        exact nod_proj_eqn hM hc hfix hnm hnl' har hvx
      · exact nod_projK_eqn hM hnm hnl' har hp
      · exact nod_projKItem_eqn hM hfix hnm hnl' har hp
      · have hg : e.fn = Parse.getterName := by
          unfold nodGetterB at hp; simp only [Bool.and_eq_true, beq_iff_eq] at hp; exact hp.1
        rw [hg] at hf
        exact nod_getter_eqn hM hnm hnl' har hf hpa hp

/-- **One model of the theory, whose steps are the semantics', in which each listed sentence
holds**: the equations (`eqIdx`) at every list of values of their variables' sorts, the constants'
`functional` axioms (`funIdx`). -/
theorem nod_instance (c : Semantics) (hc : c.coreOK = true) (hf : FnHyp c) (Nm : Parse.Names) (msrc : String)
    (eqs : List Parse.RawEqn) (cells : List Cell) (names order : List String) (sents : List KoreAML.AxiomDecl)
    (eqIdx funIdx : List Nat)
    (hnames : names.all (armNameB Nm msrc eqs c) = true) (hR : armRankB order eqs = true)
    (hord : order.all names.contains = true) (hchk : nodOrderB c names eqs order = true)
    (hfix : nodFixedB c = true)
    (heq : eqIdx.all (nodSentEqB Nm msrc eqs c cells names order sents) = true)
    (hfun : funIdx.all (nodSentFunB c eqs names order sents) = true) :
    ∃ I : Interpretation KoreAML.Sym Elem, (I ⊧ᴵP (Γc c ∪ Γstep c)) ∧
      (∀ x y : Config c, Step c x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val)))) ∧
      (∀ i ∈ eqIdx, ∃ ad ∈ sents, ad.index = i ∧ ∃ e, Parse.scanEqn (.axiom ad.ax) = some e ∧ NodEqn c I e) ∧
      (∀ i ∈ funIdx, ∃ ad ∈ sents, ad.index = i ∧ ∃ L S, nodFunctional? ad.ax = some (L, S) ∧ NodFun c I L S) := by
  obtain ⟨I, hM, hstep⟩ := model_of_arm c hc hf Nm msrc eqs names order (armBase c eqs) hnames
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
            exact nod_const_functional hM hk hR hchk hn hl hx har hR0 y
          · cases hsr

/-! ## Under every interpretation of the parameters -/

kernel_rfl nodOrderB_withHooks : ∀ (c : Semantics) (H : HookParams) (names : List String) (eqs : List Parse.RawEqn)
  (order : List String), nodOrderB (c.withHooks H) names eqs order = nodOrderB c names eqs order
kernel_rfl nodFixedB_withHooks : ∀ (c : Semantics) (H : HookParams), nodFixedB (c.withHooks H) = nodFixedB c
kernel_rfl nodSentEqB_withHooks : ∀ (c : Semantics) (H : HookParams) (Nm : Parse.Names) (msrc : String)
  (eqs : List Parse.RawEqn) (cells : List Cell) (names order : List String) (sents : List KoreAML.AxiomDecl) (i : Nat),
  nodSentEqB Nm msrc eqs (c.withHooks H) cells names order sents i = nodSentEqB Nm msrc eqs c cells names order sents i
kernel_rfl nodSentFunB_withHooks : ∀ (c : Semantics) (H : HookParams) (eqs : List Parse.RawEqn)
  (names order : List String) (sents : List KoreAML.AxiomDecl) (i : Nat),
  nodSentFunB (c.withHooks H) eqs names order sents i = nodSentFunB c eqs names order sents i
kernel_rfl armNameB_withHooks : ∀ (c : Semantics) (H : HookParams) (Nm : Parse.Names) (msrc : String)
  (eqs : List Parse.RawEqn) (n : String), armNameB Nm msrc eqs (c.withHooks H) n = armNameB Nm msrc eqs c n

/-- **`nod_instance` under every interpretation `H` of the parameters**, its checks decided once on
the data: each reads no interpretation. -/
theorem nod_instance_withHooks (c : Semantics) (hc : c.coreOK = true) (hf : ∀ H, FnHyp (c.withHooks H))
    (Nm : Parse.Names) (msrc : String) (eqs : List Parse.RawEqn) (cells : List Cell) (names order : List String)
    (sents : List KoreAML.AxiomDecl) (eqIdx funIdx : List Nat)
    (hnames : names.all (armNameB Nm msrc eqs c) = true) (hR : armRankB order eqs = true)
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
  nod_instance (c.withHooks H) ((Semantics.coreOK_withHooks c H).trans hc) (hf H) Nm msrc eqs cells names order sents
    eqIdx funIdx (by rw [show armNameB Nm msrc eqs (c.withHooks H) = armNameB Nm msrc eqs c from funext (armNameB_withHooks c H Nm msrc eqs)]; exact hnames) hR hord
    ((nodOrderB_withHooks c H names eqs order).trans hchk) ((nodFixedB_withHooks c H).trans hfix)
    (by rw [show nodSentEqB Nm msrc eqs (c.withHooks H) cells names order sents = nodSentEqB Nm msrc eqs c cells names order sents from funext (nodSentEqB_withHooks c H Nm msrc eqs cells names order sents)]; exact heq)
    (by rw [show nodSentFunB (c.withHooks H) eqs names order sents = nodSentFunB c eqs names order sents from funext (nodSentFunB_withHooks c H eqs names order sents)]; exact hfun)


/-! ## The names, with one freeness check for the registry's projections -/

section FreeSub

open DetachedB

variable {c : Semantics} {ks ks' : List Sym}

/-- A symbol named by none of `ks` is named by none of fewer symbols `ks'`. -/
theorem nodFree_name (hs : ∀ k ∈ ks', k ∈ ks) {σ : KoreAML.Sym} (h : (!isName c [] ks σ) = true) :
    (!isName c [] ks' σ) = true := by
  cases σ with
  | symbol n =>
    simp only [isName, Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at h ⊢
    exact fun k hk => h k (hs k hk)
  | _ => rfl

theorem nodFree_clean (hs : ∀ k ∈ ks', k ∈ ks) {φ : KoreAML.P} (h : clean c [] ks φ = true) :
    clean c [] ks' φ = true :=
  List.all_eq_true.mpr fun σ hσ => nodFree_name hs (List.all_eq_true.mp h σ hσ)

/-- At no sort, every sort's name is none of the names. -/
theorem nodFree_sOK (s : Srt) : sOK c [] ks s = true := rfl

theorem nodFree_kOK (hs : ∀ k ∈ ks', k ∈ ks) {f : Sym} (h : kOK c [] ks f = true) : kOK c [] ks' f = true :=
  nodFree_name hs h

theorem nodFree_appOK (hs : ∀ k ∈ ks', k ∈ ks) {f : Sym} (h : appOK c [] ks f = true) : appOK c [] ks' f = true := by
  unfold appOK at h ⊢
  split
  · rename_i X hX
    rw [hX] at h
    simp only [Bool.and_eq_true] at h ⊢
    exact ⟨nodFree_name hs h.1, nodFree_name hs h.2⟩
  · rename_i hX
    rw [hX] at h
    exact nodFree_kOK hs h

/-- A symbol of `ks` is no hook where `freeB c ks`'s last part holds, so no item is the arity of a
hook of `ks`. -/
theorem nodFree_regSig (hh : hookSigs.all (fun k => kOK c [] ks k.name) = true) (φ : KoreAML.P) :
    regSig c [] ks φ = false := by
  unfold regSig
  simp only [List.any_nil, Bool.false_or, List.any_eq_false, Bool.and_eq_true, not_and]
  intro h hh' hk
  have := List.all_eq_true.mp hh h hh'
  simp only [kOK, isName, Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at this
  exact absurd rfl (this h.name (List.contains_iff_mem.mp hk))

/-- **`freeB` at fewer symbols**: where no premise names the symbols `ks`, none names those of a
sublist `ks'`. -/
theorem nodFreeB_sub (hs : ∀ k ∈ ks', k ∈ ks) (h : freeB c ks = true) : freeB c ks' = true := by
  unfold freeB at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨hl, hv⟩, hg⟩, hh⟩ := h
  have hcl := @nodFree_clean c ks ks' hs
  have hk := @nodFree_kOK c ks ks' hs
  have ha := @nodFree_appOK c ks ks' hs
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, List.all_eq_true.mpr fun k hk' => hk (List.all_eq_true.mp hh k hk')⟩
  · unfold listsB at hl ⊢
    simp only [Bool.and_eq_true, List.all_eq_true] at hl ⊢
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hl
    refine ⟨⟨⟨fun it hit => ?_, fun it hit => hcl (h2 it hit)⟩, fun k hk' => ?_⟩, hcl h4⟩
    · have := h1 it hit
      rw [nodFree_regSig hh, Bool.or_false] at this
      rw [hcl this, Bool.true_or]
    · have := h3 k hk'
      have hn : ¬ (builtinColls.contains k = true ∧ ([] : List Srt).contains k.sort = true) := by simp
      simp only [hn, ↓reduceIte, Bool.and_eq_true, List.all_eq_true] at this ⊢
      exact ⟨hcl this.1, fun a ha' => hcl (this.2 a ha')⟩
  · unfold valuesB at hv ⊢
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at hv ⊢
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hv
    refine ⟨⟨⟨fun k hk' => ⟨hk (h1 k hk').1, fun s _ => nodFree_sOK s⟩, fun p _ => ⟨nodFree_sOK _, nodFree_sOK _⟩⟩,
      fun k hk' => .inr ?_⟩, nodFree_name hs h4⟩
    rcases h3 k hk' with h | h
    · simp [nodFree_sOK] at h
    · obtain ⟨⟨⟨⟨hu, he⟩, hc⟩, -⟩, -⟩ := h
      exact ⟨⟨⟨⟨hk hu, hk he⟩, hk hc⟩, nodFree_sOK _⟩, by cases k.val <;> rfl⟩
  · unfold graphsB at hg ⊢
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at hg ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hg
    refine ⟨⟨fun k hk' => .inr ⟨?_, fun s _ => nodFree_sOK s⟩, fun k hk' => ⟨ha (h2 k hk').1, fun s _ => nodFree_sOK s⟩⟩,
      fun f hf => ⟨ha (h3 f hf).1, fun s _ => nodFree_sOK s⟩⟩
    rcases h1 k hk' with h | h
    · rw [List.all_eq_true.mp hh k hk'] at h; cases h
    · exact ha h.1

end FreeSub

/-- The registry numbers of the sorts' projections among `names`: the symbols one freeness check
(`freeB`) covers. -/
def nodRegKs (names : List String) : List Sym :=
  names.filterMap fun n =>
    if (KoreAML.Parse.dropPrefix? "Lblproject'Coln'" n).isSome then regSymNames.idxOf? n else none

/-- `armNameB` without its freeness check: the name is no symbol of the registry or of `c` (nor
`""`, `inj`, `Lblite`), or a sort's projection with an equation `predProjOK?` accepts. -/
def nodNameB (Nm : Parse.Names) (msrc : String) (eqs : List Parse.RawEqn) (c : Semantics) (n : String) : Bool :=
  (!(regSymNames ++ c.symNames).contains n && n != "" && n != "inj" && n != "Lblite") ||
  ((KoreAML.Parse.dropPrefix? "Lblproject'Coln'" n).isSome &&
    eqs.any fun e => e.fn == n && Parse.predProjOK? Nm msrc eqs c e == some true)

/-- **The names `armNameB` accepts, with one freeness check**: each name `nodNameB` accepts, the
registry's projections among them free of the theory together (`freeB c (nodRegKs names)`). -/
theorem nod_names_reg {Nm : Parse.Names} {msrc : String} {eqs : List Parse.RawEqn} {c : Semantics}
    {names : List String} {ks : List Sym} (hks : (nodRegKs names).all ks.contains = true)
    (hfree : freeB c ks = true) (hn : names.all (nodNameB Nm msrc eqs c) = true) :
    names.all (armNameB Nm msrc eqs c) = true := by
  refine List.all_eq_true.mpr fun n hmem => ?_
  have h := List.all_eq_true.mp hn n hmem
  unfold nodNameB at h
  unfold armNameB
  rcases Bool.or_eq_true_iff.mp h with h1 | h2
  · rw [h1, Bool.true_or]
  · simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at h2
    obtain ⟨hX, e, he, hfn, hok⟩ := h2
    refine Bool.or_eq_true_iff.mpr (.inr ?_)
    rw [hX, Bool.true_and]
    refine List.any_eq_true.mpr ⟨e, he, ?_⟩
    subst hfn
    have hfr : Parse.regProjFree c e.fn = true := by
      unfold Parse.regProjFree
      rw [hX]
      cases hi : regSymNames.idxOf? e.fn with
      | none => rfl
      | some i =>
        refine nodFreeB_sub (fun k hk => ?_) hfree
        rw [List.mem_singleton.mp hk]
        exact List.contains_iff_mem.mp (List.all_eq_true.mp hks i
          (List.mem_filterMap.mpr ⟨e.fn, hmem, by rw [hX, hi]; rfl⟩))
    simp only [beq_self_eq_true, Bool.true_and, Parse.predProjAcc, hok, hfr]

/-- **`nod_instance` with one freeness check for the registry's projections among the names**
(`nod_names_reg`). -/
theorem nod_instance_reg (c : Semantics) (hc : c.coreOK = true) (hf : FnHyp c) (Nm : Parse.Names) (msrc : String)
    (eqs : List Parse.RawEqn) (cells : List Cell) (names order : List String) (sents : List KoreAML.AxiomDecl)
    (eqIdx funIdx : List Nat)
    (ks : List Sym) (hks : (nodRegKs names).all ks.contains = true) (hfree : freeB c ks = true)
    (hnames : names.all (nodNameB Nm msrc eqs c) = true)
    (hR : armRankB order eqs = true)
    (hord : order.all names.contains = true) (hchk : nodOrderB c names eqs order = true)
    (hfix : nodFixedB c = true)
    (heq : eqIdx.all (nodSentEqB Nm msrc eqs c cells names order sents) = true)
    (hfun : funIdx.all (nodSentFunB c eqs names order sents) = true) :
    ∃ I : Interpretation KoreAML.Sym Elem, (I ⊧ᴵP (Γc c ∪ Γstep c)) ∧
      (∀ x y : Config c, Step c x y ↔ ¬ (I ⊧ᴵ (den c x.val ⇒ ∼ KoreAML.sNext (den c y.val)))) ∧
      (∀ i ∈ eqIdx, ∃ ad ∈ sents, ad.index = i ∧ ∃ e, Parse.scanEqn (.axiom ad.ax) = some e ∧ NodEqn c I e) ∧
      (∀ i ∈ funIdx, ∃ ad ∈ sents, ad.index = i ∧ ∃ L S, nodFunctional? ad.ax = some (L, S) ∧ NodFun c I L S) :=
  nod_instance c hc hf Nm msrc eqs cells names order sents eqIdx funIdx (nod_names_reg hks hfree hnames) hR hord hchk
    hfix heq hfun

/-- **`nod_instance_withHooks` with one freeness check for the registry's projections among the
names** (`nod_names_reg`), decided once on the data. -/
theorem nod_instance_reg_withHooks (c : Semantics) (hc : c.coreOK = true) (hf : ∀ H, FnHyp (c.withHooks H))
    (Nm : Parse.Names) (msrc : String) (eqs : List Parse.RawEqn) (cells : List Cell) (names order : List String)
    (sents : List KoreAML.AxiomDecl) (eqIdx funIdx : List Nat)
    (ks : List Sym) (hks : (nodRegKs names).all ks.contains = true) (hfree : freeB c ks = true)
    (hnames : names.all (nodNameB Nm msrc eqs c) = true)
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
  nod_instance_withHooks c hc hf Nm msrc eqs cells names order sents eqIdx funIdx (nod_names_reg hks hfree hnames) hR
    hord hchk hfix heq hfun H

end GenEqs

end KCore
