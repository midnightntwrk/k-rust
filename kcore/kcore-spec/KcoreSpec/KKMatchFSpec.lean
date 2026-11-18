import KcoreSpec.KKMatchF
import KcoreSpec.Uniq

/-!
# `matchF` against `PatVal`, for a pattern without a collection

`matchF_sound`: a substitution `matchF` gives at the encoding of a pattern and of a value extends
the one it was given, binds every variable of the pattern, holds encodings of values of the
variables' sorts where the given one does (`BindOK`), and every `σ` that reads it (`BindRep`) makes
the pattern denote the value (`PatVal`). `matchF_complete`: where the pattern denotes the value
under a well-sorted `σ` and the given substitution agrees with `σ` (`BindAgree`), `matchF` gives
exactly one substitution, which agrees with `σ` and binds every variable of the pattern.

Both are about one semantics `c` and take, of `c`: `Exec.MatchCtxO c` (transitive and irreflexive
subsorts, the map pattern symbols no constructors) and no overloading symbol; of the pattern: its
encoding without `cb` (`noCb`) and its sort over `c.patCtxNF`, the first conjunct of
`Semantics.clauseSorted`; of the value, for soundness: the pattern's sort in `c` and literals
`kore.k` has (`litsV`). `matchCtx_d₀` gives the two facts of `c := d₀ d` from `execReady d` and
`encodable d`.
-/

set_option autoImplicit false

namespace KCore.KK

open KCore.Exec (MatchCtxO)

/-! ## A term without a collection pattern -/

mutual
/-- No `cb` in the term. -/
def noCb : T → Bool
  | .ap _ as | .hk _ as | .co _ _ as => noCbL as
  | .ij _ _ t | .as t _ | .el t => noCb t
  | .kv a v | .en a v => noCb a && noCb v
  | .cb _ _ _ => false
  | .iv _ | .bv _ | .tk _ _ | .vr _ | .bot => true
  termination_by structural t => t
def noCbL : List T → Bool
  | [] => true
  | t :: ts => noCb t && noCbL ts
  termination_by structural ts => ts
end

/-! ## What a substitution of `kore.k` holds -/

/-- Every entry of `B` is a variable of `vars` with the encoding of a value of its sort whose
literals `kore.k` has. -/
def BindOK (c : Semantics) (vars : List Srt) (B : Bind) : Prop :=
  ∀ e ∈ B, ∃ (i : Nat) (w : GroundTerm) (s : Srt), e = ((i : Int), enc w) ∧ vars[i]? = some s ∧
    c.sortOf w = some s ∧ litsV w = true

/-- `σ` reads `B`: what `B` gives a variable is the encoding of what `σ` gives it, a value of the
variable's sort whose literals `kore.k` has. -/
def BindRep (c : Semantics) (vars : List Srt) (B : Bind) (σ : Subst) : Prop :=
  ∀ x t, lookF x B = some t → ∃ (i : Nat) (w : GroundTerm) (s : Srt), x = (i : Int) ∧
    σ.lookup i = some w ∧ t = enc w ∧ vars[i]? = some s ∧ c.sortOf w = some s ∧ litsV w = true

/-- `B` agrees with `σ`: what `B` gives a variable is the encoding of what `σ` gives it. -/
def BindAgree (B : Bind) (σ : Subst) : Prop :=
  ∀ x t, lookF x B = some t → ∃ (i : Nat) (w : GroundTerm), x = (i : Int) ∧ σ.lookup i = some w ∧
    t = enc w

/-- `B'` gives every variable of `B` what `B` gives it. -/
def BindExt (B B' : Bind) : Prop := ∀ x t, lookF x B = some t → lookF x B' = some t

theorem bindOK_nil (c : Semantics) (vars : List Srt) : BindOK c vars [] := fun _ h => nomatch h

theorem bindAgree_nil (σ : Subst) : BindAgree [] σ := fun _ _ h => by simp [lookF] at h

theorem BindExt.refl (B : Bind) : BindExt B B := fun _ _ h => h

theorem BindExt.trans {B B₁ B₂ : Bind} (h1 : BindExt B B₁) (h2 : BindExt B₁ B₂) : BindExt B B₂ :=
  fun x t h => h2 x t (h1 x t h)

theorem BindExt.isSome {B B' : Bind} (h : BindExt B B') {x : Int} (hx : (lookF x B).isSome = true) :
    (lookF x B').isSome = true := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hx
  rw [h x t ht]; rfl

theorem BindRep.of_ext {c : Semantics} {vars : List Srt} {B B' : Bind} {σ : Subst}
    (h : BindExt B B') (hr : BindRep c vars B' σ) : BindRep c vars B σ :=
  fun x t hx => hr x t (h x t hx)

theorem lookF_cons_kmf (x y : Int) (t : T) (B : Bind) :
    lookF x ((y, t) :: B) = if x = y then some t else lookF x B := by rw [lookF]

theorem lookF_mem_kmf {x : Int} {t : T} : ∀ {B : Bind}, lookF x B = some t → (x, t) ∈ B
  | [], h => by simp [lookF] at h
  | (y, u) :: B, h => by
    rw [lookF_cons_kmf] at h
    split at h
    · rename_i hxy; cases h; subst hxy; simp
    · exact List.mem_cons_of_mem _ (lookF_mem_kmf h)

/-- A substitution whose entries are encodings of sorted values is read by some `σ`. -/
theorem BindOK.rep {c : Semantics} {vars : List Srt} : ∀ {B : Bind}, BindOK c vars B →
    ∃ σ : Subst, BindRep c vars B σ
  | [], _ => ⟨[], fun _ _ h => by simp [lookF] at h⟩
  | e :: B, h => by
    obtain ⟨σ, hσ⟩ := BindOK.rep (B := B) fun e' he' => h e' (List.mem_cons_of_mem _ he')
    obtain ⟨i, w, s, rfl, hs, hw, lw⟩ := h e (by simp)
    refine ⟨(i, w) :: σ, fun x t hx => ?_⟩
    rw [lookF_cons_kmf] at hx
    split at hx
    · rename_i hxi
      cases hx
      exact ⟨i, w, s, hxi, by simp [List.lookup], rfl, hs, hw, lw⟩
    · rename_i hxi
      obtain ⟨j, w', s', rfl, h1, h2, h3, h4, h5⟩ := hσ x t hx
      have hji : (j == i) = false := by
        rw [beq_eq_false_iff_ne]; intro hji; exact hxi (by rw [hji])
      exact ⟨j, w', s', rfl, by simp [List.lookup, hji, h1], h2, h3, h4, h5⟩

/-- What `σ` gives a variable whose entry in a substitution it reads is the encoding of `v`. -/
theorem BindRep.lookup {c : Semantics} {vars : List Srt} {B : Bind} {σ : Subst}
    (hr : BindRep c vars B σ) {i : Nat} {v : GroundTerm} {s : Srt} (hl : lookF (i : Int) B = some (enc v))
    (hv : c.sortOf v = some s) (lv : litsV v = true) : σ.lookup i = some v := by
  obtain ⟨j, w, s', hij, h1, h2, -, h4, h5⟩ := hr _ _ hl
  have : i = j := Int.natCast_inj.mp hij
  subst this
  rw [h1, enc_inj hv h4 lv h5 h2]

/-! ## `bindVar` and `bindAfter` -/

/-- A substitution `bindVar` gives has `X` at `T`, and is the given one or the given one with that
entry before it. -/
theorem bindVarF_mem {x : Int} {t : T} {B B' : Bind} (h : B' ∈ bindVarF x t B (lookF x B)) :
    lookF x B' = some t ∧ BindExt B B' ∧ (B' = B ∨ B' = (x, t) :: B) := by
  cases hl : lookF x B with
  | none =>
    rw [hl] at h
    simp only [bindVarF, List.mem_singleton] at h
    subst h
    refine ⟨by simp [lookF_cons_kmf], fun y u hy => ?_, .inr rfl⟩
    rw [lookF_cons_kmf]
    split
    · rename_i hyx; subst hyx; rw [hl] at hy; cases hy
    · exact hy
  | some u =>
    rw [hl] at h
    simp only [bindVarF] at h
    split at h
    · rename_i htu
      simp only [List.mem_singleton] at h
      subst h; subst htu
      exact ⟨hl, BindExt.refl _, .inl rfl⟩
    · cases h

theorem bindVarF_ok {c : Semantics} {vars : List Srt} {i : Nat} {v : GroundTerm} {s : Srt}
    {B B' : Bind} (hs : vars[i]? = some s) (hv : c.sortOf v = some s) (lv : litsV v = true)
    (h : B' ∈ bindVarF (i : Int) (enc v) B (lookF (i : Int) B)) (hB : BindOK c vars B) :
    BindOK c vars B' := by
  rcases (bindVarF_mem h).2.2 with rfl | rfl
  · exact hB
  · intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨i, v, s, rfl, hs, hv, lv⟩
    · exact hB e he

theorem bindAfterF_mem {x : Int} {t : T} {B' : Bind} : ∀ {ms : Ms}, B' ∈ bindAfterF x t ms →
    ∃ B₁ ∈ ms, B' ∈ bindVarF x t B₁ (lookF x B₁)
  | [], h => by simp [bindAfterF] at h
  | B :: ms, h => by
    simp only [bindAfterF, List.mem_append] at h
    rcases h with h | h
    · exact ⟨B, by simp, h⟩
    · obtain ⟨B₁, h1, h2⟩ := bindAfterF_mem h
      exact ⟨B₁, by simp [h1], h2⟩

/-- Where the given substitution agrees with `σ`, `bindVar` at what `σ` gives the variable gives
one substitution, which agrees with `σ`. -/
theorem bindVarF_agree {σ : Subst} {B : Bind} {i : Nat} {v : GroundTerm} (hB : BindAgree B σ)
    (hi : σ.lookup i = some v) :
    ∃ B', bindVarF (i : Int) (enc v) B (lookF (i : Int) B) = [B'] ∧ BindAgree B' σ ∧ BindExt B B' ∧
      lookF (i : Int) B' = some (enc v) := by
  cases hl : lookF (i : Int) B with
  | none =>
    refine ⟨((i : Int), enc v) :: B, rfl, fun x t hx => ?_, fun y u hy => ?_, by simp [lookF_cons_kmf]⟩
    · rw [lookF_cons_kmf] at hx
      split at hx
      · rename_i hxi; cases hx; exact ⟨i, v, hxi, hi, rfl⟩
      · exact hB x t hx
    · rw [lookF_cons_kmf]
      split
      · rename_i hyx; subst hyx; rw [hl] at hy; cases hy
      · exact hy
  | some u =>
    obtain ⟨j, w, hij, h1, h2⟩ := hB _ _ hl
    have : i = j := Int.natCast_inj.mp hij
    subst this
    rw [hi] at h1; cases h1
    subst h2
    exact ⟨B, by simp [bindVarF], hB, BindExt.refl _, hl⟩

/-! ## The encoding of a pattern, form by form -/

section
variable (c : Semantics)

theorem encTerm_var_kmf (i : Nat) : encTerm c (.var i) = some (.vr i) := by
  simp [encTerm, encTermWith]

theorem encTerm_dv_kmf (s : Srt) (l : Lit) : encTerm c (.dv s l) = encLit s l := by
  simp [encTerm, encTermWith]

theorem encTerm_inj_kmf (a b : Srt) (t : Term) :
    encTerm c (.inj a b t) = (encTerm c t).map (.ij a b) := by
  simp [encTerm, encTermWith]

theorem encTerm_as_kmf (t : Term) (i : Nat) : encTerm c (.as t i) = (encTerm c t).map (.as · i) := by
  simp [encTerm, encTermWith]

theorem encTerm_app_kmf (f : Sym) (ts : List Term) :
    encTerm c (.app f ts) = readApp c f (encTermsWith c encLit ts)
      ((collSymOf c f).bind fun (k, s, r) => encCollWith c encLit k s r ts) := by
  simp [encTerm, encTermWith]

theorem encTerms_cons_kmf {t : Term} {ts : List Term} {qs : List T}
    (h : encTermsWith c encLit (t :: ts) = some qs) :
    ∃ q qs', encTerm c t = some q ∧ encTermsWith c encLit ts = some qs' ∧ qs = q :: qs' := by
  rw [encTermsWith] at h
  unfold encTerm
  split at h
  · rename_i p ps h1 h2; cases h; exact ⟨p, ps, h1, h2, rfl⟩
  · cases h

theorem encTerms_nil_kmf {qs : List T} (h : encTermsWith c encLit [] = some qs) : qs = [] := by
  rw [encTermsWith] at h; cases h; rfl

variable {c}

/-- An application's form without `cb`: the symbol applied to its arguments' forms, by a
constructor or by a function that is no parameter, or an operation. -/
theorem readApp_noCb_kmf {f : Sym} {args parts : Option (List T)} {q : T}
    (h : readApp c f args parts = some q) (hq : noCb q = true) :
    (∃ qs, args = some qs ∧ q = .ap f qs ∧ (c.isCtor f = true ∨ c.isParam f = false)) ∨
      ∃ o as, q = .hk o as := by
  unfold readApp at h
  split at h
  · rename_i hc
    obtain ⟨qs, rfl, rfl⟩ := Option.map_eq_some_iff.mp h
    exact .inl ⟨qs, rfl, rfl, .inl hc⟩
  · split at h
    · obtain ⟨ps, -, rfl⟩ := Option.map_eq_some_iff.mp h
      simp [noCb] at hq
    · split at h
      · split at h
        · obtain ⟨qs, -, rfl⟩ := Option.map_eq_some_iff.mp h
          exact .inr ⟨_, _, rfl⟩
        · obtain ⟨qs, -, h'⟩ := Option.bind_eq_some_iff.mp h
          unfold derivedHook at h'
          split at h'
          · cases h'; exact .inr ⟨_, _, rfl⟩
          · cases h'
      · split at h
        · cases h
        · rename_i hp
          split at h
          · obtain ⟨qs, rfl, rfl⟩ := Option.map_eq_some_iff.mp h
            exact .inl ⟨qs, rfl, rfl, .inr (by simpa using hp)⟩
          · cases h

theorem readApp_ctor_kmf {f : Sym} (hc : c.isCtor f = true) (args parts : Option (List T)) :
    readApp c f args parts = args.map (.ap f) := by
  simp [readApp, hc]

/-- A collection symbol that is no constructor is read as a collection pattern. -/
theorem readApp_coll_kmf {f : Sym} (hc : c.isCtor f = false) (hk : (collSymOf c f).isSome = true)
    {args parts : Option (List T)} {q : T} (h : readApp c f args parts = some q) : noCb q = false := by
  obtain ⟨⟨k, s, r⟩, hk⟩ := Option.isSome_iff_exists.mp hk
  simp only [readApp, hc, Bool.false_eq_true, ite_false, hk] at h
  obtain ⟨ps, -, rfl⟩ := Option.map_eq_some_iff.mp h
  simp [noCb]

theorem libCollOf_pats_kmf :
    (patternHooks ++ collPatternHooks).all (fun g => (libCollOf g).isSome && isHook g) = true := by
  decide +kernel

/-- A map, set or list pattern symbol is a collection symbol. -/
theorem collSymOf_pat_kmf {f : Sym} (h : patternHooks.contains f = true ∨ c.isCollPat f = true) :
    (collSymOf c f).isSome = true := by
  have hall : ∀ g, (patternHooks.contains g || collPatternHooks.contains g) = true →
      (libCollOf g).isSome = true ∧ isHook g = true := by
    intro g hg
    have hm : g ∈ patternHooks ++ collPatternHooks :=
      List.mem_append.mpr (by simpa [List.contains_iff_mem] using hg)
    simpa using List.all_eq_true.mp libCollOf_pats_kmf g hm
  rcases h with h | h
  · obtain ⟨h1, h2⟩ := hall f (by rw [h]; rfl)
    simp [collSymOf, h2, h1]
  · unfold Semantics.isCollPat at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨-, h⟩ := h
    split at h
    · rename_i hh
      obtain ⟨h1, h2⟩ := hall f (by rw [h, Bool.or_true])
      simp [collSymOf, h2, h1]
    · rename_i hh
      unfold collSymOf
      simp only [hh, Bool.false_eq_true, ite_false]
      cases hk : c.lookupParam f with
      | none => simp [hk] at h
      | some k =>
        cases hg : k.impl with
        | none => simp [hk, hg] at h
        | some g =>
          simp only [hk, hg] at h
          simp only [hg, Option.bind_some, Option.isSome_map]
          exact (hall g h).1

end

/-! ## A value from the form of its encoding -/

theorem enc_ctor_kmf (f : Sym) (vs : List GroundTerm) : enc (.ctor f vs) = .ap f (encTs vs) := by
  rw [enc]

theorem enc_inj_form_kmf (a b : Srt) (v : GroundTerm) : enc (.inj a b v) = .ij a b (enc v) := by
  rw [enc]

theorem enc_eq_ap_kmf {v : GroundTerm} {f : Int} {ts : List T} (h : enc v = .ap f ts) :
    ∃ (g : Sym) (vs : List GroundTerm), v = .ctor g vs ∧ f = g ∧ ts = encTs vs := by
  cases v with
  | ctor g vs => rw [enc_ctor_kmf] at h; cases h; exact ⟨g, vs, rfl, rfl, rfl⟩
  | inj a b u => rw [enc_inj_form_kmf] at h; cases h
  | dv s l =>
    rcases enc_dv_cases_kkc s l with ⟨i, h'⟩ | ⟨b, h'⟩ | ⟨x, y, h'⟩ | h' <;> rw [h'] at h <;> cases h
  | map s es => rw [enc] at h; cases h
  | set s es => rw [enc] at h; cases h
  | list s es => rw [enc] at h; cases h

theorem enc_eq_ij_kmf {v : GroundTerm} {a b : Int} {t : T} (h : enc v = .ij a b t) :
    ∃ (a' b' : Srt) (u : GroundTerm), v = .inj a' b' u ∧ a = a' ∧ b = b' ∧ t = enc u := by
  cases v with
  | ctor g vs => rw [enc_ctor_kmf] at h; cases h
  | inj a' b' u => rw [enc_inj_form_kmf] at h; cases h; exact ⟨a', b', u, rfl, rfl, rfl, rfl⟩
  | dv s l =>
    rcases enc_dv_cases_kkc s l with ⟨i, h'⟩ | ⟨b, h'⟩ | ⟨x, y, h'⟩ | h' <;> rw [h'] at h <;> cases h
  | map s es => rw [enc] at h; cases h
  | set s es => rw [enc] at h; cases h
  | list s es => rw [enc] at h; cases h

theorem encTs_cons_kmf (v : GroundTerm) (vs : List GroundTerm) : encTs (v :: vs) = enc v :: encTs vs := by
  rw [encTs]

/-- A literal `kore.k` has matches itself only. -/
theorem matchF_lit (S : List (Int × Int)) {s : Srt} {l : Lit} {q : T} (h : encLit s l = some q)
    (a : T) (B : Bind) : matchF S q a B = some (if a = q then [B] else []) := by
  rcases encLit_some h with ⟨i, -, -, rfl⟩ | ⟨b, -, -, rfl⟩ | ⟨x, -, rfl⟩
  · exact matchF_iv S i a B
  · exact matchF_bv S b a B
  · exact matchF_tk S s x a B

/-! ## What the statements read of `c` -/

/-- A constructor's signature is the one a left side's context reads. -/
theorem lookupSig_patCtxAll_kmf {c : Semantics} {f : Sym} {k : CtorSig}
    (h : lookupSig c.ctorSigs f = some k) : lookupSig c.patCtxAll.heads f = some k :=
  lookupSig_append_some (lookupSig_append_some h)

/-- An open generator is a parameter symbol. -/
theorem isParam_of_lookupOpen_kmf {c : Semantics} {f : Sym} {k : ParamSig}
    (h : c.lookupOpen f = some k) : c.isParam f = true := by
  obtain ⟨hk, -, hn, -⟩ := c.lookupOpen_spec h
  rw [Semantics.isParam, Semantics.lookupParam_eq, List.find?_isSome]
  exact ⟨k, hk, by simp [hn]⟩

/-- A sorted constructor term whose head, as a pattern, is read as an application: the head is a
constructor and the arguments have the sorts of the pattern's arguments. -/
theorem sortOf_ctor_pat_kmf {c : Semantics} (hov : c.ovls = []) {vars : List Srt} {f : Sym}
    {ps : List Term} {vs : List GroundTerm} {s : Srt}
    (hp : sortOfTerm c.patCtxNF vars (.app f ps) = some s) (hv : c.sortOf (.ctor f vs) = some s)
    (hf : c.isCtor f = true ∨ c.isParam f = false) :
    c.isCtor f = true ∧ ∃ ss, sortsOfTerms c.patCtxNF vars ps = some ss ∧ c.sortsOf vs = some ss := by
  obtain ⟨k, -, hps, -⟩ := sortOfTerm_app.mp hp
  obtain ⟨k₂, hk₂, hps₂, -⟩ := sortOfTerm_app.mp (sortOfTerm_all_of_nf hp)
  have hargs : k.args = k₂.args := Option.some.inj ((sortsOfTerms_all_of_nf hps).symm.trans hps₂)
  rcases c.sortOf_ctor_iff.mp hv with ⟨k', hk', hvs, -⟩ | ⟨-, o, ho, -⟩ | ⟨hn, -, k', hk', -⟩
  · have : k₂ = k' := Option.some.inj (hk₂.symm.trans (lookupSig_patCtxAll_kmf hk'))
    subst this
    exact ⟨by simp [Semantics.isCtor, hk'], k.args, hps, by rw [hargs]; exact hvs⟩
  · simp [Semantics.lookupOvl, hov] at ho
  · rcases hf with hf | hf
    · simp [Semantics.isCtor, hn] at hf
    · rw [isParam_of_lookupOpen_kmf hk'] at hf; cases hf

theorem sortOf_dv_pat_kmf {c : Semantics} {vars : List Srt} {s' s : Srt} {l : Lit}
    (hp : sortOfTerm c.patCtxNF vars (.dv s' l) = some s) : c.sortOf (.dv s' l) = some s := by
  obtain ⟨h, rfl⟩ := sortOfTerm_dv.mp hp
  have h' : dvOK c.lib s l = true := h
  simp [Semantics.sortOf, h']

/-! ## Soundness -/

section
variable {c : Semantics} (hmc : MatchCtxO c) (hov : c.ovls = []) {vars : List Srt}
include hmc hov
set_option linter.unusedSectionVars false

mutual
/-- **`matchF` is sound.** A substitution `B'` that `match` gives at the encoding of the pattern
`p` and of a value `v` of `p`'s sort, from `B`: extends `B`, binds every variable of `p`, holds
encodings of values of the variables' sorts where `B` does, and under every `σ` that reads `B'`
the pattern denotes `v`. -/
theorem matchF_sound : ∀ {p : Term} {q : T} {s : Srt} {v : GroundTerm} {B B' : Bind} {M : Ms},
    encTerm c p = some q → noCb q = true → sortOfTerm c.patCtxNF vars p = some s →
    c.sortOf v = some s → litsV v = true → matchF (subsF c) q (enc v) B = some M → B' ∈ M →
    BindExt B B' ∧ (∀ i ∈ varOccs p, (lookF (i : Int) B').isSome = true) ∧
      (BindOK c vars B → BindOK c vars B') ∧ ∀ σ, BindRep c vars B' σ → PatVal c σ p v
  | .var i, q, s, v, B, B', M, hq, _, hp, hv, lv, hm, hB => by
    rw [encTerm_var_kmf] at hq; cases hq
    rw [matchF_vr] at hm; cases hm
    obtain ⟨h1, h2, -⟩ := bindVarF_mem hB
    have hs := sortOfTerm_var.mp hp
    refine ⟨h2, fun j hj => ?_, bindVarF_ok hs hv lv hB, fun σ hσ => .var (hσ.lookup h1 hv lv)⟩
    simp only [varOccs, List.mem_singleton] at hj
    subst hj; rw [h1]; rfl
  | .dv s' l, q, s, v, B, B', M, hq, _, hp, hv, lv, hm, hB => by
    rw [encTerm_dv_kmf] at hq
    rw [matchF_lit _ hq] at hm; cases hm
    split at hB
    · rename_i he
      simp only [List.mem_singleton] at hB
      subst hB
      have hl : litsV (.dv s' l) = true := by simp [litsV, hq]
      have : v = .dv s' l :=
        enc_inj hv (sortOf_dv_pat_kmf hp) lv hl (he.trans (enc_dv_of_encLit hq).symm)
      subst this
      exact ⟨BindExt.refl _, fun j hj => by simp [varOccs] at hj, id, fun σ _ => .dv⟩
    · cases hB
  | .inj a b p, q, s, v, B, B', M, hq, hcb, hp, hv, lv, hm, hB => by
    rw [encTerm_inj_kmf] at hq
    obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
    obtain ⟨hab, hp', rfl⟩ := sortOfTerm_inj.mp hp
    have hcb' : noCb q' = true := by simpa [noCb] using hcb
    obtain ⟨c₁, e₁, t, hv', hcase⟩ := matchF_ij_inv _ hm hB
    obtain ⟨a', b', u, rfl, rfl, rfl, rfl⟩ := enc_eq_ij_kmf hv'
    obtain ⟨ha'b', hu, hus, rfl⟩ := sortOf_inj_kel hv
    have lu : litsV u = true := by simpa [litsV] using lv
    rcases hcase with ⟨hac, hm'⟩ | ⟨hac, hle, hm'⟩
    · have : a = a' := Int.natCast_inj.mp hac
      subst this
      obtain ⟨h1, h2, h3, h4⟩ := matchF_sound hq' hcb' hp' hus lu hm' hB
      refine ⟨h1, h2, h3, fun σ hσ => ?_⟩
      have := PatVal.inj (a := a) (b := s) (h4 σ hσ)
      rwa [Det.injNormal_of_not_inj hu] at this
    · have hne : a' ≠ a := fun h => hac (by rw [h])
      rw [leqF_subsF hmc.trans] at hle
      simp only [Bool.or_eq_true, beq_iff_eq, hne, false_or] at hle
      have hw : c.sortOf (.inj a' a u) = some a := by
        simp [Semantics.sortOf, List.contains_iff_mem.mp hle, hu, hus]
      have lw : litsV (.inj a' a u) = true := by simpa [litsV] using lu
      rw [← enc_inj_form_kmf] at hm'
      obtain ⟨h1, h2, h3, h4⟩ := matchF_sound hq' hcb' hp' hw lw hm' hB
      exact ⟨h1, h2, h3, fun σ hσ => PatVal.inj (a := a) (b := s) (h4 σ hσ)⟩
  | .as p i, q, s, v, B, B', M, hq, hcb, hp, hv, lv, hm, hB => by
    rw [encTerm_as_kmf] at hq
    obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
    obtain ⟨hs, hp'⟩ := Exec.sortOfTerm_as hp
    have hcb' : noCb q' = true := by simpa [noCb] using hcb
    rw [matchF_as] at hm
    obtain ⟨M₁, hm₁, rfl⟩ := Option.map_eq_some_iff.mp hm
    obtain ⟨B₁, hB₁, hB⟩ := bindAfterF_mem hB
    obtain ⟨h1, h2, h3, h4⟩ := matchF_sound hq' hcb' hp' hv lv hm₁ hB₁
    obtain ⟨g1, g2, -⟩ := bindVarF_mem hB
    refine ⟨h1.trans g2, fun j hj => ?_, fun hok => bindVarF_ok hs hv lv hB (h3 hok),
      fun σ hσ => .as (h4 σ (hσ.of_ext g2)) (hσ.lookup g1 hv lv)⟩
    simp only [varOccs, List.mem_append, List.mem_singleton] at hj
    rcases hj with hj | rfl
    · exact g2.isSome (h2 j hj)
    · rw [g1]; rfl
  | .app f ps, q, s, v, B, B', M, hq, hcb, hp, hv, lv, hm, hB => by
    rw [encTerm_app_kmf] at hq
    rcases readApp_noCb_kmf hq hcb with ⟨qs, hqs, rfl, hf⟩ | ⟨o, as, rfl⟩
    · obtain ⟨ts, hv', hm'⟩ := matchF_ap_inv _ hm hB
      obtain ⟨g, vs, rfl, hfg, rfl⟩ := enc_eq_ap_kmf hv'
      have : f = g := Int.natCast_inj.mp hfg
      subst this
      obtain ⟨hc, ss, hps, hvs⟩ := sortOf_ctor_pat_kmf hov hp hv hf
      have hcb' : noCbL qs = true := by simpa [noCb] using hcb
      have lvs : litsVL vs = true := by simpa [litsV] using lv
      obtain ⟨h1, h2, h3, h4⟩ := matchTsF_sound hqs hcb' hps hvs lvs hm' hB
      exact ⟨h1, fun j hj => h2 j (by simpa [varOccs] using hj), h3,
        fun σ hσ => .ctor hc (h4 σ hσ)⟩
    · rw [matchF_hk] at hm; cases hm; cases hB
/-- `matchTs` is sound: the same of a list of patterns and a list of values of their sorts. -/
theorem matchTsF_sound : ∀ {ps : List Term} {qs : List T} {ss : List Srt} {vs : List GroundTerm}
    {B B' : Bind} {M : Ms},
    encTermsWith c encLit ps = some qs → noCbL qs = true → sortsOfTerms c.patCtxNF vars ps = some ss →
    c.sortsOf vs = some ss → litsVL vs = true → matchTsF (subsF c) qs (encTs vs) B = some M → B' ∈ M →
    BindExt B B' ∧ (∀ i ∈ varOccsList ps, (lookF (i : Int) B').isSome = true) ∧
      (BindOK c vars B → BindOK c vars B') ∧ ∀ σ, BindRep c vars B' σ → PatVals c σ ps vs
  | [], qs, ss, vs, B, B', M, hq, _, hp, hv, _, hm, hB => by
    cases encTerms_nil_kmf c hq
    cases sortsOfTerms_nil.mp hp
    cases Faithful.sortsOf_nil_eq hv
    rw [encTs, matchTsF_nil] at hm; cases hm
    simp only [List.mem_singleton] at hB
    subst hB
    exact ⟨BindExt.refl _, fun j hj => by simp [varOccsList] at hj, id, fun σ _ => .nil⟩
  | p :: ps, qs, ss, vs, B, B', M, hq, hcb, hp, hv, lv, hm, hB => by
    obtain ⟨q, qs', hq1, hq2, rfl⟩ := encTerms_cons_kmf c hq
    obtain ⟨s, ss', hp1, hp2, rfl⟩ := sortsOfTerms_cons.mp hp
    cases vs with
    | nil => simp [Semantics.sortsOf] at hv
    | cons v vs =>
      obtain ⟨s₁, ss₁, hv1, hv2, he⟩ := sortsOf_cons.mp hv
      cases he
      simp only [noCbL, Bool.and_eq_true] at hcb
      simp only [litsVL, Bool.and_eq_true] at lv
      rw [encTs_cons_kmf, matchTsF_cons] at hm
      cases hm₁ : matchF (subsF c) q (enc v) B with
      | none => rw [hm₁] at hm; cases hm
      | some ms =>
        rw [hm₁] at hm
        obtain ⟨B₁, hB₁, M₁, hm₂, hB'⟩ := matchKF_mem _ hm hB
        obtain ⟨h1, h2, h3, h4⟩ := matchF_sound hq1 hcb.1 hp1 hv1 lv.1 hm₁ hB₁
        obtain ⟨g1, g2, g3, g4⟩ := matchTsF_sound hq2 hcb.2 hp2 hv2 lv.2 hm₂ hB'
        refine ⟨h1.trans g1, fun j hj => ?_, fun hok => g3 (h3 hok),
          fun σ hσ => .cons (h4 σ (hσ.of_ext g1)) (g4 σ hσ)⟩
        simp only [varOccsList, List.mem_append] at hj
        rcases hj with hj | hj
        · exact g1.isSome (h2 j hj)
        · exact g2 j hj
end

/-! ## Completeness -/

mutual
/-- **`matchF` is complete.** Where the pattern `p` denotes `v` under a well-sorted `σ` and `B`
agrees with `σ`, `match` at the encodings gives exactly one substitution, which extends `B`,
agrees with `σ` and binds every variable of `p`. -/
theorem matchF_complete : ∀ {p : Term} {q : T} {s : Srt} {v : GroundTerm} {σ : Subst} {B : Bind},
    encTerm c p = some q → noCb q = true → sortOfTerm c.patCtxNF vars p = some s →
    c.WellSorted vars σ → PatVal c σ p v → BindAgree B σ →
    ∃ B', matchF (subsF c) q (enc v) B = some [B'] ∧ BindAgree B' σ ∧ BindExt B B' ∧
      ∀ i ∈ varOccs p, (lookF (i : Int) B').isSome = true
  | .var i, q, s, v, σ, B, hq, _, _, _, h, hB => by
    rw [encTerm_var_kmf] at hq; cases hq
    cases h with
    | var hi =>
      obtain ⟨B', h1, h2, h3, h4⟩ := bindVarF_agree hB hi
      refine ⟨B', by rw [matchF_vr, h1], h2, h3, fun j hj => ?_⟩
      simp only [varOccs, List.mem_singleton] at hj
      subst hj; rw [h4]; rfl
  | .dv s' l, q, s, v, σ, B, hq, _, _, _, h, hB => by
    rw [encTerm_dv_kmf] at hq
    cases h with
    | dv =>
      refine ⟨B, ?_, hB, BindExt.refl _, fun j hj => by simp [varOccs] at hj⟩
      rw [matchF_lit _ hq, enc_dv_of_encLit hq]
      simp only [↓reduceIte]
  | .inj a b p, q, s, v, σ, B, hq, hcb, hp, hσ, h, hB => by
    rw [encTerm_inj_kmf] at hq
    obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
    obtain ⟨hab, hp', rfl⟩ := sortOfTerm_inj.mp hp
    have hcb' : noCb q' = true := by simpa [noCb] using hcb
    cases h with
    | inj h =>
      rename_i w
      have hw : c.sortOf w = some a := Det.patVal_sortedAll hmc hσ h hp'
      obtain ⟨B', h1, h2, h3, h4⟩ := matchF_complete hq' hcb' hp' hσ h hB
      refine ⟨B', ?_, h2, h3, fun j hj => h4 j (by simpa [varOccs] using hj)⟩
      cases hi : w.isInj with
      | false =>
        rw [Det.injNormal_of_not_inj hi, enc_inj_form_kmf, matchF_ij_ij]
        simp only [↓reduceIte]
        exact h1
      | true =>
        cases w with
        | inj a' x u =>
          obtain ⟨ha', -, -, rfl⟩ := sortOf_inj_kel hw
          have hne : a' ≠ a := fun h => hmc.irrefl a (h ▸ ha')
          have hne' : ¬ ((a : Int) = (a' : Int)) := fun h => hne (Int.natCast_inj.mp h).symm
          have hle : leqF (a' : Int) (a : Int) (subsF c) = true := by
            rw [leqF_subsF hmc.trans]; simp [ha']
          show matchF (subsF c) (.ij a s q') (enc (.inj a' s u)) B = some [B']
          rw [enc_inj_form_kmf, matchF_ij_ij]
          simp only [hne', ↓reduceIte, hle]
          rw [← enc_inj_form_kmf]
          exact h1
        | _ => cases hi
  | .as p i, q, s, v, σ, B, hq, hcb, hp, hσ, h, hB => by
    rw [encTerm_as_kmf] at hq
    obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
    obtain ⟨-, hp'⟩ := Exec.sortOfTerm_as hp
    have hcb' : noCb q' = true := by simpa [noCb] using hcb
    cases h with
    | as h hi =>
      obtain ⟨B₁, h1, h2, h3, h4⟩ := matchF_complete hq' hcb' hp' hσ h hB
      obtain ⟨B', g1, g2, g3, g4⟩ := bindVarF_agree h2 hi
      refine ⟨B', ?_, g2, h3.trans g3, fun j hj => ?_⟩
      · rw [matchF_as, h1]; simp [bindAfterF, g1]
      · simp only [varOccs, List.mem_append, List.mem_singleton] at hj
        rcases hj with hj | rfl
        · exact g3.isSome (h4 j hj)
        · rw [g4]; rfl
  | .app f ps, q, s, v, σ, B, hq, hcb, hp, hσ, h, hB => by
    rw [encTerm_app_kmf] at hq
    cases h with
    | ctor hc hs =>
      rename_i vs
      rw [readApp_ctor_kmf hc] at hq
      obtain ⟨qs, hqs, rfl⟩ := Option.map_eq_some_iff.mp hq
      obtain ⟨k, -, hps, -⟩ := sortOfTerm_app.mp hp
      have hcb' : noCbL qs = true := by simpa [noCb] using hcb
      obtain ⟨B', h1, h2, h3, h4⟩ := matchTsF_complete hqs hcb' hps hσ hs hB
      refine ⟨B', ?_, h2, h3, fun j hj => h4 j (by simpa [varOccs] using hj)⟩
      rw [enc_ctor_kmf, matchF_ap_ap]
      simp only [↓reduceIte]
      exact h1
    | hook hp' hs hv =>
      have := readApp_coll_kmf (hmc.patHooks f (List.contains_iff_mem.mp hp')) (collSymOf_pat_kmf (.inl hp')) hq
      rw [this] at hcb; cases hcb
    | coll hc hp' hs hv =>
      have := readApp_coll_kmf hc (collSymOf_pat_kmf (.inr hp')) hq
      rw [this] at hcb; cases hcb
    | ovl hc ho hs hv =>
      simp [Semantics.isOvl, Semantics.lookupOvl, hov] at ho
/-- `matchTs` is complete: the same of a list of patterns. -/
theorem matchTsF_complete : ∀ {ps : List Term} {qs : List T} {ss : List Srt} {vs : List GroundTerm}
    {σ : Subst} {B : Bind},
    encTermsWith c encLit ps = some qs → noCbL qs = true → sortsOfTerms c.patCtxNF vars ps = some ss →
    c.WellSorted vars σ → PatVals c σ ps vs → BindAgree B σ →
    ∃ B', matchTsF (subsF c) qs (encTs vs) B = some [B'] ∧ BindAgree B' σ ∧ BindExt B B' ∧
      ∀ i ∈ varOccsList ps, (lookF (i : Int) B').isSome = true
  | [], qs, ss, vs, σ, B, hq, _, _, _, h, hB => by
    cases encTerms_nil_kmf c hq
    cases h with
    | nil =>
      exact ⟨B, by rw [encTs, matchTsF_nil], hB, BindExt.refl _,
        fun j hj => by simp [varOccsList] at hj⟩
  | p :: ps, qs, ss, vs, σ, B, hq, hcb, hp, hσ, h, hB => by
    obtain ⟨q, qs', hq1, hq2, rfl⟩ := encTerms_cons_kmf c hq
    obtain ⟨s, ss', hp1, hp2, rfl⟩ := sortsOfTerms_cons.mp hp
    simp only [noCbL, Bool.and_eq_true] at hcb
    cases h with
    | cons h hs =>
      obtain ⟨B₁, h1, h2, h3, h4⟩ := matchF_complete hq1 hcb.1 hp1 hσ h hB
      obtain ⟨B', g1, g2, g3, g4⟩ := matchTsF_complete hq2 hcb.2 hp2 hσ hs h2
      refine ⟨B', ?_, g2, h3.trans g3, fun j hj => ?_⟩
      · rw [encTs_cons_kmf, matchTsF_cons, h1]
        exact matchKF_single _ g1
      · simp only [varOccsList, List.mem_append] at hj
        rcases hj with hj | hj
        · exact g3.isSome (h4 j hj)
        · exact g4 j hj
end

/-! ## The substitution a match gives, as a well-sorted `σ` -/

/-- **The bindings are well sorted.** A substitution `matchTs` gives from the empty one, at
patterns that bind every variable, is read by a `σ` that gives every variable a value of its sort
and under which the patterns denote the values. -/
theorem matchTsF_wellSorted {ps : List Term} {qs : List T} {ss : List Srt} {vs : List GroundTerm}
    {B' : Bind} {M : Ms} (hq : encTermsWith c encLit ps = some qs) (hcb : noCbL qs = true)
    (hp : sortsOfTerms c.patCtxNF vars ps = some ss) (hv : c.sortsOf vs = some ss)
    (lv : litsVL vs = true) (hb : binds vars.length (varOccsList ps) = true)
    (hm : matchTsF (subsF c) qs (encTs vs) [] = some M) (hB : B' ∈ M) :
    ∃ σ, BindRep c vars B' σ ∧ c.WellSorted vars σ ∧ PatVals c σ ps vs := by
  obtain ⟨-, h2, h3, h4⟩ := matchTsF_sound hmc hov hq hcb hp hv lv hm hB
  obtain ⟨σ, hσ⟩ := (h3 (bindOK_nil c vars)).rep
  refine ⟨σ, hσ, fun i s hs => ?_, h4 σ hσ⟩
  have hi : i < vars.length := by
    rcases Nat.lt_or_ge i vars.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hs; cases hs
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (h2 i (Exec.binds_all hb i hi))
  obtain ⟨j, w, s', hij, h5, -, h6, h7, -⟩ := hσ _ _ ht
  have : i = j := Int.natCast_inj.mp hij
  subst this
  rw [hs] at h6; cases h6
  exact ⟨w, h5, h7⟩

/-- The same of one pattern (a rule's left side). -/
theorem matchF_wellSorted {p : Term} {q : T} {s : Srt} {v : GroundTerm} {B' : Bind} {M : Ms}
    (hq : encTerm c p = some q) (hcb : noCb q = true)
    (hp : sortOfTerm c.patCtxNF vars p = some s) (hv : c.sortOf v = some s)
    (lv : litsV v = true) (hb : binds vars.length (varOccs p) = true)
    (hm : matchF (subsF c) q (enc v) [] = some M) (hB : B' ∈ M) :
    ∃ σ, BindRep c vars B' σ ∧ c.WellSorted vars σ ∧ PatVal c σ p v := by
  obtain ⟨-, h2, h3, h4⟩ := matchF_sound hmc hov hq hcb hp hv lv hm hB
  obtain ⟨σ, hσ⟩ := (h3 (bindOK_nil c vars)).rep
  refine ⟨σ, hσ, fun i s hs => ?_, h4 σ hσ⟩
  have hi : i < vars.length := by
    rcases Nat.lt_or_ge i vars.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hs; cases hs
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (h2 i (Exec.binds_all hb i hi))
  obtain ⟨j, w, s', hij, h5, -, h6, h7, -⟩ := hσ _ _ ht
  have : i = j := Int.natCast_inj.mp hij
  subst this
  rw [hs] at h6; cases h6
  exact ⟨w, h5, h7⟩

end

/-! ## At `d₀ d` -/

/-- A substitution that gives the variables of a list that holds every variable values of their
sorts is well sorted: what `Fails` and `NotApplies` state of a `σ` (`WellSortedAt` at the left
side's variables) is what `matchF_complete` takes, where the left side binds every variable. -/
theorem wellSorted_of_at_kmf {c : Semantics} {vars : List Srt} {is occs : List Nat} {σ : Subst}
    (hσ : c.WellSortedAt vars is σ) (hb : binds vars.length occs = true) (hsub : ∀ i ∈ occs, i ∈ is) :
    c.WellSorted vars σ := by
  intro i s hs
  have hi : i < vars.length := by
    rcases Nat.lt_or_ge i vars.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hs; cases hs
  exact hσ i (hsub i (Exec.binds_all hb i hi)) s hs

/-- What the statements read of `d₀ d`, from `execReady d` and `encodable d`. -/
theorem matchCtx_d₀ {d : Semantics} (hx : CExec.execReady d = true) (he : encodable d = true) :
    MatchCtxO (d₀ d) ∧ (d₀ d).ovls = [] := by
  have hx' : CExec.execReady (d₀ d) = true := (CExec.execReady_withHooks d _).trans hx
  simp only [CExec.execReady, Bool.and_eq_true] at hx'
  exact ⟨Exec.matchCtxO_of hx'.1.1.1.1.2, (encodable_facts (d₀_facts_kkv hx he).2.2.2).1⟩

set_option smartUnfolding false in
/-- A pattern's encoding at `d₀ d` is its encoding at `d`. -/
theorem encTerm_d₀ (d : Semantics) (p : Term) : encTerm (d₀ d) p = encTerm d p := rfl

set_option smartUnfolding false in
theorem encTermsWith_d₀ (d : Semantics) (ps : List Term) :
    encTermsWith (d₀ d) encLit ps = encTermsWith d encLit ps := rfl

/-- `kore.k`'s subsort table of `d₀ d` is that of `d`. -/
theorem subsF_d₀ (d : Semantics) : subsF (d₀ d) = subsF d := rfl

/-- Under `encodable d`, a list of terms of `d`'s rules and clauses has the encodings `encDef`
writes (`encT`). -/
theorem encTerms_of_encodable {d : Semantics} (h : encodable d = true) : ∀ {ts : List Term},
    (∀ t ∈ ts, t ∈ lhsTerms d ++ rhsTerms d ++ ensTerms d) →
    encTermsWith d encLit ts = some (ts.map (encT d))
  | [], _ => by rw [encTermsWith]; rfl
  | t :: ts, hts => by
    have h1 : encTermWith d encLit t = some (encT d t) := encTerm_of_encodable h (hts t (by simp))
    have h2 := encTerms_of_encodable h (ts := ts) fun t' ht' => hts t' (by simp [ht'])
    rw [encTermsWith, h1, h2]; rfl

/-- The sort premise of a clause's patterns, from `execReady d`: the first conjunct of
`clauseSorted` for a function of `d`, the sort predicates' own text for a generated one. -/
theorem clausePats_d₀ {d : Semantics} (hx : CExec.execReady d = true) (he : encodable d = true)
    {fn : Fn} (hfn : fn ∈ (d₀ d).allFns) {cl : Clause} (hcl : cl ∈ fn.clauses) :
    sortsOfTerms (d₀ d).patCtxNF cl.vars cl.pats = some fn.args :=
  CExec.clausePats_nf (d₀_facts_kkv hx he).1 (matchCtx_d₀ hx he).1 hfn hcl

/-- The sort premise of a rule's left side, from `execReady d`. -/
theorem rulePat_d₀ {d : Semantics} (hx : CExec.execReady d = true) (he : encodable d = true)
    {r : Rule} (hr : r ∈ (d₀ d).rules) :
    sortOfTerm (d₀ d).patCtxNF r.vars r.lhs = some topCellSort :=
  CExec.rulePat_nf (d₀_facts_kkv hx he).1 (matchCtx_d₀ hx he).1 hr

end KCore.KK
