/-
  The rule of construct fixture e3-ml-rule-rhs-top (`rule <k> go => #Top ... </k>`), read by
  `Parse.parse` from K 7.1.337 kompile's KORE (`f2-examples/heldrhstop.kompile.kore`), its tie
  through the cut, and its successors. Run from the package root, after the library:
  `lake env lean -j1 test/TieRuleRhsTop.lean`.

  kompile writes the right side as `<k>(append(\top{SortK{}}(), _DotVar1))`: `#Top` at the sort K, as
  the first argument of K's `append`, R := _DotVar1 the rest of the k cell.
  - The reading (`read`, `rz_shape`, `coreOK`, `fnHypH`): the rule `go ~> R => ?Z ++ R` with one
    existential variable Z:K (`exs`), `post` `\top` (Z is in `\top` always, so the cut adds no
    condition). `coreOK` holds (append is a held symbol, `Semantics.appendHeldX`, so Z is held), and
    `FnHyp` for every hook interpretation H: no obligation is named, no rule or clause has a
    `requires` variable its left side leaves open, no open generator.
  - The tie (`left_eq`, `right_text`, `right_tie`, `tie`): `ruleRight c rz` is
    `∃Z:K. (K[Z] ∧ ⊤)`, K the context `<generatedTop>(<k>(append(·, R)), counter)` and ⊤ the `ensures`
    `\top{GeneratedTopCell}`; its conjunction is the theorem's `K[Z] ∧ ⊤ ∧ q` with q := ⊤ written
    twice (`dup_iff`), and `\top{C}` is the membership of Z in `\top{K}` (`MemOf.top`, each sort
    pattern a sort constant, which does not hold the variable `\top` binds), so `rule_cut_mem` gives
    the text's right side `K[\top{K}] ∧ ⊤`; every element of `\top{K}` is in K (`top_inh`).
  - The successors, for every H, at x = `<k> go ~> R </k>` for a value R of K (counter 0), each
    through the reading (C7 form (a); the families Γstep and kNoJunk): `step` (x steps to `<k> z ++ R </k>` for
    every value z of K, `kcatRT z R` the sequence z followed by R), with the named instances
    `step_dot` (z = `.K`, `<k> R </k>`) and `step_self` (z = `go`, x itself); `step_iff` (`Step`
    reaches exactly those); `exact_y` (by `exact_hyp`: y is a successor of x in some model of
    `Γc ∪ Γstep` exactly where y is some `<k> z ++ R </k>`). That each is a possible successor is
    the sentence's instance Z := z; that no other value is one rests on the step's closure and on
    K's no-junk item of Γ (`append` held, `HeldBack`, KcoreSpec/AppendHeldBack.lean).
  - The value of append (`eval_append`), for every H: at values z, R of K, `append(z, R)` evaluates to
    `kcatRT z R`, by induction on z through append's two clauses (`f(dotk, T) = T`,
    `f(kseq(I, KS), T) = kseq(I, f(KS, T))`); every value of K is `.K` or a `kseq` of a value of
    KItem and a value of K (`k_shape`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore KCore.Faithful KoreAML ML

namespace TieRuleRhsTop

kore_term kore from "f2-examples/heldrhstop.kompile.kore"
definition_of defn from "f2-examples/heldrhstop.kompile.kore"
noncomputable abbrev c : Semantics := defn.sem

def exp : Srt := 32
def ctrS : Srt := 19
def kCell : KCore.Sym := 383
def symGo : KCore.Sym := 389
def symApp : KCore.Sym := 390

example : c.sortName exp = "Exp" ∧ c.sortName Srt.k = "K" ∧ c.sortName ctrS = "GeneratedCounterCell" ∧
    c.symName kCell = "Lbl'-LT-'k'-GT-'" ∧ c.symName symGo = "Lblgo" ∧ c.symName symApp = "append" := by
  decide +kernel

/-! ## The reading -/

/-- `<generatedTop>(<k>(kseq(inj{Exp,KItem}(go), V0)), V1)`. -/
def lhsT : Term := .app topLabel [.app kCell [.app kseq [.inj exp Srt.kitem (.app symGo []), .var 0]], .var 1]
/-- `<generatedTop>(<k>(append(Z, V0)), V1)`, Z the variable 2. -/
def rhsT : Term := .app topLabel [.app kCell [.app symApp [.var 2, .var 0]], .var 1]

noncomputable def rz : Rule := c.rules[0]'(by decide +kernel)

/-- The reader reads the text's one rule as `go ~> V0 => ?Z ++ V0`, Z:K existential, `post` `\top`. -/
theorem read : c.rules = [rz] := by
  have h : c.rules.length = 1 := by decide +kernel
  match hr : c.rules, h with
  | [r], _ => simp only [rz, hr, List.getElem_cons_zero]

theorem rz_shape : rz.vars = [Srt.k, ctrS, Srt.k] ∧ rz.lhs = lhsT ∧ rz.rhs = rhsT ∧ rz.req = none ∧
    rz.ens = none ∧ rz.exs = [2] ∧ rz.pre = .top ∧ rz.post = .top :=
  ⟨by decide +kernel, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 1000000 in
/-- **Admitted**: the definition with the rule `go => ?Z ++ R` has `coreOK`. -/
theorem coreOK : c.coreOK = true := by decide_cheap

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
/-- No rule and no clause has a variable of its `requires` that its left side does not bind. -/
theorem reqOpen_nil : rz.reqOpen = false ∧ ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.reqOpen = false := by
  decide +kernel
theorem term_named : c.rankObligations [] ++ c.decObligationsL = [] := by decide +kernel
theorem total_named : c.totalObligationsRP [] [] = [] := by decide +kernel
theorem agree_named : c.agreeObligationsI = [] := by decide +kernel
theorem match_named : c.matchObligationsL = ([] : List (Nat × Nat)) := by decide +kernel

noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem rulesH (H : HookParams) : (cH H).rules = [rz] := read
theorem sortOfH (H : HookParams) (v : GroundTerm) : (cH H).sortOf v = c.sortOf v := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]

/-- The obligations, for every H: none is named, no rule or clause needs a witness and no
parameter is an open generator. -/
theorem obl_nil (H : HookParams) : FnObligations (cH H) [] [] := by
  have h1 : (cH H).rankObligations [] ++ (cH H).decObligationsL = [] := by
    rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact term_named
  have h2 : (cH H).totalObligationsRP [] [] = [] := (Semantics.totalObligationsRP_withHooks _ H _ _).trans total_named
  have h3 : (cH H).agreeObligationsI = [] := (Det.Semantics.agreeObligationsI_withHooks _ H).trans agree_named
  have h4 : (cH H).matchObligationsL = [] := (Det.Semantics.matchObligationsL_withHooks _ H).trans match_named
  exact ⟨fun f hf => by rw [h1] at hf; exact absurd hf List.not_mem_nil,
   fun f hf => by rw [h2] at hf; exact absurd hf List.not_mem_nil,
   fun f hf => by rw [h3] at hf; exact absurd hf List.not_mem_nil,
   fun p hp => by rw [h4] at hp; exact absurd hp List.not_mem_nil,
   openDecided_of_plain (fun r hr => by
      rw [rulesH, List.mem_singleton] at hr; subst hr; simp [Rule.needsWitness, reqOpen_nil.1])
    (fun fn hfn cl hcl => by simp [Clause.needsWitness, reqOpen_nil.2 fn hfn cl hcl]),
   openLaws_of_plain noRaw⟩

/-- **`FnHyp` for every H**: no obligation is named. -/
theorem fnHypH (H : HookParams) : FnHyp (cH H) :=
  fnHyp_withHooks coreOK (Semantics.rightHeld_of_valued (by decide +kernel)) H ParamsTotal.nil (obl_nil H)

theorem fnDetH (H : HookParams) : FnDet (cH H) := (fnModel_of_fnHyp (coreOKH H) (fnHypH H)).1

/-! ## The tie through the cut -/

def topC : Kore.KSort := srt "GeneratedTopCell"
def S : Kore.KSort := srt "K"
def z : Kore.EVar := evar "VarV2" S
def E : Kore.Pattern := .top topC
/-- The context of Z: `<generatedTop>(<k>(append(·, V0)), V1)`. -/
def K : KoreCutCtx :=
  .app ⟨⟨"Lbl'-LT-'generatedTop'-GT-'"⟩⟩ [] []
    (.app ⟨⟨"Lbl'-LT-'k'-GT-'"⟩⟩ [] [] (.app ⟨⟨"append"⟩⟩ [] [] .hole [ev "VarV0" S]) [])
    [ev "VarV1" (srt "GeneratedCounterCell")]

/-- The theorem's right pattern: the right side with `\top{K}` in Z's position. -/
def right : Kore.Pattern := .and topC [K.fill (.top S), E]

/-- `ruleRight`: Z bound over the right side and the `ensures` `\top`, `post` writing nothing. -/
theorem left_eq : ruleRight c rz = .exist topC z (.and topC [K.fill (.var (.evar z)), E]) := by
  decide +kernel

/-- The text's spelling of the canonical names of the rule's variables. -/
def spell (n : String) (_ : Kore.KSort) : String :=
  if n == "VarV0" then "Var'Unds'DotVar1" else if n == "VarV1" then "Var'Unds'DotVar0" else n

/-- The `\rewrites` axiom at the place i of the text's last module: its left and right arguments. -/
def rewritesAt (k : Kore.Definition) (i : Nat) : Option (Kore.Pattern × Kore.Pattern) :=
  match k.modules.getLast?.bind (·.sentences[i]?) with
  | some (.axiom a) => match a.pattern with
    | .rewrites _ l r => some (l, r)
    | _ => none
  | _ => none

theorem right_text : some (renVars spell (fun n _ => n) right) = (rewritesAt kore 206).map (·.2) := by
  decide +kernel

theorem right_tie (r : Kore.Pattern) (h : (rewritesAt kore 206).map (·.2) = some r) :
    tr ⟨tableOf [] r, []⟩ r = tr ⟨tableOf [] right, []⟩ right := by
  have hr : r = renVars spell (fun n _ => n) right := by
    have := right_text; rw [h] at this; exact (Option.some.inj this).symm
  rw [hr]
  exact tr_occurrence_order spell (fun n _ => n) [] [] right (by decide +kernel)

/-- A conjunct written twice is written once. -/
theorem dup_iff {M : Type} {I : Interpretation KoreAML.Sym M} (ctx : Ctx) (C : Kore.KSort)
    (x y : Kore.Pattern) (e : Valuation M) (m : M) :
    (tr ctx (.and C [x, y, y])).interpret I e m ↔ (tr ctx (.and C [x, y])).interpret I e m := by
  simp only [tr, trAndList, interp_sAnd, and_self]

/-- Every element of `\top{S}` is in S, where the sort pattern is a sort constant. -/
theorem top_inh {M : Type} {I : Interpretation KoreAML.Sym M} (hD : DefOK I) {ctx : Ctx} {e : Valuation M}
    {σ : M} (hS : ∀ a, (trSort ctx.vars S).interpret I e a ↔ a = σ) (a : M)
    (h : (tr ctx (.top S)).interpret I e a) : Inh I σ a := by
  simp only [tr] at h
  rw [interp_sTop hD (by unfold S; rw [trSort_srt]; rfl)] at h
  exact (interp_inhOf_of hS).mp h

/-- **`rule_cut_mem` at the fixture**: `ruleRight c rz` is the right side with `\top{K}` in Z's
position, under the theorem's premises at a table without aliases; the membership is `MemOf.top`. -/
theorem tie {M : Type} {I : Interpretation KoreAML.Sym M} [Inhabited M] (hD : DefOK I)
    (tbl : VarTable) (e : Valuation M) {σ σ' : M}
    (hsides : K.SidesNoRead I ⟨tbl, []⟩ (tbl.ev (evarKey z)))
    (hφ : NoReadCut I (tbl.ev (evarKey z)) (tr ⟨tbl, []⟩ (.top S)))
    (hE : NoReadCut I (tbl.ev (evarKey z)) (tr ⟨tbl, []⟩ E))
    (hSz : NoReadCut I (tbl.ev (evarKey z)) (trSort tbl S))
    (hCz : NoReadCut I (tbl.ev (evarKey z)) (trSort tbl topC))
    (hS : ∀ a, (trSort tbl S).interpret I e a ↔ a = σ)
    (hC : ∀ a, (trSort tbl topC).interpret I e a ↔ a = σ')
    (hout : ∀ m, (tr ⟨tbl, []⟩ (K.fill (.top S))).interpret I e m → Inh I σ' m) (m : M) :
    (tr ⟨tbl, []⟩ (ruleRight c rz)).interpret I e m ↔ (tr ⟨tbl, []⟩ right).interpret I e m := by
  have hq : MemOf I ⟨tbl, []⟩ e (tbl.ev (evarKey z)) σ σ' E (.top S) :=
    MemOf.top (ctx := ⟨tbl, []⟩) hSz hCz hS hC hD (by unfold S; rw [trSort_srt]; rfl)
      (by unfold topC; rw [trSort_srt]; rfl)
  have hcut := rule_cut_mem hD ⟨tbl, []⟩ K rfl S topC z rfl (.top S) E E e hsides hφ hE hSz hS hq
    (fun a ha => top_inh hD hS a ha) hout m
  rw [left_eq]
  refine Iff.trans ?_ hcut
  show (sExists (tbl.ev (evarKey z)) (trSort tbl S) (tr ⟨tbl, []⟩ (.and topC [K.fill (.var (.evar z)), E]))).interpret I e m ↔
    (sExists (tbl.ev (evarKey z)) (trSort tbl S) (tr ⟨tbl, []⟩ (.and topC [K.fill (.var (.evar z)), E, E]))).interpret I e m
  rw [interp_sExists, interp_sExists]
  exact exists_congr fun x => and_congr_right' (dup_iff _ _ _ _ _ _).symm

/-! ## The value of `append` -/

/-- The K sequence z followed by r: z's items before r, where z is a `kseq` sequence. -/
def kcatRT : GroundTerm → GroundTerm → GroundTerm
  | .ctor f [i, ks], r => if f = kseq then .ctor kseq [i, kcatRT ks r] else r
  | _, r => r

theorem kcatRT_dot (r : GroundTerm) : kcatRT (.ctor dotk []) r = r := by simp [kcatRT]
theorem kcatRT_kseq (i ks r : GroundTerm) : kcatRT (.ctor kseq [i, ks]) r = .ctor kseq [i, kcatRT ks r] := by
  simp [kcatRT]

def kseqSigRT : KCore.CtorSig := ⟨kseq, [Srt.kitem, Srt.k], Srt.k⟩
def dotkSigRT : KCore.CtorSig := ⟨dotk, [], Srt.k⟩

theorem ctorK : ∀ k ∈ c.ctorSigs, k.result = Srt.k → k = kseqSigRT ∨ k = dotkSigRT := by decide +kernel
theorem ovlK : ∀ o ∈ c.ovls, o.sig.result ≠ Srt.k := by decide +kernel
theorem subK : ∀ p ∈ c.subsorts, p.2 ≠ Srt.k := by decide +kernel
theorem collK : c.collOf Srt.k = none := by decide +kernel
theorem dvK (lit : Lit) : dvOK c.lib Srt.k lit = false := by
  have h : (c.lib.carrier Srt.k == Srt.int) = false ∧ (c.lib.carrier Srt.k == Srt.bool) = false ∧
      (c.lib.carrier Srt.k == Srt.kconfigVar) = false ∧ (c.lib.carrier Srt.k == Srt.string) = false ∧
      (c.lib.carrier Srt.k == Srt.bytes) = false ∧ (c.lib.carrier Srt.k == Srt.float) = false ∧
      c.lib.carrier Srt.k ∉ c.lib.tokenSorts ∧ c.lib.carrier Srt.k ∉ c.lib.byteSorts := by
    decide +kernel
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  cases lit <;> simp [dvOK, h1, h2, h3, h4, h5, h6, h7, h8]

/-- **Every value of K is `.K` or a `kseq`** of a value of KItem and a value of K. -/
theorem k_shape {v : GroundTerm} (h : c.sortOf v = some Srt.k) :
    v = .ctor dotk [] ∨ ∃ i ks, v = .ctor kseq [i, ks] ∧ c.sortOf i = some Srt.kitem ∧ c.sortOf ks = some Srt.k := by
  cases v with
  | ctor f ts =>
    simp only [Semantics.sortOf] at h
    cases hl : lookupSig c.ctorSigs f with
    | some k =>
      rw [hl] at h
      simp only at h
      split at h
      · rename_i hts
        have hk := Option.some.inj h
        obtain ⟨hkm, rfl⟩ := lookupSig_spec hl
        have hts' := beq_iff_eq.mp hts
        have hlen := KK.sortsOf_length_kct hts'
        rcases ctorK k hkm hk with rfl | rfl
        · right
          change c.sortsOf ts = some [Srt.kitem, Srt.k] at hts'
          change ts.length = 2 at hlen
          obtain ⟨i, ks, rfl⟩ : ∃ i ks, ts = [i, ks] := by
            match ts, hlen with
            | [i, ks], _ => exact ⟨i, ks, rfl⟩
          obtain ⟨hi, hks⟩ := OvlLaws.sortsOf_cons_iff.mp hts'
          exact ⟨i, ks, rfl, hi, (OvlLaws.sortsOf_cons_iff.mp hks).1⟩
        · left
          change c.sortsOf ts = some [] at hts'
          rw [sortsOf_nil_eq hts']
          rfl
      · cases h
    | none =>
      rw [hl] at h
      simp only at h
      cases ho : c.lookupOvl f with
      | some o =>
        rw [ho] at h
        simp only at h
        split at h
        · exact absurd (Option.some.inj h) (ovlK o (List.mem_of_find?_eq_some ho))
        · cases h
      | none =>
        rw [ho] at h
        simp only at h
        cases hp : c.lookupOpen f with
        | some k =>
          have : k.raw = true ∧ k ∈ c.params := by
            unfold Semantics.lookupOpen at hp
            split at hp
            · have h' := List.find?_some hp
              simp only [Bool.and_eq_true] at h'
              exact ⟨h'.1, List.mem_of_find?_eq_some hp⟩
            · cases hp
          exact absurd (noRaw k this.2) (by rw [this.1]; decide)
        | none => rw [hp] at h; cases h
  | inj a b w =>
    simp only [Semantics.sortOf] at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, List.contains_iff_mem] at hc
      exact absurd rfl (subK _ hc.1.1)
    · cases h
  | dv s lit =>
    obtain ⟨hok, rfl⟩ := sortOf_dv.mp h
    rw [dvK] at hok; cases hok
  | map s es =>
    obtain ⟨k, vs, hk, -, -, -, rfl⟩ := c.sortOf_map_inv h
    rw [collK] at hk; cases hk
  | set s es =>
    simp only [Semantics.sortOf] at h
    split at h
    · rename_i hk _
      split at h
      · cases h; rw [collK] at hk; cases hk
      · cases h
    · cases h
  | list s es =>
    simp only [Semantics.sortOf] at h
    split at h
    · rename_i hk _
      split at h
      · cases h; rw [collK] at hk; cases hk
      · cases h
    · cases h

theorem kseq_sort {i ks : GroundTerm} (hi : c.sortOf i = some Srt.kitem) (hks : c.sortOf ks = some Srt.k) :
    c.sortOf (.ctor kseq [i, ks]) = some Srt.k := by
  have hl : lookupSig c.ctorSigs kseq = some kseqSigRT := by decide +kernel
  simp only [Semantics.sortOf, hl, Semantics.sortsOf, hi, hks]
  rfl

/-- `kcatRT z r` is a value of K where z and r are. -/
theorem kcatRT_sort : ∀ (n : Nat) (z r : GroundTerm), sizeOf z ≤ n → c.sortOf z = some Srt.k →
    c.sortOf r = some Srt.k → c.sortOf (kcatRT z r) = some Srt.k := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro z r hle hz hr
  rcases k_shape hz with rfl | ⟨i, ks, rfl, hi, hks⟩
  · rw [kcatRT_dot]; exact hr
  · rw [kcatRT_kseq]
    exact kseq_sort hi (ih _ (Nat.lt_of_lt_of_le (by simp; omega) hle) ks r (Nat.le_refl _) hks hr)

/-- append's function and its two clauses. -/
noncomputable def fnA : Fn := (c.lookupFn symApp).get (by decide +kernel)
theorem lookupFnA : c.lookupFn symApp = some fnA := by unfold fnA; simp
noncomputable def cdA : Clause := fnA.clauses[0]'(by decide +kernel)
noncomputable def ckA : Clause := fnA.clauses[1]'(by decide +kernel)

theorem fnA_clauses : fnA.clauses = [cdA, ckA] := by
  have h : fnA.clauses.length = 2 := by decide +kernel
  match hc : fnA.clauses, h with
  | [a, b], _ => simp only [cdA, ckA, hc, List.getElem_cons_zero, List.getElem_cons_succ]

theorem cdA_shape : cdA.vars = [Srt.k] ∧ cdA.pats = [.app dotk [], .var 0] ∧ cdA.req = none ∧
    cdA.rhs = .var 0 ∧ cdA.ens = none ∧ cdA.exs = [] ∧ cdA.pre = .top ∧ cdA.post = .top ∧
    cdA.prio = ckA.prio :=
  ⟨by decide +kernel, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide +kernel⟩
theorem ckA_shape : ckA.vars = [Srt.kitem, Srt.k, Srt.k] ∧ ckA.pats = [.app kseq [.var 0, .var 1], .var 2] ∧
    ckA.req = none ∧ ckA.rhs = .app kseq [.var 0, .app symApp [.var 1, .var 2]] ∧ ckA.ens = none ∧
    ckA.exs = [] ∧ ckA.pre = .top ∧ ckA.post = .top :=
  ⟨by decide +kernel, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem syms_ok : c.isCtor topLabel = true ∧ c.isCtor kCell = true ∧ c.isCtor kseq = true ∧
    c.isCtor symGo = true ∧ c.isCtor dotk = true ∧ c.isCtor counterLabel = true ∧
    c.isCtor symApp = false ∧ isHook symApp = false ∧ c.isParam symApp = false := by
  decide +kernel

theorem symsH (H : HookParams) : (cH H).isCtor topLabel = true ∧ (cH H).isCtor kCell = true ∧
    (cH H).isCtor kseq = true ∧ (cH H).isCtor symGo = true ∧ (cH H).isCtor dotk = true ∧
    (cH H).isCtor counterLabel = true ∧ (cH H).isCtor symApp = false ∧ isHook symApp = false ∧
    (cH H).isParam symApp = false := syms_ok

/-- No clause of append has a smaller priority than another. -/
theorem prio_low {cl cl' : Clause} (hcl : cl ∈ fnA.clauses) (hcl' : cl' ∈ fnA.clauses) : ¬ cl'.prio < cl.prio := by
  rw [fnA_clauses] at hcl hcl'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl hcl'
  have hp := cdA_shape.2.2.2.2.2.2.2.2
  rcases hcl with rfl | rfl <;> rcases hcl' with rfl | rfl <;> simp [hp]

/-- **append at values**, for every H: `append(z, r)` is `kcatRT z r` for values z, r of K. -/
theorem eval_append (H : HookParams) : ∀ (n : Nat) (z r : GroundTerm), sizeOf z ≤ n → c.sortOf z = some Srt.k →
    c.sortOf r = some Srt.k → Eval (cH H) symApp [z, r] (some (kcatRT z r)) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro z r hle hz hr
  obtain ⟨hdv, hdp, hdq, hdr, hde, hdx, hdpre, hdpost, -⟩ := cdA_shape
  obtain ⟨hkv, hkp, hkq, hkr, hke, hkx, hkpre, hkpost⟩ := ckA_shape
  have hcd : cdA ∈ fnA.clauses := by rw [fnA_clauses]; simp
  have hck : ckA ∈ fnA.clauses := by rw [fnA_clauses]; simp
  have hlk : (cH H).lookupFn symApp = some fnA := lookupFnA
  rcases k_shape hz with rfl | ⟨i, ks, rfl, hi, hks⟩
  · rw [kcatRT_dot]
    refine Eval.clause (σ := [(0, r)]) hlk hcd ?_ ?_ ?_ ?_ ?_ hdx ?_ ?_ ?_
    · intro j s hs
      rw [hdv] at hs
      match j, hs with
      | 0, hs => cases hs; exact ⟨r, rfl, by rw [sortOfH]; exact hr⟩
    · rw [hdp]; exact .cons (.ctor (symsH H).2.2.2.2.1 .nil) (.cons (.var rfl) .nil)
    · intro t ht; rw [hdq] at ht; cases ht
    · rw [hdpre]; exact .top
    · intro cl' hcl' _ hlt; exact absurd hlt (prio_low hcd hcl')
    · rw [hdr]; exact .var
    · intro t ht; rw [hde] at ht; cases ht
    · rw [hdpost]; exact .top
  · rw [kcatRT_kseq]
    have hrec := ih _ (Nat.lt_of_lt_of_le (by simp; omega) hle) ks r (Nat.le_refl _) hks hr
    refine Eval.clause (σ := [(0, i), (1, ks), (2, r)]) hlk hck ?_ ?_ ?_ ?_ ?_ hkx ?_ ?_ ?_
    · intro j s hs
      rw [hkv] at hs
      match j, hs with
      | 0, hs => cases hs; exact ⟨i, rfl, by rw [sortOfH]; exact hi⟩
      | 1, hs => cases hs; exact ⟨ks, rfl, by rw [sortOfH]; exact hks⟩
      | 2, hs => cases hs; exact ⟨r, rfl, by rw [sortOfH]; exact hr⟩
    · rw [hkp]
      exact .cons (.ctor (symsH H).2.2.1 (.cons (.var rfl) (.cons (.var rfl) .nil))) (.cons (.var rfl) .nil)
    · intro t ht; rw [hkq] at ht; cases ht
    · rw [hkpre]; exact .top
    · intro cl' hcl' _ hlt; exact absurd hlt (prio_low hck hcl')
    · rw [hkr]
      have hcall : EvalTerm (cH H) [(0, i), (1, ks), (2, r)] (.app symApp [.var 1, .var 2]) (some (kcatRT ks r)) :=
        .call (symsH H).2.2.2.2.2.2.1 (symsH H).2.2.2.2.2.2.2.1 (.cons .var (.cons .var .nil)) rfl hrec
          (symsH H).2.2.2.2.2.2.2.2
      exact .ctor (symsH H).2.2.1 (.cons .var (.cons hcall .nil))
    · intro t ht; rw [hke] at ht; cases ht
    · rw [hkpost]; exact .top

/-! ## The successors, for every H -/

def ctr : GroundTerm := .ctor counterLabel [int 0]
/-- The configuration `<generatedTop>(<k>(k), <generatedCounter>(0))`. -/
def cfgR (k : GroundTerm) : GroundTerm := .ctor topLabel [.ctor kCell [k], ctr]
/-- `go ~> r`. -/
def goSeq (r : GroundTerm) : GroundTerm := .ctor kseq [.inj exp Srt.kitem (.ctor symGo []), r]

theorem sortOf_ctor_congr {f : KCore.Sym} {ts ts0 : List GroundTerm}
    (hl : (lookupSig c.ctorSigs f).isSome = true)
    (h : c.sortsOf ts = c.sortsOf ts0) : c.sortOf (.ctor f ts) = c.sortOf (.ctor f ts0) := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hl
  simp only [Semantics.sortOf, hk, h]

theorem sortsOf_head_congr {t t0 : GroundTerm} {ts : List GroundTerm} (h : c.sortOf t = c.sortOf t0) :
    c.sortsOf (t :: ts) = c.sortsOf (t0 :: ts) := by
  simp only [Semantics.sortsOf, h]

theorem lookups_ok : (lookupSig c.ctorSigs topLabel).isSome = true ∧ (lookupSig c.ctorSigs kCell).isSome = true := by
  decide +kernel

/-- `<k> k </k>` is a configuration for every value k of K. -/
theorem sortOf_cfgR {k : GroundTerm} (hk : c.sortOf k = some Srt.k) : c.sortOf (cfgR k) = some topCellSort := by
  have h0 : c.sortOf (cfgR (.ctor dotk [])) = some topCellSort := by decide +kernel
  rw [← h0]
  exact sortOf_ctor_congr lookups_ok.1 (sortsOf_head_congr (sortOf_ctor_congr lookups_ok.2
    (sortsOf_head_congr (by rw [hk]; decide +kernel))))

theorem goSeq_sort {r : GroundTerm} (hr : c.sortOf r = some Srt.k) : c.sortOf (goSeq r) = some Srt.k :=
  kseq_sort (by decide +kernel) hr

section Steps
variable (H : HookParams) (R : GroundTerm) (hR : c.sortOf R = some Srt.k)

/-- x = `<k> go ~> R </k>`. -/
def X : Config (cH H) := ⟨cfgR (goSeq R), by rw [sortOfH]; exact sortOf_cfgR (goSeq_sort hR)⟩
/-- `<k> z ++ R </k>`. -/
def Y (z : GroundTerm) (hz : c.sortOf z = some Srt.k) : Config (cH H) :=
  ⟨cfgR (kcatRT z R), by rw [sortOfH]; exact sortOf_cfgR (kcatRT_sort _ z R (Nat.le_refl _) hz hR)⟩

include hR in
/-- The right side under τ that gives V0, V1 and Z the values R, the counter and z. -/
theorem rhs_eval {τ : Subst} {z : GroundTerm} (hz : c.sortOf z = some Srt.k)
    (h0 : τ.lookup 0 = some R) (h1 : τ.lookup 1 = some ctr) (h2 : τ.lookup 2 = some z) :
    EvalTerm (cH H) τ rz.rhs (some (cfgR (kcatRT z R))) := by
  rw [rz_shape.2.2.1]
  have hcall : EvalTerm (cH H) τ (.app symApp [.var 2, .var 0]) (some (kcatRT z R)) :=
    .call (symsH H).2.2.2.2.2.2.1 (symsH H).2.2.2.2.2.2.2.1 (.cons .var (.cons .var .nil))
      (by rw [h2, h0]; rfl) (eval_append H _ z R (Nat.le_refl _) hz hR) (symsH H).2.2.2.2.2.2.2.2
  have e1 : EvalTerm (cH H) τ (.var 1) (some ctr) := h1 ▸ .var
  exact .ctor (symsH H).1 (.cons (.ctor (symsH H).2.1 (.cons hcall .nil)) (.cons e1 .nil))

theorem prio_none {r' : Rule} (hr' : r' ∈ (cH H).rules) (hlt : r'.prio < rz.prio) : False := by
  rw [rulesH, List.mem_singleton] at hr'
  subst hr'
  exact Nat.lt_irrefl _ hlt

def σz (z : GroundTerm) : Subst := [(0, R), (1, ctr), (2, z)]

/-- **x steps to `<k> z ++ R </k>` for every value z of K**, Z := z, for every H. -/
theorem stepBy (z : GroundTerm) (hz : c.sortOf z = some Srt.k) :
    StepBy (cH H) rz (σz R z) (X H R hR) (Y H R hR z hz) where
  mem := by rw [rulesH]; simp
  hσ := fun j s hs => by
    rw [rz_shape.1] at hs
    match j, hs with
    | 0, hs => cases hs; exact ⟨_, rfl, by rw [sortOfH]; exact hR⟩
    | 1, hs => cases hs; exact ⟨_, rfl, by rw [sortOfH]; decide +kernel⟩
    | 2, hs => cases hs; exact ⟨_, rfl, by rw [sortOfH]; exact hz⟩
  hmatch := by
    rw [rz_shape.2.1]
    exact .ctor (symsH H).1 (.cons (.ctor (symsH H).2.1 (.cons (.ctor (symsH H).2.2.1
      (.cons (.inj (.ctor (symsH H).2.2.2.1 .nil)) (.cons (.var rfl) .nil))) .nil)) (.cons (.var rfl) .nil))
  hreq := fun t ht => by rw [rz_shape.2.2.2.1] at ht; cases ht
  hpre := by rw [rz_shape.2.2.2.2.2.2.1]; exact .top
  heval := rhs_eval H R hR hz rfl rfl rfl
  hens := fun t ht => by rw [rz_shape.2.2.2.2.1] at ht; cases ht
  hpost := by rw [rz_shape.2.2.2.2.2.2.2]; exact .top
  hprio := fun r' hr' hlt => (prio_none H hr' hlt).elim

/-- **x steps to `<k> z ++ R </k>` for every value z of K**, for every H. -/
theorem step (z : GroundTerm) (hz : c.sortOf z = some Srt.k) : Step (cH H) (X H R hR) (Y H R hR z hz) :=
  step_iff_by.mpr ⟨rz, σz R z, stepBy H R hR z hz⟩

/-- **The named instance z = `.K`**: x steps to `<k> R </k>`, for every H. -/
theorem step_dot : Step (cH H) (X H R hR) ⟨cfgR R, by rw [sortOfH]; exact sortOf_cfgR hR⟩ := by
  have h := step H R hR (.ctor dotk []) (by decide +kernel)
  simp only [Y, kcatRT_dot] at h
  exact h

/-- **z = `go`**: x steps to itself, for every H. -/
theorem step_self : Step (cH H) (X H R hR) (X H R hR) := by
  have h := step H R hR (goSeq (.ctor dotk [])) (goSeq_sort (by decide +kernel))
  simp only [Y, goSeq, kcatRT_kseq, kcatRT_dot] at h
  exact h

/-- A match at x gives V0 and V1 the values R and the counter. -/
theorem lookups {τ : Subst} (hm : PatVal (cH H) τ rz.lhs (cfgR (goSeq R))) :
    τ.lookup 0 = some R ∧ τ.lookup 1 = some ctr := by
  rw [rz_shape.2.1] at hm
  have hp : patternHooks.contains topLabel = false ∧ patternHooks.contains kCell = false ∧
      patternHooks.contains kseq = false := by decide +kernel
  obtain ⟨-, vs, he, hs⟩ := PatVal.app_inv hp.1 hm (symsH H).1
  cases he
  obtain ⟨_, _, he1, h1, hs1⟩ := PatVals.cons_inv hs
  cases he1
  obtain ⟨_, _, he2, h2, _⟩ := PatVals.cons_inv hs1
  cases he2
  obtain ⟨-, ws, hw, hws⟩ := PatVal.app_inv hp.2.1 h1 (symsH H).2.1
  cases hw
  obtain ⟨_, _, hw1, h11, _⟩ := PatVals.cons_inv hws
  cases hw1
  obtain ⟨-, us, hu, hus⟩ := PatVal.app_inv hp.2.2 h11 (symsH H).2.2.1
  cases hu
  obtain ⟨_, _, hu1, _, hus1⟩ := PatVals.cons_inv hus
  cases hu1
  obtain ⟨_, _, hu2, h22, _⟩ := PatVals.cons_inv hus1
  cases hu2
  exact ⟨PatVal.var_inv h22, PatVal.var_inv h2⟩

/-- **`Step` reaches exactly the `<k> z ++ R </k>`** from x, z a value of K, for every H. -/
theorem step_iff (y : Config (cH H)) :
    Step (cH H) (X H R hR) y ↔ ∃ z, ∃ hz : c.sortOf z = some Srt.k, y = Y H R hR z hz := by
  constructor
  · intro hs
    obtain ⟨r, τ, hb⟩ := step_iff_by.mp hs
    have hr := hb.mem
    rw [rulesH, List.mem_singleton] at hr
    subst hr
    obtain ⟨h0, h1⟩ := lookups H R hb.hmatch
    obtain ⟨v, h2, hv⟩ := hb.hσ 2 Srt.k (by rw [rz_shape.1]; rfl)
    rw [sortOfH] at hv
    refine ⟨v, hv, Subtype.ext ?_⟩
    exact Option.some.inj (EvalTerm.functional_of_fnDet (fnDetH H) hb.heval (rhs_eval H R hR hv h0 h1 h2))
  · rintro ⟨z, hz, rfl⟩
    exact step H R hR z hz

/-- **By `exact_hyp`, for every H**: y is a successor of x in some model of `Γc` with the step's
closure exactly where y is some `<k> z ++ R </k>`, z a value of K. -/
theorem exact_y (y : Config (cH H)) :
    (∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
      (I ⊧ᴵP (Γc (cH H) ∪ Γstep (cH H))) ∧ ¬ (I ⊧ᴵ (den (cH H) (X H R hR).val ⇒ ∼ KoreAML.sNext (den (cH H) y.val)))) ↔
    ∃ z, ∃ hz : c.sortOf z = some Srt.k, y = Y H R hR z hz := by
  rw [← exact_hyp (cH H) (coreOKH H) (fnHypH H) (X H R hR) y]
  exact step_iff H R hR y

end Steps

/-- info: 'TieRuleRhsTop.tie' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tie
/-- info: 'TieRuleRhsTop.right_tie' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms right_tie
/-- info: 'TieRuleRhsTop.eval_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms eval_append
/-- info: 'TieRuleRhsTop.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step
/-- info: 'TieRuleRhsTop.step_dot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_dot
/-- info: 'TieRuleRhsTop.step_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_self
/-- info: 'TieRuleRhsTop.step_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_iff
/-- info: 'TieRuleRhsTop.exact_y' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms exact_y

end TieRuleRhsTop
