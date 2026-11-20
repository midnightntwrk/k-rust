/-
  `Faithful.Model.consistent_of_fnMany_agree` on the fixture e3-ml-eq-rhs-or, at its function h,
  for every interpretation of the hooks. Run from the package root:
  `lake env lean -j1 test/FnManyOverOr.lean`.

  The text is `f2-examples/e3-ml-eq-rhs-or.kompile.kore` (`rule h(X) => f(X) #Or g(X)` with
  `rule f(X) => X` and `rule g(X) => 0 -Int X`, none `total`, over Int). The reader gives h the one
  clause `clH`: `[X:Int, #Or0:Int]`, `exs [1]`, `rhs #Or0`, `post := #Or0 ∈ f(X) ∨ #Or0 ∈ g(X)`
  (`read`). Decided on the text (`decide +kernel`, `decide_cheap`):
  - h's name `Lblh` is read as no instance (`plain_h`) and is no constant (`spare_h`);
  - the theory's lists hold `Lblh` in h's own items only (`lists_h`), the values are built from
    symbols of other names (`values_h`), and the heads applied at values but h's are not `Lblh`
    (`hooks_h`, `params_h`, `fns_h`);
  - h's clause's premise and right side apply no symbol named `Lblh` (`kok_h`);
  - `coreOKEx`, no raw parameter, every clause's predicate `\top`.
  For every H: every premise of the theory but h's own items avoids `Lblh` (`avoidsOffH`; h's
  clause applies at every argument of Int, so the theory states no rest of h), and two matches of
  h's clause at one argument agree on X, its only variable off `exsFree` (`agreeH`). So the
  theory has a model for every H where evaluation has one result at most, `f` and `g` solve their
  equations and the right-side predicates have truth values (`consistent_of_rest`).

  Those three hold for every H, so the theory has a model for every H (`consistent`):
  - `fnDetH`: every function has at most one result, by `fnDet_of_coherent`. f's and g's clause is
    coherent with itself (one right-hand side at matches agreeing on X), h's through the results'
    agreement (`resEx_h`: a result of h's clause at a match giving X the value x is x, since the
    instance at #Or0 := x has `post` true and gives x alone, and a result agrees with every
    instance), a sort predicate's clauses as in `Faithful.fnDet_of_agree`. h's clause is not match
    independent (at n ≠ 0 no result of it exists), so `fnDet_of_agree` does not apply.
  - `postDecH`: h's right-side predicate is decided where f and g each have one result (`dec_post`).
  - `solvesF`, `solvesG`: `f(x)` is x and `g(n)` is `0 - n`, each its one instance's value.
  `h_not_matchIndependent`: h's clause decides at `[1]` and has no result there.
-/
import KcoreSpec
import KcoreSpec.ModelFnMany
import KcoreSpec.ModelFnOverHooks

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore KCore.Parse KCore.GenEqs KCore.Faithful KCore.Faithful.Model

/-! ## Facts the proofs share with test/ExClauseFxOr.lean (a test file imports no test file) -/

namespace ExClauseFixtures.OrFx

open GroundTerm

variable {d : Semantics} {σ : Subst}

theorem lkSelf (i : Nat) (v : GroundTerm) (σ : Subst) : ((i, v) :: σ : Subst).lookup i = some v := by
  simp [List.lookup]

theorem lkNe {i j : Nat} (v : GroundTerm) (σ : Subst) (h : i ≠ j) :
    ((j, v) :: σ : Subst).lookup i = σ.lookup i := by
  have hb : (i == j) = false := by simp [h]
  simp [List.lookup, hb]

theorem sameResult_some {v w : GroundTerm} : sameResult (some v) (some w) = true ↔ v = w := by
  simp [sameResult, cmp_eq_iff]

theorem sameResult_self (v : GroundTerm) : sameResult (some v) (some v) = true := sameResult_some.mpr rfl

theorem holds_cast {n : Nat} {p : Cond} {b b' : Bool} (h : Holds d n σ p b) (e : b = b') : Holds d n σ p b' :=
  e ▸ h

/-- The instances of a clause whose one existential variable is the variable 1: σ with it set. -/
theorem agree_set1 (σ : Subst) (w : GroundTerm) : AgreeOff [1] σ ((1, w) :: σ) := fun i hi =>
  lkNe w σ (fun h => hi (by rw [h]; exact List.mem_singleton_self _))

/-- A substitution giving the variables 0 and 1 values of the two sorts is well sorted. -/
theorem sorted2 {a b : Srt} {x w : GroundTerm} (h0 : σ.lookup 0 = some x) (hx : d.sortOf x = some a)
    (h1 : σ.lookup 1 = some w) (hw : d.sortOf w = some b) : d.WellSorted [a, b] σ := by
  intro i s hs
  match i, hs with
  | 0, hs => cases hs; exact ⟨x, h0, hx⟩
  | 1, hs => cases hs; exact ⟨w, h1, hw⟩
  | i + 2, hs => simp at hs

/-- A substitution giving the variable 0 a value of the sort is well sorted. -/
theorem sorted1 {a : Srt} {x : GroundTerm} (h0 : σ.lookup 0 = some x) (hx : d.sortOf x = some a) :
    d.WellSorted [a] σ := by
  intro i s hs
  match i, hs with
  | 0, hs => cases hs; exact ⟨x, h0, hx⟩
  | i + 1, hs => simp at hs

/-- The predicate p has the truth value b under σ, and no other. -/
def Dec (d : Semantics) (n : Nat) (σ : Subst) (p : Cond) (b : Bool) : Prop :=
  Holds d n σ p b ∧ ∀ t, Holds d n σ p t → t = b

theorem dec_or {n : Nat} {p q : Cond} {b b' : Bool} (hp : Dec d n σ p b) (hq : Dec d n σ q b') :
    Dec d n σ (.or p q) (b || b') :=
  ⟨.or hp.1 hq.1, fun t ht => by cases ht with | or h h' => rw [hp.2 _ h, hq.2 _ h']⟩

/-- `f` is a function of d: no constructor, hook, parameter or overloading symbol, so an
application of it on defined arguments has `Eval`'s results. -/
def Fun (d : Semantics) (f : Sym) : Prop :=
  d.isCtor f = false ∧ isHook f = false ∧ d.isParam f = false ∧ d.isOvl f = false

/-- `f` has at `[x]` the result r and no other. -/
def Only (d : Semantics) (f : Sym) (x : GroundTerm) (r : Option GroundTerm) : Prop :=
  Eval d f [x] r ∧ ∀ r', Eval d f [x] r' → r' = r

/-- The application `f(X)` of a function has `f`'s results at the value σ gives X. -/
theorem call_of {f : Sym} (hf : Fun d f) {x : GroundTerm} (h0 : σ.lookup 0 = some x)
    {r : Option GroundTerm} (h : Eval d f [x] r) : EvalTerm d σ (.app f [.var 0]) r :=
  .call hf.1 hf.2.1 (rs := [σ.lookup 0]) (.cons .var .nil) (by rw [h0]; rfl) h hf.2.2.1

theorem call_inv {f : Sym} (hf : Fun d f) {x : GroundTerm} (h0 : σ.lookup 0 = some x)
    {r : Option GroundTerm} (h : EvalTerm d σ (.app f [.var 0]) r) : Eval d f [x] r := by
  have hrs : ∀ {rs}, EvalTerms d σ [.var 0] rs → rs = [some x] := fun hts => by
    obtain ⟨r0, rs', rfl, h1, hs⟩ := EvalTerms.cons_inv hts
    obtain rfl := EvalTerms.nil_inv hs
    obtain rfl := EvalTerm.var_inv h1
    rw [h0]
  generalize ht : Term.app f [.var 0] = t at h
  cases h with
  | hook _ hk _ _ _ => cases ht; rw [hf.2.1] at hk; cases hk
  | ctor hc _ => cases ht; rw [hf.1] at hc; cases hc
  | param _ _ hp _ _ => cases ht; rw [hf.2.2.1] at hp; cases hp
  | call _ _ hts hvs he _ =>
    cases ht
    rw [hrs hts] at hvs
    cases hvs
    exact he
  | callUndef _ _ hts hvs _ => cases ht; rw [hrs hts] at hvs; cases hvs
  | ovl _ ho _ _ => cases ht; rw [hf.2.2.2] at ho; cases ho
  | ovlFn _ ho _ _ _ _ _ => cases ht; rw [hf.2.2.2] at ho; cases ho
  | _ => cases ht

/-- An application of an interpreted hooked symbol has the value `hookRes` gives at its arguments'
results, and none where an argument has none. -/
theorem hook_inv {f : Sym} {ts : List Term} {r : Option GroundTerm} (hc : d.isCtor f = false)
    (hk : isHook f = true) (h : EvalTerm d σ (.app f ts) r) :
    ∃ rs, EvalTerms d σ ts rs ∧ (∀ vs, allSome rs = some vs → d.hookRes f vs = some r) ∧
      (allSome rs = none → r = none) := by
  generalize ht : Term.app f ts = t at h
  cases h with
  | hook _ _ hts hh hund => cases ht; exact ⟨_, hts, hh, hund⟩
  | ctor h _ => cases ht; rw [hc] at h; cases h
  | param _ h _ _ _ => cases ht; rw [hk] at h; cases h
  | call _ h _ _ _ _ => cases ht; rw [hk] at h; cases h
  | callUndef _ h _ _ _ => cases ht; rw [hk] at h; cases h
  | ovl _ ho _ _ => cases ht; rw [(d.isOvl_parts ho).2.1] at hk; cases hk
  | ovlFn _ ho _ _ _ _ _ => cases ht; rw [(d.isOvl_parts ho).2.1] at hk; cases hk
  | _ => cases ht

end ExClauseFixtures.OrFx

namespace FnManyOverOr

open GroundTerm ExClauseFixtures.OrFx

definition_of defn from "f2-examples/e3-ml-eq-rhs-or.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

def fF : Sym := 384
def fG : Sym := 385
def fH : Sym := 386
def nH : String := "Lblh"

/-- `f(X) => X`. -/
def clF : Clause := { vars := [Srt.int], pats := [.var 0], req := none, rhs := .var 0, ens := none }

/-- `g(X) => 0 -Int X`. -/
def clG : Clause :=
  { vars := [Srt.int], pats := [.var 0], req := none, rhs := .app intSub [.dv Srt.int (.int 0), .var 0],
    ens := none }

/-- `#Or0 ∈ f(X) ∨ #Or0 ∈ g(X)`. -/
def postH : Cond :=
  .or (.mem Srt.int (.var 1) (.app fF [.var 0])) (.mem Srt.int (.var 1) (.app fG [.var 0]))

/-- `h(X) => #Or0` with `exs = [#Or0]` and `post := postH`. -/
def clH : Clause :=
  { vars := [Srt.int, Srt.int], pats := [.var 0], req := none, rhs := .var 1, ens := none, exs := [1],
    post := postH }

def fnF : Fn := { label := fF, args := [Srt.int], result := Srt.int, clauses := [clF] }
def fnG : Fn := { label := fG, args := [Srt.int], result := Srt.int, clauses := [clG] }
def fnH : Fn := { label := fH, args := [Srt.int], result := Srt.int, clauses := [clH] }

/-- **The reading**: the text's functions are `f`, `g` and `h`, `h` with the one clause `clH`. -/
theorem read : c.fns = [fnF, fnG, fnH] := by kernel_rfl

theorem name_h : c.symName fH = nH := by decide +kernel

/-! ## The checks on the text -/

theorem plain_h : instDecode? nH = none := by decide +kernel
theorem spare_h : spareSymB c nH = true := by decide +kernel
theorem values_h : NameFree.valuesN c [nH] = true := by rw [NameFree.valuesN]; decide_cheap 40
theorem hooks_h : hookSigs.all (fun k => NameFree.appOKN c [nH] k.name) = true := by decide_cheap 40
theorem params_h : c.params.all (fun k => NameFree.appOKN c [nH] k.sig.name) = true := by decide_cheap 40
theorem fns_h : c.allFns.all (fun g => decide (g.label = fH) || NameFree.appOKN c [nH] g.label) = true := by
  decide_cheap 40
theorem lists_h : listsOffB c fH nH = true := by rw [listsOffB]; decide_cheap 40
theorem kok_h : ownKokB c fnH clH = true := by decide +kernel
theorem coreEx : c.coreOKEx = true := by
  unfold Semantics.coreOKEx Semantics.sortedOKEx; decide_cheap
theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem preTop : (c.fns.all fun f => f.clauses.all fun cl => cl.pre.isTop) = true := by decide +kernel
theorem fH_one : (c.allFns.filter (fun g => decide (g.label = fH))).length = 1 := by decide +kernel
theorem exsFree_h : clH.exsFree = [1] := by decide

/-! ## For every H -/

theorem rangeBelowH (H : HookParams) : RangeBelow (cH H) :=
  have h := hypSoundEx_of_coreEx (c := cH H) ((coreOKEx_withHooks_fm c H).trans coreEx)
  haveI := h.2.2.2.2.2.2.2.2
  rangeBelow_of_genWf h.2.2.2.1

/-- h's clause applies at every argument of Int. -/
theorem not_fails_h (H : HookParams) {x : GroundTerm} (hx : (cH H).sortOf x = some Srt.int) :
    ¬ Fails (cH H) [x] clH := by
  intro hF
  cases hF with
  | intro hF =>
    have hs : (cH H).WellSorted clH.vars [(1, x), (0, x)] := by
      intro i s hs
      match i, hs with
      | 0, hs => cases hs; exact ⟨x, rfl, hx⟩
      | 1, hs => cases hs; exact ⟨x, rfl, hx⟩
      | i + 2, hs => simp [clH] at hs
    cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
    | intro ht => cases ht
    | pre hp => cases hp

/-- **Every premise but h's own items avoids `Lblh`, for every H.** -/
theorem avoidsOffH (H : HookParams) : AvoidsOff (cH H) fH ((cH H).symName fH) := by
  have hn : (cH H).symName fH = nH := name_h
  rw [hn]
  refine avoidsOff_of_lists (rangeBelowH H) (listsOff_withHooks H lists_h) values_h
    (List.all_eq_true.mp hooks_h) (List.all_eq_true.mp params_h)
    (fun g hg hl => by
      have h1 : NameFree.appOKN c [nH] g.label = true := by
        have := List.all_eq_true.mp fns_h g hg
        simpa [hl] using this
      exact h1)
    (fun fn hfn hl vs hvs => ?_)
  have hfn' : fn ∈ c.allFns.filter (fun g => decide (g.label = fH)) := List.mem_filter.mpr ⟨hfn, by simpa using hl⟩
  have hH : fnH ∈ c.allFns.filter (fun g => decide (g.label = fH)) :=
    List.mem_filter.mpr ⟨List.mem_append_left _ (by rw [read]; simp), by simp [fnH]⟩
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp fH_one
  rw [hx, List.mem_singleton] at hfn' hH
  obtain rfl : fn = fnH := hfn'.trans hH.symm
  match vs, hvs with
  | [x], hvs =>
    have hx : (cH H).sortOf x = some Srt.int := by
      simp only [Semantics.sortsOf] at hvs
      cases h1 : (cH H).sortOf x with
      | none => rw [h1] at hvs; cases hvs
      | some s => rw [h1] at hvs; cases hvs; rfl
    exact fun hall => not_fails_h H hx (hall clH (List.mem_singleton_self _))
  | [], hvs => cases hvs
  | _ :: _ :: _, hvs => exact absurd (sortsOf_len hvs) (by simp [fnH])

/-- **Two matches of h's clause at one argument agree on X, for every H.** -/
theorem agreeH (H : HookParams) : ∀ ws σ₁ σ₂, clH.AppliesAt (cH H) σ₁ ws → clH.AppliesAt (cH H) σ₂ ws →
    ∀ i < clH.vars.length, i ∉ clH.exsFree → σ₁.lookup i = σ₂.lookup i := by
  intro ws σ₁ σ₂ h1 h2 i hi hx
  rw [exsFree_h] at hx
  have hi0 : i = 0 := by
    have hl : clH.vars.length = 2 := rfl
    simp only [List.mem_singleton] at hx
    omega
  subst hi0
  obtain ⟨v, vs', rfl, hv, -⟩ := PatVals.cons_inv (show PatVals (cH H) σ₁ [.var 0] ws from h1.2.1)
  obtain ⟨v', vs'', hvs, hv', -⟩ := PatVals.cons_inv (show PatVals (cH H) σ₂ [.var 0] (v :: vs') from h2.2.1)
  cases hvs
  rw [PatVal.var_inv hv, PatVal.var_inv hv']

/-- **The theory has a model for every H** where evaluation has one result at most, `f` and `g`
solve their equations and the right-side predicates have truth values. -/
theorem consistent_of_rest (H : HookParams) (hd : FnDet (cH H)) (hf : FnSolvesAt (cH H) fnF)
    (hg : FnSolvesAt (cH H) fnG) (hq : ClausePostDecided (cH H)) : Consistent (cH H) := by
  have hfns : (cH H).fns = [fnF, fnG, fnH] := read
  refine consistent_of_fnMany_agree (f := fH) (fn := fnH) (cl := clH) (a := Srt.int)
    ((coreOKEx_withHooks_fm c H).trans coreEx) (by rw [hfns]; simp) rfl rfl rfl (by decide)
    (by rw [show (cH H).symName fH = nH from name_h]; exact plain_h)
    (by rw [show (cH H).symName fH = nH from name_h, spareSymB_withHooks_fm]; exact spare_h)
    (avoidsOffH H) (by rw [ownKokB_withHooks]; exact kok_h) hd (fun g hg' hl => ?_) (agreeH H)
    (clausePreDecided_of_isTop (c := cH H) preTop) hq (openLaws_of_plain noRaw)
  rw [hfns] at hg'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
  rcases hg' with rfl | rfl | rfl
  · exact hf
  · exact hg
  · exact absurd rfl hl

/-! ## The clauses of f, g and h, for every H -/

theorem kinds : (c.isCtor fF = false ∧ isHook fF = false ∧ c.isParam fF = false ∧ c.isOvl fF = false) ∧
    (c.isCtor fG = false ∧ isHook fG = false ∧ c.isParam fG = false ∧ c.isOvl fG = false) ∧
    c.isCtor intSub = false := by decide +kernel
theorem shapes : c.shapesOK = true := by decide_cheap

section Clause

variable {d : Semantics} {σ : Subst}

/-- The truth value of `postH` where #Or0 has the value w, `f` the result rf and `g` the result rg
at X's value. -/
def postVal (w : GroundTerm) (rf rg : Option GroundTerm) : Bool :=
  sameResult (some w) rf || sameResult (some w) rg

theorem dec_mem {f : Sym} (hf : Fun d f) {n : Nat} {x w : GroundTerm} {r : Option GroundTerm}
    (ho : Only d f x r) (h0 : σ.lookup 0 = some x) (h1 : σ.lookup 1 = some w) :
    Dec d n σ (.mem Srt.int (.var 1) (.app f [.var 0])) (sameResult (some w) r) := by
  refine ⟨holds_cast (Holds.mem .var (call_of hf h0 ho.1)) (by rw [h1]; rfl), fun t ht => ?_⟩
  cases ht with
  | mem h h' =>
    obtain rfl := EvalTerm.var_inv h
    obtain rfl := ho.2 _ (call_inv hf h0 h')
    rw [h1]; rfl

/-- **`post` is decided** where `f` and `g` each have one result at X's value. -/
theorem dec_post (hF : Fun d fF) (hG : Fun d fG) {x w : GroundTerm} {rf rg : Option GroundTerm}
    (hf : Only d fF x rf) (hg : Only d fG x rg) (h0 : σ.lookup 0 = some x) (h1 : σ.lookup 1 = some w) :
    Dec d 2 σ postH (postVal w rf rg) :=
  dec_or (dec_mem hF hf h0 h1) (dec_mem hG hg h0 h1)

/-- An instance whose `post` is true gives #Or0's value, and agrees with no other result. -/
theorem inst_true (hF : Fun d fF) (hG : Fun d fG) {x w : GroundTerm} {rf rg : Option GroundTerm}
    (hf : Only d fF x rf) (hg : Only d fG x rg) (h0 : σ.lookup 0 = some x) (h1 : σ.lookup 1 = some w)
    (hp : postVal w rf rg = true) : InstIs d σ clH (some w) ∧ ∀ r, InstIs d σ clH r → r = some w := by
  have hd := dec_post hF hG hf hg h0 h1
  refine ⟨.gives (h1 ▸ .var) (fun t ht => nomatch ht) (holds_cast hd.1 hp), fun r h => ?_⟩
  cases h with
  | fails _ hfl =>
    cases hfl with
    | ens ht _ _ => cases ht
    | post hq => have e := hd.2 _ hq; rw [hp] at e; cases e
    | rhs h => have e := EvalTerm.var_inv h; rw [h1] at e; cases e
  | gives hrhs _ _ =>
    have e := EvalTerm.var_inv hrhs
    rw [h1] at e; exact e

/-- An instance whose `post` is false gives nothing: it agrees with every result. -/
theorem inst_false (hF : Fun d fF) (hG : Fun d fG) {x w : GroundTerm} {rf rg : Option GroundTerm}
    (hf : Only d fF x rf) (hg : Only d fG x rg) (h0 : σ.lookup 0 = some x) (h1 : σ.lookup 1 = some w)
    (hp : postVal w rf rg = false) (r : Option GroundTerm) : InstIs d σ clH r :=
  have hd := dec_post hF hG hf hg h0 h1
  .fails hd.1 (.post (holds_cast hd.1 hp))

/-- An instance at σ gives X the value σ gives it. -/
theorem agree_x {σ' : Subst} (h : AgreeOff clH.exsFree σ σ') : σ'.lookup 0 = σ.lookup 0 :=
  h 0 (by decide)

/-- σ with #Or0 := w is an instance of the clause at σ, well sorted where σ gives X a value of Int
and w is of Int. -/
theorem ext_sorted {x w : GroundTerm} (h0 : σ.lookup 0 = some x) (hx : d.sortOf x = some Srt.int)
    (hw : d.sortOf w = some Srt.int) : d.WellSorted clH.vars ((1, w) :: σ) :=
  sorted2 ((lkNe _ _ (by decide)).trans h0) hx (lkSelf _ _ _) hw

theorem ext_x {x : GroundTerm} (h0 : σ.lookup 0 = some x) (w : GroundTerm) :
    ((1, w) :: σ : Subst).lookup 0 = some x := (lkNe _ _ (by decide)).trans h0

end Clause

/-! ### `f` and `g` in a semantics that reads their clauses -/

section FG

variable {d : Semantics}

/-- **`f(x)` is x and nothing else**, at an argument of Int. -/
theorem f_only (hfn : d.lookupFn fF = some fnF) {x : GroundTerm} (hx : d.sortOf x = some Srt.int) :
    Only d fF x (some x) := by
  have hcl : ∀ {cl fn'}, d.lookupFn fF = some fn' → cl ∈ fn'.clauses → cl = clF := fun h1 h2 => by
    rw [hfn] at h1; cases h1; simpa [fnF] using h2
  have hx0 : ∀ {σ : Subst}, PatVals d σ clF.pats [x] → σ.lookup 0 = some x := fun hm => by
    obtain ⟨v, vs', hvs, hv, -⟩ := PatVals.cons_inv hm
    cases hvs
    exact PatVal.var_inv hv
  have hs : d.WellSorted clF.vars [(0, x)] := sorted1 rfl hx
  refine ⟨.clause (fn := fnF) (cl := clF) (σ := [(0, x)]) hfn (List.mem_singleton_self _) hs
    (.cons (.var rfl) .nil) (fun t ht => nomatch ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fnF, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    rfl .var (fun t ht => nomatch ht) .top, fun r h => ?_⟩
  cases h with
  | clause hfn' hmem _ hmatch _ _ _ _ hrhs _ _ =>
    obtain rfl := hcl hfn' hmem
    rw [EvalTerm.var_inv hrhs, hx0 hmatch]
  | rest hfn' hnone =>
    rw [hfn] at hfn'; cases hfn'
    cases hnone clF (List.mem_singleton_self _) with
    | intro hF =>
      cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
      | intro ht => cases ht
      | pre hp => cases hp
  | ensFails hfn' hmem _ _ _ _ _ _ ht _ _ => obtain rfl := hcl hfn' hmem; cases ht
  | clauseEx hfn' hmem _ _ _ _ _ hne _ _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd rfl hne
  | exNone hfn' hmem hne _ _ _ _ _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd rfl hne

theorem subHook : isHook intSub = true := by decide +kernel

/-- `0 -Int n`, under every interpretation: the hook's value on Int values. -/
theorem hookSub (n : Int) : d.hookRes intSub [int 0, int n] = some (some (int (0 - n))) :=
  Semantics.hookRes_of_value rfl

theorem evalSub (hc : d.isCtor intSub = false) {σ : Subst} {n : Int} (h0 : σ.lookup 0 = some (int n)) :
    EvalTerm d σ clG.rhs (some (int (0 - n))) :=
  .hook hc subHook (rs := [some (int 0), σ.lookup 0]) (.cons .dv (.cons .var .nil))
    (fun vs hvs => by rw [h0] at hvs; cases hvs; exact hookSub n)
    (fun hn => by rw [h0] at hn; cases hn)

theorem evalSub_inv (hc : d.isCtor intSub = false) {σ : Subst} {n : Int} (h0 : σ.lookup 0 = some (int n))
    {r : Option GroundTerm} (h : EvalTerm d σ clG.rhs r) : r = some (int (0 - n)) := by
  obtain ⟨rs, hts, hh, -⟩ := hook_inv hc subHook h
  obtain ⟨r0, rs', rfl, h1, hs⟩ := EvalTerms.cons_inv hts
  obtain ⟨r1, rs'', rfl, h2, hs'⟩ := EvalTerms.cons_inv hs
  obtain rfl := EvalTerms.nil_inv hs'
  obtain rfl := EvalTerm.dv_inv h1
  obtain rfl := EvalTerm.var_inv h2
  have := hh [int 0, int n] (by rw [h0]; rfl)
  rw [hookSub] at this
  exact (Option.some.inj this).symm

/-- **`g(n)` is `0 - n` and nothing else.** -/
theorem g_only (hc : d.isCtor intSub = false) (hfn : d.lookupFn fG = some fnG) (n : Int) :
    Only d fG (int n) (some (int (0 - n))) := by
  have hcl : ∀ {cl fn'}, d.lookupFn fG = some fn' → cl ∈ fn'.clauses → cl = clG := fun h1 h2 => by
    rw [hfn] at h1; cases h1; simpa [fnG] using h2
  have hx0 : ∀ {σ : Subst}, PatVals d σ clG.pats [int n] → σ.lookup 0 = some (int n) := fun hm => by
    obtain ⟨v, vs', hvs, hv, -⟩ := PatVals.cons_inv hm
    cases hvs
    exact PatVal.var_inv hv
  have hs : d.WellSorted clG.vars [(0, int n)] := sorted1 rfl (rmS_sortOf_int d n)
  refine ⟨.clause (fn := fnG) (cl := clG) (σ := [(0, int n)]) hfn (List.mem_singleton_self _) hs
    (.cons (.var rfl) .nil) (fun t ht => nomatch ht) .top
    (fun cl' hcl' _ hlt => by
      simp only [fnG, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    rfl (evalSub hc rfl) (fun t ht => nomatch ht) .top, fun r h => ?_⟩
  cases h with
  | clause hfn' hmem _ hmatch _ _ _ _ hrhs _ _ =>
    obtain rfl := hcl hfn' hmem
    exact evalSub_inv hc (hx0 hmatch) hrhs
  | rest hfn' hnone =>
    rw [hfn] at hfn'; cases hfn'
    cases hnone clG (List.mem_singleton_self _) with
    | intro hF =>
      cases hF _ (hs.at _) (.cons (.var rfl) .nil) with
      | intro ht => cases ht
      | pre hp => cases hp
  | ensFails hfn' hmem _ _ _ _ _ _ ht _ _ => obtain rfl := hcl hfn' hmem; cases ht
  | clauseEx hfn' hmem _ _ _ _ _ hne _ _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd rfl hne
  | exNone hfn' hmem hne _ _ _ _ _ _ _ => obtain rfl := hcl hfn' hmem; exact absurd rfl hne

end FG

theorem lookupF : c.lookupFn fF = some fnF := by rw [Semantics.lookupFn_eq]; rfl
theorem lookupG : c.lookupFn fG = some fnG := by rw [Semantics.lookupFn_eq]; rfl
theorem lookupH : c.lookupFn fH = some fnH := by rw [Semantics.lookupFn_eq]; rfl
theorem lookupFH (H : HookParams) : (cH H).lookupFn fF = some fnF := by
  rw [Semantics.lookupFn_withHooks]; exact lookupF
theorem lookupGH (H : HookParams) : (cH H).lookupFn fG = some fnG := by
  rw [Semantics.lookupFn_withHooks]; exact lookupG
theorem lookupHH (H : HookParams) : (cH H).lookupFn fH = some fnH := by
  rw [Semantics.lookupFn_withHooks]; exact lookupH
theorem funF (H : HookParams) : Fun (cH H) fF := kinds.1
theorem funG (H : HookParams) : Fun (cH H) fG := kinds.2.1
theorem subNotCtor (H : HookParams) : (cH H).isCtor intSub = false := kinds.2.2
theorem shapesH (H : HookParams) : (cH H).shapesOK = true := shapes

/-- f and g have one result each at an argument of Int, for every H. -/
theorem fg_only (H : HookParams) {x : GroundTerm} (hx : (cH H).sortOf x = some Srt.int) :
    ∃ rg, Only (cH H) fF x (some x) ∧ Only (cH H) fG x rg := by
  obtain ⟨n, rfl⟩ := shape_int (shapesH H) hx
  exact ⟨_, f_only (lookupFH H) hx, g_only (subNotCtor H) (lookupGH H) n⟩

/-- **A result of h's clause at a match giving X the value x is x, for every H**: the instance at
#Or0 := x has `post` true (`f(x)` is x), so it gives x and agrees with no other result; a result
of the clause agrees with every instance. -/
theorem resEx_h (H : HookParams) {σ : Subst} {x : GroundTerm} {r : Option GroundTerm}
    (h0 : σ.lookup 0 = some x) (hx : (cH H).sortOf x = some Srt.int) (h : clH.ResEx (cH H) σ r) :
    r = some x := by
  obtain ⟨rg, hf, hg⟩ := fg_only H hx
  have hp : postVal x (some x) rg = true := by simp [postVal, sameResult_self]
  have ht := inst_true (funF H) (funG H) hf hg (ext_x h0 x) (lkSelf _ _ _) hp
  have hag : AgreeOff clH.exsFree σ ((1, x) :: σ) := agree_set1 σ x
  have hws := ext_sorted h0 hx hx
  rcases h with ⟨σ₁, v, -, -, -, hall, rfl⟩ | ⟨rfl, -, hall⟩
  · exact ht.2 _ (hall _ hag hws)
  · exact absurd (ht.2 _ (hall _ hag hws)) (by simp)

/-- The value of X at a match of a clause whose pattern is X and whose X is of Int. -/
theorem match0 {d : Semantics} {cl : Clause} (hp : cl.pats = [.var 0]) (hu : 0 ∈ cl.univ)
    (hv : cl.vars[0]? = some Srt.int) {σ : Subst} {vs : List GroundTerm} (ha : cl.AppliesAt d σ vs) :
    ∃ x, vs = [x] ∧ σ.lookup 0 = some x ∧ d.sortOf x = some Srt.int := by
  have hm : PatVals d σ [.var 0] vs := hp ▸ ha.2.1
  obtain ⟨x, vs', rfl, hx, hs⟩ := PatVals.cons_inv hm
  obtain rfl : vs' = [] := by cases hs; rfl
  obtain ⟨v, hv0, hvs⟩ := ha.1 0 hu Srt.int hv
  have e : some v = some x := hv0.symm.trans (PatVal.var_inv hx)
  obtain rfl := Option.some.inj e
  exact ⟨v, rfl, hv0, hvs⟩

theorem coh_clF (H : HookParams) : Coherent (cH H) clF clF := by
  intro vs σ σ' ha ha' _ _ _ _ _
  obtain ⟨x, rfl, h0, -⟩ := match0 (d := cH H) rfl (by decide) rfl ha
  obtain ⟨x', hx', h0', -⟩ := match0 (d := cH H) rfl (by decide) rfl ha'
  cases hx'
  refine .inl ⟨rfl, rfl, rfl, rfl, fun i hi => ?_, fun t ht => nomatch ht⟩
  simp [clF, varOccs] at hi
  subst hi; rw [h0, h0']

theorem coh_clG (H : HookParams) : Coherent (cH H) clG clG := by
  intro vs σ σ' ha ha' _ _ _ _ _
  obtain ⟨x, rfl, h0, -⟩ := match0 (d := cH H) rfl (by decide) rfl ha
  obtain ⟨x', hx', h0', -⟩ := match0 (d := cH H) rfl (by decide) rfl ha'
  cases hx'
  refine .inl ⟨rfl, rfl, rfl, rfl, fun i hi => ?_, fun t ht => nomatch ht⟩
  simp [clG, varOccs, varOccsList] at hi
  subst hi; rw [h0, h0']

theorem coh_clH (H : HookParams) : Coherent (cH H) clH clH := by
  intro vs σ σ' ha ha' _ _ _ _ _
  obtain ⟨x, rfl, h0, hx⟩ := match0 (d := cH H) rfl (by decide) rfl ha
  obtain ⟨x', hx', h0', -⟩ := match0 (d := cH H) rfl (by decide) rfl ha'
  cases hx'
  refine .inr fun r r' hr hr' => ?_
  have hne : clH.exs ≠ [] := by decide
  rcases hr with ⟨he, -⟩ | ⟨-, hr⟩
  · exact absurd he hne
  rcases hr' with ⟨he, -⟩ | ⟨-, hr'⟩
  · exact absurd he hne
  rw [resEx_h H h0 hx hr, resEx_h H h0' hx hr']

/-- **Every function has at most one result, for every H**: f's, g's and h's one clause is
coherent with itself (h's by `resEx_h`: its result at a match is X's value), and a sort
predicate's clauses as in `Faithful.fnDet_of_agree`. -/
theorem fnDetH (H : HookParams) : FnDet (cH H) := by
  refine fnDet_of_coherent fun f fn hfn cl hcl cl' hcl' hprio => ?_
  obtain ⟨hmem, -⟩ := lookupFn_spec hfn
  rcases List.mem_append.mp hmem with hu | hp
  · have hfns : (cH H).fns = [fnF, fnG, fnH] := read
    rw [hfns] at hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl
    · simp only [fnF, List.mem_singleton] at hcl hcl'; subst hcl hcl'; exact coh_clF H
    · simp only [fnG, List.mem_singleton] at hcl hcl'; subst hcl hcl'; exact coh_clG H
    · simp only [fnH, List.mem_singleton] at hcl hcl'; subst hcl hcl'; exact coh_clH H
  · by_cases he : cl = cl'
    · subst he
      intro vs σ σ' _ _ _ _ _ _ _
      refine Or.inl ⟨Semantics.sortPreds_exs hp cl hcl, Semantics.sortPreds_exs hp cl hcl, rfl, rfl,
        fun i hi => absurd hi ?_, fun t ht => ?_⟩
      · obtain ⟨s', lit, hr⟩ := sortPreds_rhs hp cl hcl
        rw [hr, varOccs]
        exact List.not_mem_nil
      · rw [sortPreds_ens hp cl hcl] at ht; cases ht
    · rcases mem_pairs_of_ne hcl hcl' he with hpr | hpr
      · exact (sortPreds_agree hp cl cl' hpr hprio).1
      · refine (sortPreds_agree hp cl' cl hpr ?_).2
        rcases hprio with h | h | h
        · exact .inl h.symm
        · exact .inr (.inr h)
        · exact .inr (.inl h)


/-- **The right-side predicates have truth values, for every H**: f's and g's are `\top`, h's is
decided where f and g each have one result. -/
theorem postDecH (H : HookParams) : ClausePostDecided (cH H) := by
  intro fn hfn cl hcl σ hσ
  have hfns : (cH H).fns = [fnF, fnG, fnH] := read
  rw [hfns] at hfn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl | rfl
  · simp only [fnF, List.mem_singleton] at hcl; subst hcl; exact ⟨true, .top⟩
  · simp only [fnG, List.mem_singleton] at hcl; subst hcl; exact ⟨true, .top⟩
  · simp only [fnH, List.mem_singleton] at hcl; subst hcl
    obtain ⟨x, h0, hx⟩ := hσ 0 Srt.int rfl
    obtain ⟨w, h1, -⟩ := hσ 1 Srt.int rfl
    obtain ⟨rg, hf, hg⟩ := fg_only H hx
    exact ⟨_, (dec_post (funF H) (funG H) hf hg h0 h1).1⟩

/-- **Evaluation solves f's equation, for every H.** -/
theorem solvesF (H : HookParams) : FnSolvesAt (cH H) fnF := by
  intro vs _ cl hcl σ hdec v
  simp only [fnF, List.mem_singleton] at hcl; subst hcl
  obtain ⟨x, rfl, h0, hx⟩ := match0 (d := cH H) rfl (by decide) rfl hdec.1
  have hf := f_only (lookupFH H) hx
  have hws : (cH H).WellSorted clF.vars σ := (wellSortedAt_univ rfl).mp hdec.1.1
  constructor
  · intro he
    obtain rfl : v = x := Option.some.inj (hf.2 _ he)
    exact ⟨σ, fun _ _ => rfl, hws, h0 ▸ .var, (fun t ht => nomatch ht), .top⟩
  · rintro ⟨σ', hag, -, hy, -, -⟩
    have h0' : σ'.lookup 0 = σ.lookup 0 := hag 0 (by simp [Clause.exsFree, clF])
    have e := EvalTerm.var_inv hy
    rw [h0', h0] at e
    cases e
    exact hf.1

/-- **Evaluation solves g's equation, for every H.** -/
theorem solvesG (H : HookParams) : FnSolvesAt (cH H) fnG := by
  intro vs _ cl hcl σ hdec v
  simp only [fnG, List.mem_singleton] at hcl; subst hcl
  obtain ⟨x, rfl, h0, hx⟩ := match0 (d := cH H) rfl (by decide) rfl hdec.1
  obtain ⟨n, rfl⟩ := shape_int (shapesH H) hx
  have hg := g_only (subNotCtor H) (lookupGH H) n
  have hws : (cH H).WellSorted clG.vars σ := (wellSortedAt_univ rfl).mp hdec.1.1
  constructor
  · intro he
    obtain rfl : v = int (0 - n) := Option.some.inj (hg.2 _ he)
    exact ⟨σ, fun _ _ => rfl, hws, evalSub (subNotCtor H) h0, (fun t ht => nomatch ht), .top⟩
  · rintro ⟨σ', hag, -, hy, -, -⟩
    have h0' : σ'.lookup 0 = some (int n) := (hag 0 (by simp [Clause.exsFree, clG])).trans h0
    obtain rfl := Option.some.inj (evalSub_inv (subNotCtor H) h0' hy)
    exact hg.1

/-- **The theory has a model, for every H** (`consistent_of_fnMany_agree` at h). -/
theorem consistent (H : HookParams) : Consistent (cH H) :=
  consistent_of_rest H (fnDetH H) (solvesF H) (solvesG H) (postDecH H)

/-- A result of h's clause at a match giving X the value n is `0 - n`: the instance at
#Or0 := `0 - n` has `post` true (`g(n)` is `0 - n`) and gives `0 - n` alone. -/
theorem resEx_neg (H : HookParams) {σ : Subst} {n : Int} {r : Option GroundTerm}
    (h0 : σ.lookup 0 = some (int n)) (h : clH.ResEx (cH H) σ r) : r = some (int (0 - n)) := by
  have hx := rmS_sortOf_int (cH H) n
  have hf := f_only (lookupFH H) hx
  have hg := g_only (subNotCtor H) (lookupGH H) n
  have hp : postVal (int (0 - n)) (some (int n)) (some (int (0 - n))) = true := by
    simp [postVal, sameResult_self]
  have ht := inst_true (funF H) (funG H) hf hg (ext_x h0 _) (lkSelf _ _ _) hp
  have hag : AgreeOff clH.exsFree σ ((1, int (0 - n)) :: σ) := agree_set1 σ _
  have hws := ext_sorted h0 hx (rmS_sortOf_int _ (0 - n))
  rcases h with ⟨σ₁, v, -, -, -, hall, rfl⟩ | ⟨rfl, -, hall⟩
  · exact ht.2 _ (hall _ hag hws)
  · exact absurd (ht.2 _ (hall _ hag hws)) (by simp)

/-- **h's clause is not match independent, for every H**: it decides at `[1]` and has no result
there (a result would be 1, `resEx_h`, and `0 - 1`, `resEx_neg`). -/
theorem h_not_matchIndependent (H : HookParams) : ¬ MatchIndependent (cH H) clH := by
  intro hm
  have hx := rmS_sortOf_int (cH H) 1
  have hs : (cH H).WellSorted clH.vars [(1, int 1), (0, int 1)] := sorted2 rfl hx rfl hx
  have hdec : clH.Decides (cH H) fnH [(1, int 1), (0, int 1)] [int 1] :=
    ⟨⟨hs.at _, .cons (.var rfl) .nil, (fun t ht => nomatch ht), Holds.top⟩, fun cl' hcl' _ hlt => by
      simp only [fnH, List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _)⟩
  obtain ⟨r, hr⟩ := hm.2 (by decide) fH fnH [int 1] _ (lookupHH H) (List.mem_singleton_self _) hdec
  rcases hr with ⟨he, -⟩ | ⟨-, hr⟩
  · exact absurd he (by decide)
  have e1 := resEx_h H (σ := [(1, int 1), (0, int 1)]) rfl hx hr
  have e2 := resEx_neg H (σ := [(1, int 1), (0, int 1)]) rfl hr
  rw [e1] at e2
  have : (1 : Int) = 0 - 1 := by simpa [KCore.int] using e2
  omega

end FnManyOverOr

/-- info: 'FnManyOverOr.lists_h' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FnManyOverOr.lists_h
/-- info: 'FnManyOverOr.avoidsOffH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FnManyOverOr.avoidsOffH
/-- info: 'FnManyOverOr.consistent_of_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FnManyOverOr.consistent_of_rest
/-- info: 'FnManyOverOr.fnDetH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FnManyOverOr.fnDetH
/-- info: 'FnManyOverOr.consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FnManyOverOr.consistent
/-- info: 'FnManyOverOr.h_not_matchIndependent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FnManyOverOr.h_not_matchIndependent
