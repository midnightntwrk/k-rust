/-
  The held existential variables of test/HeldFixtures.lean, under every interpretation of the
  parameters: the four texts e3-vars-map, e3-vars-map-rest, e3-vars-set and e3-vars-list (copied to
  f2-examples as `heldmap`, `heldmaprest`, `heldset` and `exvarslist.kompile.kore`; each is its
  fixture's text up to the Source and Location attributes), each read by the reader, each statement
  over `c0.withHooks H` for every `H : HookParams`, `c0` the reading.
  Run from the package root: `lake env lean -j1 test/HeldFixturesH.lean`.

  ## Why no statement depends on H
  An interpretation enters evaluation in three places: a parameter symbol without a registry hook
  (`Semantics.paramVal`), an interpreted symbol at a silent point where the registry gives no value
  (`Semantics.hookRes`, `fallback`), and the sort of an open generator's application
  (`Semantics.sortOf`). These texts apply the element and concatenation symbols of Map, Set and
  List. Each is an interpreted hooked symbol and no parameter (`syms_ok` of each namespace: `isHook`,
  evaluated by `EvalTerm.hook`), and none has a silent point (`not_silent_fxv`), so its result is the
  registry's at every argument list, including the lists where it has none: the concatenation of two
  maps with a shared key and of two sets with a shared element. No parameter of the texts is an
  open generator (`noRaw0`), so every value has the sort the parsed data gives it (`sortOf_eq`).
  So each statement below, the ones at the excluded key among them, holds for every H; none reads
  the registry's value of a symbol H can change.

  ## The statements, per text
  - `step_iff H`: the `Step` successors of the start configuration are exactly the instances of the
    right side at the Ints where it has a value (every Int for the map's value and the list; every
    Int but 1 for the set and the map's key).
  - `sound_xy H`: in every model of `Γc`, the start configuration has a successor among the
    instances (`•famEx`), and each `Step` successor is one (`sound_at`).
  - `exact_y H`: by `ExactC`, y is a successor in some model of `Γc` with the step's closure exactly
    where `Step` has it.
  - for the set and the map with a rest, at the excluded key: `rhs_none_at_key H` (the right side
    has no value there), `no_step_at_key H` (no step by the rule binds the variable to it) and
    `concat_key_bot H` (in every model of `Γc` the concatenation there has no element).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace HeldFixturesH

section Shared

open ML Faithful

variable {c : Semantics} {σ : Subst}

/-- An application of an interpreted hooked symbol that is no constructor has the result `hookRes`
gives its arguments' results, and none where an argument has none. -/
theorem evalHook_inv_fxv {f : Sym} {ts : List Term} {r : Option GroundTerm}
    (hc : c.isCtor f = false) (hh : isHook f = true) (h : EvalTerm c σ (.app f ts) r) :
    ∃ rs, EvalTerms c σ ts rs ∧ (∀ vs, allSome rs = some vs → c.hookRes f vs = some r) ∧
      (allSome rs = none → r = none) := by
  generalize ht : Term.app f ts = t at h
  cases h with
  | hook _ _ hts hh' hund => cases ht; exact ⟨_, hts, hh', hund⟩
  | ctor h _ => cases ht; rw [hc] at h; cases h
  | param _ h _ _ _ => cases ht; rw [hh] at h; cases h
  | call _ h _ _ _ _ => cases ht; rw [hh] at h; cases h
  | callUndef _ h _ _ _ => cases ht; rw [hh] at h; cases h
  | ovl _ ho _ => cases ht; rw [(c.isOvl_parts ho).2.1] at hh; cases hh
  | ovlFn _ ho => cases ht; rw [(c.isOvl_parts ho).2.1] at hh; cases hh
  | _ => cases ht

/-- A constructor application has the sort of another of the same constructor whose arguments have
the same sorts. -/
theorem sortOf_ctor_congr_fxv {f : Sym} {ts ts0 : List GroundTerm}
    (hl : (lookupSig c.ctorSigs f).isSome = true)
    (h : c.sortsOf ts = c.sortsOf ts0) : c.sortOf (.ctor f ts) = c.sortOf (.ctor f ts0) := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hl
  simp only [Semantics.sortOf, hk, h]

theorem sortsOf_cons_congr_fxv {t t0 : GroundTerm} {ts ts0 : List GroundTerm} (h : c.sortOf t = c.sortOf t0)
    (hs : c.sortsOf ts = c.sortsOf ts0) : c.sortsOf (t :: ts) = c.sortsOf (t0 :: ts0) := by
  simp only [Semantics.sortsOf, h, hs]

theorem sortOf_inj_congr_fxv {a b : Srt} {t t0 : GroundTerm} (h : c.sortOf t = c.sortOf t0)
    (hi : t.isInj = t0.isInj) : c.sortOf (.inj a b t) = c.sortOf (.inj a b t0) := by
  simp only [Semantics.sortOf, h, hi]

/-- `inj{Int, KItem}(i)`. -/
def ki (i : Int) : GroundTerm := .inj Srt.int Srt.kitem (int i)

/-- An Int injected into KItem has the sort of `inj{Int, KItem}(0)`. -/
theorem sortOf_ki_fxv (i : Int) : c.sortOf (ki i) = c.sortOf (ki 0) :=
  sortOf_inj_congr_fxv (by rw [sortOf_int, sortOf_int]) rfl

/-- A map of `Map` with sorted keys whose entries are Ints injected into KItem is a value of `Map`,
in a semantics whose `Map` is the library's. -/
theorem sortOf_map_ki_fxv
    (hco : c.collOf Srt.map = some ⟨Srt.map, .map, Srt.kitem, some Srt.kitem, mapUnit, mapElem, mapConcat⟩)
    (hki : ∀ j, c.sortOf (ki j) = some Srt.kitem) {es : Entries} (hs : keysSorted es = true)
    (he : ∀ e ∈ es, ∃ a b, e = (ki a, ki b)) : c.sortOf (.map Srt.map es) = some Srt.map := by
  have hok : c.entriesOK Srt.kitem Srt.kitem es = true := KCore.Map.entriesOK_iff.mpr fun e hm => by
    obtain ⟨a, b, rfl⟩ := he e hm
    simp only [Semantics.entryOK, hki, beq_self_eq_true, Bool.and_self]
  simp only [Semantics.sortOf, hco, hs, hok, Bool.and_self, ↓reduceIte]

/-- `ki a` and `ki b` are equal in `GroundTerm.cmp` exactly where a and b are equal. -/
theorem cmp_ki_fxv (a b : Int) : GroundTerm.cmp (ki a) (ki b) = .eq ↔ a = b := by
  rw [cmp_eq_iff]; simp [ki, int]

/-- The element symbols and the concatenations of sets and lists, at values. -/
theorem hook_setElem_fxv (k : GroundTerm) : hook setElem [k] = some (some (.set Srt.set [k])) := rfl
theorem hook_setConcat_fxv (s t : Srt) (a b : List GroundTerm) :
    hook setConcat [.set s a, .set t b] = some ((concatS a b).map (.set Srt.set)) := rfl
theorem hook_listElem_fxv (k : GroundTerm) : hook listElem [k] = some (some (.list Srt.list [k])) := rfl
theorem hook_listConcat_fxv (s t : Srt) (a b : List GroundTerm) :
    hook listConcat [.list s a, .list t b] = some (some (.list Srt.list (a ++ b))) := rfl

/-- A list of Ints injected into KItem has the sorts KItem. -/
theorem sortsOf_ki_fxv (hki : ∀ j, c.sortOf (ki j) = some Srt.kitem) :
    ∀ {es : List GroundTerm}, (∀ e ∈ es, ∃ j, e = ki j) → c.sortsOf es = some (es.map fun _ => Srt.kitem)
  | [], _ => rfl
  | e :: es, h => by
    obtain ⟨j, rfl⟩ := h e (by simp)
    simp only [Semantics.sortsOf, hki, sortsOf_ki_fxv hki (fun e he => h e (List.mem_cons_of_mem _ he)),
      List.map_cons]

/-- A sorted set of `Set` of Ints injected into KItem is a value of `Set`, in a semantics whose
`Set` is the library's. -/
theorem sortOf_set_ki_fxv
    (hco : c.collOf Srt.set = some ⟨Srt.set, .set, Srt.kitem, none, setUnit, setElem, setConcat⟩)
    (hki : ∀ j, c.sortOf (ki j) = some Srt.kitem) {es : List GroundTerm} (hs : elemsSorted es = true)
    (he : ∀ e ∈ es, ∃ j, e = ki j) : c.sortOf (.set Srt.set es) = some Srt.set := by
  simp [Semantics.sortOf, hco, sortsOf_ki_fxv hki he, hs]

/-- A list of `List` of Ints injected into KItem is a value of `List`, in a semantics whose `List`
is the library's. -/
theorem sortOf_list_ki_fxv
    (hco : c.collOf Srt.list = some ⟨Srt.list, .list, Srt.kitem, none, listUnit, listElem, listConcat⟩)
    (hki : ∀ j, c.sortOf (ki j) = some Srt.kitem) {es : List GroundTerm}
    (he : ∀ e ∈ es, ∃ j, e = ki j) : c.sortOf (.list Srt.list es) = some Srt.list := by
  simp [Semantics.sortOf, hco, sortsOf_ki_fxv hki he]


/-- No element or concatenation symbol of Map, Set or List has a silent point: its result is the
registry's at every argument list, whatever the interpretation. -/
theorem not_silent_fxv : silentKey mapElem = false ∧ silentKey mapConcat = false ∧ silentKey setElem = false ∧
    silentKey setConcat = false ∧ silentKey listElem = false ∧ silentKey listConcat = false := by
  decide

/-! The conditions of the parsed data that the proofs read do not read the interpretation. -/
theorem isCtor_wh_fxv (c : Semantics) (H : HookParams) (f : Sym) : (c.withHooks H).isCtor f = c.isCtor f := rfl
theorem rules_wh_fxv (c : Semantics) (H : HookParams) : (c.withHooks H).rules = c.rules := rfl
theorem fns_wh_fxv (c : Semantics) (H : HookParams) : (c.withHooks H).fns = c.fns := rfl
theorem params_wh_fxv (c : Semantics) (H : HookParams) : (c.withHooks H).params = c.params := rfl
theorem shapesOK_wh_fxv (c : Semantics) (H : HookParams) : (c.withHooks H).shapesOK = c.shapesOK := rfl
theorem ctorSigs_wh_fxv (c : Semantics) (H : HookParams) : (c.withHooks H).ctorSigs = c.ctorSigs := rfl
theorem collOf_wh_fxv (c : Semantics) (H : HookParams) (s : Srt) : (c.withHooks H).collOf s = c.collOf s := rfl

end Shared

namespace Map

open ML Faithful

definition_of defn from "f2-examples/heldmap.kompile.kore"

noncomputable abbrev c0 : Semantics := defn.sem

theorem coreOK0 : c0.coreOK = true := by decide_cheap
theorem noRaw0 : ∀ k ∈ c0.params, k.raw = false := by decide +kernel

variable {H : HookParams}

/-- A value has the sort the parsed data gives it, under every interpretation: no parameter is an
open generator. -/
theorem sortOf_eq : (c0.withHooks H).sortOf = c0.sortOf := Semantics.sortOf_withHooks c0 H noRaw0
theorem sortsOf_eq : (c0.withHooks H).sortsOf = c0.sortsOf := Semantics.sortsOf_withHooks c0 H noRaw0

/-- Decides a condition of the parsed data stated of `c0.withHooks H`: the condition does not read
the interpretation, so it is rewritten to `c0`'s and decided there. -/
local macro "whd" : tactic => `(tactic| first | decide +kernel | (rw [sortOf_eq]; decide +kernel) | (rw [sortsOf_eq]; decide +kernel) |
  (simp only [isCtor_wh_fxv, rules_wh_fxv, fns_wh_fxv, params_wh_fxv, shapesOK_wh_fxv, ctorSigs_wh_fxv,
    collOf_wh_fxv]; decide +kernel))

def sExp : Srt := 34
def kCell : Sym := 385
def mCell : Sym := 387
def symSet : Sym := 389


theorem coreOK : (c0.withHooks H).coreOK = true := (Semantics.coreOK_withHooks c0 H).trans coreOK0

noncomputable def r0 : Rule := c0.rules[0]'(by decide +kernel)

theorem rules_eq : (c0.withHooks H).rules = [r0] := by
  have h : c0.rules.length = 1 := by decide +kernel
  rw [rules_wh_fxv]
  match hr : c0.rules, h with
  | [r], _ => simp only [r0, hr, List.getElem_cons_zero]

theorem r0_vars : r0.vars = [Srt.int, Srt.k, 19, Srt.int] := rfl
theorem r0_lhs : r0.lhs = .app topLabel [.app kCell [.app kseq [.inj sExp Srt.kitem (.app symSet [.var 0]),
    .var 1]], .app mCell [.app mapUnit []], .var 2] := rfl
theorem r0_rhs : r0.rhs = .app topLabel [.app kCell [.var 1],
    .app mCell [.app mapElem [.inj Srt.int Srt.kitem (.var 0), .inj Srt.int Srt.kitem (.var 3)]], .var 2] := rfl
theorem r0_shape : r0.req = none ∧ r0.ens = none ∧ r0.pre = .top ∧ r0.post = .top ∧ r0.exs = [3] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩


theorem fns_nil : (c0.withHooks H).fns = [] := by whd
theorem noRaw : ∀ k ∈ (c0.withHooks H).params, k.raw = false := by whd
theorem noWitness : ∀ r ∈ (c0.withHooks H).rules, r.needsWitness (c0.withHooks H) = false := by
  intro r hr
  rw [rules_eq] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  have h : r0.reqOpen = false := by decide +kernel
  simp only [Rule.needsWitness, h, Bool.false_and]
theorem shapesOK : (c0.withHooks H).shapesOK = true := by whd

theorem syms_ok : (c0.withHooks H).isCtor topLabel = true ∧ (c0.withHooks H).isCtor kCell = true ∧ (c0.withHooks H).isCtor kseq = true ∧
    (c0.withHooks H).isCtor symSet = true ∧ (c0.withHooks H).isCtor mCell = true ∧ (c0.withHooks H).isCtor dotk = true ∧ (c0.withHooks H).isCtor counterLabel = true ∧
    (c0.withHooks H).isCtor mapElem = false ∧ isHook mapElem = true := by
  whd
theorem hooks_ok : patternHooks.contains topLabel = false ∧ patternHooks.contains kCell = false ∧
    patternHooks.contains kseq = false ∧ patternHooks.contains symSet = false ∧
    patternHooks.contains mCell = false ∧ patternHooks.contains mapUnit = true := by
  whd

/-- The hypothesis on the functions holds: the text declares none, no rule needs a witness and no
parameter is an open generator. -/
theorem fnHyp : FnHyp (c0.withHooks H) :=
  have hn : ∀ fn, fn ∈ (c0.withHooks H).fns → False := fun fn hfn => by rw [fns_nil] at hfn; cases hfn
  ⟨fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim,
    fun fn hfn => (hn fn hfn).elim,
    openDecided_of_plain noWitness (fun fn hfn => (hn fn hfn).elim),
    openLaws_of_plain noRaw⟩

/-! ## The configurations -/

def ctr : GroundTerm := .ctor counterLabel [int 0]

/-- `<k> set(5) ~> . </k> <m> .Map </m>`. -/
def X (H : HookParams) : Config (c0.withHooks H) :=
  ⟨.ctor topLabel [.ctor kCell [.ctor kseq [.inj sExp Srt.kitem (.ctor symSet [int 5]), .ctor dotk []]],
    .ctor mCell [.map Srt.map []], ctr], by whd⟩

/-- The configuration `<k> . </k> <m> 5 |-> i </m>`. -/
def cfgY (i : Int) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor dotk []], .ctor mCell [.map Srt.map [(ki 5, ki i)]], ctr]

theorem lookups_ok : (lookupSig (c0.withHooks H).ctorSigs topLabel).isSome = true ∧ (lookupSig (c0.withHooks H).ctorSigs mCell).isSome = true := by
  whd

theorem collOf_map : (c0.withHooks H).collOf Srt.map = some ⟨Srt.map, .map, Srt.kitem, some Srt.kitem, mapUnit, mapElem, mapConcat⟩ := by
  whd

theorem sortOf_ki (j : Int) : (c0.withHooks H).sortOf (ki j) = some Srt.kitem := by
  rw [sortOf_ki_fxv j]; whd

/-- `<k> . </k> <m> 5 |-> i </m>` is a configuration for every Int i, as `5 |-> 0` is. -/
theorem sortOf_cfgY (i : Int) : (c0.withHooks H).sortOf (cfgY i) = some topCellSort := by
  have h0 : (c0.withHooks H).sortOf (cfgY 0) = some topCellSort := by whd
  rw [← h0]
  have hm : (c0.withHooks H).sortOf (.map Srt.map [(ki 5, ki i)]) = (c0.withHooks H).sortOf (.map Srt.map [(ki 5, ki 0)]) := by
    simp only [Semantics.sortOf, collOf_map, Semantics.entriesOK, Semantics.entryOK, keysSorted, sortOf_ki]
  exact sortOf_ctor_congr_fxv (lookups_ok (H := H)).1 (sortsOf_cons_congr_fxv rfl
    (sortsOf_cons_congr_fxv (sortOf_ctor_congr_fxv (lookups_ok (H := H)).2 (sortsOf_cons_congr_fxv hm rfl)) rfl))

def Y (H : HookParams) (i : Int) : Config (c0.withHooks H) := ⟨cfgY i, sortOf_cfgY i⟩

/-! ## `Step` from `set(5)` to `5 |-> i`, for every Int i -/

def σ (i : Int) : Subst := [(0, int 5), (1, .ctor dotk []), (2, ctr), (3, int i)]

theorem hmatchX (τ : Subst) (h0 : τ.lookup 0 = some (int 5)) (h1 : τ.lookup 1 = some (.ctor dotk []))
    (h2 : τ.lookup 2 = some ctr) : PatVal (c0.withHooks H) τ r0.lhs (X H).val := by
  rw [r0_lhs]
  exact .ctor (syms_ok (H := H)).1 (.cons (.ctor (syms_ok (H := H)).2.1 (.cons (.ctor (syms_ok (H := H)).2.2.1
    (.cons (.inj (.ctor (syms_ok (H := H)).2.2.2.1 (.cons (.var h0) .nil))) (.cons (.var h1) .nil))) .nil))
    (.cons (.ctor (syms_ok (H := H)).2.2.2.2.1 (.cons (.hook hooks_ok.2.2.2.2.2 .nil rfl) .nil)) (.cons (.var h2) .nil)))

/-- `K |-> V` at K := 5, V := i is the map `5 |-> i`. -/
theorem elemEval (i : Int) : EvalTerm (c0.withHooks H) (σ i)
    (.app mapElem [.inj Srt.int Srt.kitem (.var 0), .inj Srt.int Srt.kitem (.var 3)])
    (some (.map Srt.map [(ki 5, ki i)])) :=
  .hook (syms_ok (H := H)).2.2.2.2.2.2.2.1 (syms_ok (H := H)).2.2.2.2.2.2.2.2 (.cons (.inj .var) (.cons (.inj .var) .nil))
    (fun vs hvs => by
      obtain rfl : vs = [ki 5, ki i] := (Option.some.inj (show some [ki 5, ki i] = some vs from hvs)).symm
      exact Semantics.hookRes_of_value (Exec.hook_mapElem _ _))
    (fun h => nomatch (show some [ki 5, ki i] = none from h))

/-- **`set(5)` steps to `5 |-> i`** by the rule, V := i. -/
theorem stepBy (i : Int) : StepBy (c0.withHooks H) r0 (σ i) (X H) (Y H i) where
  mem := by rw [rules_eq]; simp
  hσ := fun j s hs => by
    rw [r0_vars] at hs
    match j, hs with
    | 0, hs => cases hs; exact ⟨_, rfl, sortOf_int 5⟩
    | 1, hs => cases hs; exact ⟨_, rfl, by whd⟩
    | 2, hs => cases hs; exact ⟨_, rfl, by whd⟩
    | 3, hs => cases hs; exact ⟨_, rfl, sortOf_int i⟩
    | _ + 4, hs => simp at hs
  hmatch := hmatchX _ rfl rfl rfl
  hreq := fun t ht => by rw [r0_shape.1] at ht; cases ht
  hpre := by rw [r0_shape.2.2.1]; exact .top
  heval := by
    rw [r0_rhs]
    exact .ctor (syms_ok (H := H)).1 (.cons (.ctor (syms_ok (H := H)).2.1 (.cons .var .nil))
      (.cons (.ctor (syms_ok (H := H)).2.2.2.2.1 (.cons (elemEval i) .nil)) (.cons .var .nil)))
  hens := fun t ht => by rw [r0_shape.2.1] at ht; cases ht
  hpost := by rw [r0_shape.2.2.2.1]; exact .top
  hprio := fun r' hr' hlt => by
    rw [rules_eq] at hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst hr'
    exact absurd hlt (Nat.lt_irrefl _)

theorem step (i : Int) : Step (c0.withHooks H) (X H) (Y H i) := step_iff_by.mpr ⟨r0, σ i, stepBy i⟩

/-! ## No other successor -/

/-- **What the left side denotes**: `<k> set(k) ~> w </k> <m> m </m>` with the counter cell u, k, w
and u the values σ gives the variables 0, 1 and 2. -/
theorem lhs_inv {τ : Subst} {x : GroundTerm} (h : PatVal (c0.withHooks H) τ r0.lhs x) :
    ∃ k w m u, x = .ctor topLabel [.ctor kCell [.ctor kseq [.inj sExp Srt.kitem (.ctor symSet [k]), w]],
      .ctor mCell [m], u] ∧ τ.lookup 0 = some k ∧ τ.lookup 1 = some w ∧ τ.lookup 2 = some u := by
  rw [r0_lhs] at h
  obtain ⟨-, vs, rfl, hvs⟩ := PatVal.app_inv hooks_ok.1 h (syms_ok (H := H)).1
  obtain ⟨v1, vs1, rfl, h1, hvs1⟩ := hvs.cons_inv
  obtain ⟨v2, vs2, rfl, h2, hvs2⟩ := hvs1.cons_inv
  obtain ⟨u, vs3, rfl, h3, hvs3⟩ := hvs2.cons_inv
  cases hvs3.nil_inv
  obtain ⟨-, ws, rfl, hws⟩ := PatVal.app_inv hooks_ok.2.1 h1 (syms_ok (H := H)).2.1
  obtain ⟨w1, ws1, rfl, h11, hws1⟩ := hws.cons_inv
  cases hws1.nil_inv
  obtain ⟨-, ns, rfl, hns⟩ := PatVal.app_inv hooks_ok.2.2.2.2.1 h2 (syms_ok (H := H)).2.2.2.2.1
  obtain ⟨m, ns1, rfl, -, hns1⟩ := hns.cons_inv
  cases hns1.nil_inv
  obtain ⟨-, zs, rfl, hzs⟩ := PatVal.app_inv hooks_ok.2.2.1 h11 (syms_ok (H := H)).2.2.1
  obtain ⟨z1, zs1, rfl, hz1, hzs1⟩ := hzs.cons_inv
  obtain ⟨w, zs2, rfl, hz2, hzs2⟩ := hzs1.cons_inv
  cases hzs2.nil_inv
  obtain ⟨a, ha, rfl⟩ := PatVal.inj_inv hz1
  obtain ⟨-, as, rfl, has⟩ := PatVal.app_inv hooks_ok.2.2.2.1 ha (syms_ok (H := H)).2.2.2.1
  obtain ⟨k, as1, rfl, hk, has1⟩ := has.cons_inv
  cases has1.nil_inv
  exact ⟨k, w, m, u, rfl, PatVal.var_inv hk, PatVal.var_inv hz2, PatVal.var_inv h3⟩

/-- **Every `Step` successor of `<k> set(5) </k> <m> .Map </m>` is a `5 |-> i`.** -/
theorem step_inv {y : Config (c0.withHooks H)} (hs : Step (c0.withHooks H) (X H) y) : ∃ i : Int, y = Y H i := by
  obtain ⟨r, τ, hb⟩ := step_iff_by.mp hs
  have hr := hb.mem
  rw [rules_eq] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  obtain ⟨k, w, m, u, hx, h0, h1, h2⟩ := lhs_inv hb.hmatch
  simp only [X, GroundTerm.ctor.injEq, GroundTerm.inj.injEq, List.cons.injEq, and_true, true_and] at hx
  obtain ⟨⟨rfl, rfl⟩, -, rfl⟩ := hx
  obtain ⟨v, h3, hv⟩ := hb.hσ 3 Srt.int (by rw [r0_vars]; rfl)
  obtain ⟨i, rfl⟩ := shape_int shapesOK hv
  refine ⟨i, Subtype.ext ?_⟩
  have h := hb.heval
  rw [r0_rhs] at h
  obtain ⟨rs, hrs, he⟩ := EvalTerm.ctor_inv (syms_ok (H := H)).1 h
  obtain ⟨q1, rs1, rfl, hq1, hrs1⟩ := hrs.cons_inv
  obtain ⟨q2, rs2, rfl, hq2, hrs2⟩ := hrs1.cons_inv
  obtain ⟨q3, rs3, rfl, hq3, hrs3⟩ := hrs2.cons_inv
  cases hrs3.nil_inv
  rw [hq3.var_inv, h2] at he
  obtain ⟨ps, hps, rfl⟩ := EvalTerm.ctor_inv (syms_ok (H := H)).2.1 hq1
  obtain ⟨p1, ps1, rfl, hp1, hps1⟩ := hps.cons_inv
  cases hps1.nil_inv
  rw [hp1.var_inv, h1] at he
  obtain ⟨ms, hms, rfl⟩ := EvalTerm.ctor_inv (syms_ok (H := H)).2.2.2.2.1 hq2
  obtain ⟨m1, ms1, rfl, hm1, hms1⟩ := hms.cons_inv
  cases hms1.nil_inv
  obtain ⟨es, hes, hh, -⟩ := evalHook_inv_fxv (syms_ok (H := H)).2.2.2.2.2.2.2.1 (syms_ok (H := H)).2.2.2.2.2.2.2.2 hm1
  obtain ⟨e1, es1, rfl, he1, hes1⟩ := hes.cons_inv
  obtain ⟨e2, es2, rfl, he2, hes2⟩ := hes1.cons_inv
  cases hes2.nil_inv
  obtain ⟨e1', he1', rfl⟩ := EvalTerm.inj_inv he1
  obtain ⟨e2', he2', rfl⟩ := EvalTerm.inj_inv he2
  rw [he1'.var_inv, h0, he2'.var_inv, h3] at hh
  have hm := hh _ rfl
  rw [Semantics.hookRes_of_value (Exec.hook_mapElem _ _)] at hm
  cases hm
  simp only [allSome, Option.bind, Option.map, injNormal, Option.some.injEq] at he
  exact he

/-- **The successors of `<k> set(5) </k> <m> .Map </m>`** are exactly the `5 |-> i`, i an Int. -/
theorem step_iff (H : HookParams) (y : Config (c0.withHooks H)) : Step (c0.withHooks H) (X H) y ↔ ∃ i : Int, y = Y H i :=
  ⟨step_inv, fun ⟨i, hi⟩ => hi ▸ step i⟩

/-- **In every model of `Γc`, `<k> set(5) </k> <m> .Map </m>` has a successor among the instances of
the application, and `5 |-> i` is one of them**, for every Int i (`sound_at`; no competitor, no
function). -/
theorem sound_xy (H : HookParams) (i : Int) :
    (Γc (c0.withHooks H) ⊧ (den (c0.withHooks H) (X H).val ⇒ KoreAML.sNext (famEx (c0.withHooks H) r0 (σ i)))) ∧ (Γc (c0.withHooks H) ⊧ (den (c0.withHooks H) (Y H i).val ⇒ famEx (c0.withHooks H) r0 (σ i))) :=
  sound_at (c0.withHooks H) coreOK (X H) (Y H i) r0 (σ i) (stepBy i)
    (fun r' hr' hlt _ _ => by
      rw [rules_eq] at hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      subst hr'
      exact absurd hlt (Nat.lt_irrefl _))
    (fun fn hfn => by rw [fns_nil] at hfn; cases hfn)

/-- **By `ExactC`**: y is a successor of `<k> set(5) </k> <m> .Map </m>` in some model of `Γc` with
the step's closure exactly where y is some `5 |-> i`; in no model is another value a successor. -/
theorem exact_y (H : HookParams) (y : Config (c0.withHooks H)) :
    (∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
      (I ⊧ᴵP (Γc (c0.withHooks H) ∪ Γstep (c0.withHooks H))) ∧ ¬ (I ⊧ᴵ (den (c0.withHooks H) (X H).val ⇒ ∼ KoreAML.sNext (den (c0.withHooks H) y.val)))) ↔
    ∃ i : Int, y = Y H i := by
  rw [← exact_hyp (c0.withHooks H) coreOK fnHyp (X H) y]
  exact step_iff H y

/-- info: 'HeldFixturesH.Map.step_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_iff
/-- info: 'HeldFixturesH.Map.sound_xy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sound_xy
/-- info: 'HeldFixturesH.Map.exact_y' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms exact_y

end Map

namespace MapRest

open ML Faithful

definition_of defn from "f2-examples/heldmaprest.kompile.kore"

noncomputable abbrev c0 : Semantics := defn.sem

theorem coreOK0 : c0.coreOK = true := by decide_cheap
theorem noRaw0 : ∀ k ∈ c0.params, k.raw = false := by decide +kernel

variable {H : HookParams}

/-- A value has the sort the parsed data gives it, under every interpretation: no parameter is an
open generator. -/
theorem sortOf_eq : (c0.withHooks H).sortOf = c0.sortOf := Semantics.sortOf_withHooks c0 H noRaw0
theorem sortsOf_eq : (c0.withHooks H).sortsOf = c0.sortsOf := Semantics.sortsOf_withHooks c0 H noRaw0

/-- Decides a condition of the parsed data stated of `c0.withHooks H`: the condition does not read
the interpretation, so it is rewritten to `c0`'s and decided there. -/
local macro "whd" : tactic => `(tactic| first | decide +kernel | (rw [sortOf_eq]; decide +kernel) | (rw [sortsOf_eq]; decide +kernel) |
  (simp only [isCtor_wh_fxv, rules_wh_fxv, fns_wh_fxv, params_wh_fxv, shapesOK_wh_fxv, ctorSigs_wh_fxv,
    collOf_wh_fxv]; decide +kernel))

def sExp : Srt := 34
def kCell : Sym := 385
def mCell : Sym := 387
def symGo : Sym := 389


theorem coreOK : (c0.withHooks H).coreOK = true := (Semantics.coreOK_withHooks c0 H).trans coreOK0

noncomputable def r0 : Rule := c0.rules[0]'(by decide +kernel)

theorem rules_eq : (c0.withHooks H).rules = [r0] := by
  have h : c0.rules.length = 1 := by decide +kernel
  rw [rules_wh_fxv]
  match hr : c0.rules, h with
  | [r], _ => simp only [r0, hr, List.getElem_cons_zero]

theorem r0_vars : r0.vars = [Srt.k, Srt.map, 19, Srt.int] := rfl
theorem r0_lhs : r0.lhs = .app topLabel [.app kCell [.app kseq [.inj sExp Srt.kitem (.app symGo []),
    .var 0]], .app mCell [.var 1], .var 2] := rfl
theorem r0_rhs : r0.rhs = .app topLabel [.app kCell [.var 0],
    .app mCell [.app mapConcat [.app mapElem [.inj Srt.int Srt.kitem (.var 3),
      .inj Srt.int Srt.kitem (.dv Srt.int (.int 0))], .var 1]], .var 2] := rfl
theorem r0_shape : r0.req = none ∧ r0.ens = none ∧ r0.pre = .top ∧ r0.post = .top ∧ r0.exs = [3] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩


theorem fns_nil : (c0.withHooks H).fns = [] := by whd
theorem noRaw : ∀ k ∈ (c0.withHooks H).params, k.raw = false := by whd
theorem noWitness : ∀ r ∈ (c0.withHooks H).rules, r.needsWitness (c0.withHooks H) = false := by
  intro r hr
  rw [rules_eq] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  have h : r0.reqOpen = false := by decide +kernel
  simp only [Rule.needsWitness, h, Bool.false_and]
theorem shapesOK : (c0.withHooks H).shapesOK = true := by whd

theorem syms_ok : (c0.withHooks H).isCtor topLabel = true ∧ (c0.withHooks H).isCtor kCell = true ∧ (c0.withHooks H).isCtor kseq = true ∧
    (c0.withHooks H).isCtor symGo = true ∧ (c0.withHooks H).isCtor mCell = true ∧ (c0.withHooks H).isCtor dotk = true ∧ (c0.withHooks H).isCtor counterLabel = true ∧
    (c0.withHooks H).isCtor mapElem = false ∧ isHook mapElem = true ∧ (c0.withHooks H).isCtor mapConcat = false ∧ isHook mapConcat = true := by
  whd
theorem hooks_ok : patternHooks.contains topLabel = false ∧ patternHooks.contains kCell = false ∧
    patternHooks.contains kseq = false ∧ patternHooks.contains symGo = false ∧
    patternHooks.contains mCell = false := by
  whd

/-- The hypothesis on the functions holds: the text declares none, no rule needs a witness and no
parameter is an open generator. -/
theorem fnHyp : FnHyp (c0.withHooks H) :=
  have hn : ∀ fn, fn ∈ (c0.withHooks H).fns → False := fun fn hfn => by rw [fns_nil] at hfn; cases hfn
  ⟨fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim,
    fun fn hfn => (hn fn hfn).elim,
    openDecided_of_plain noWitness (fun fn hfn => (hn fn hfn).elim),
    openLaws_of_plain noRaw⟩

/-! ## The configurations -/

def ctr : GroundTerm := .ctor counterLabel [int 0]

/-- The map `1 |-> 0`, whose one key is 1. -/
def m1 : Entries := [(ki 1, ki 0)]

/-- `<k> go() ~> . </k> <m> 1 |-> 0 </m>`. -/
def X (H : HookParams) : Config (c0.withHooks H) :=
  ⟨.ctor topLabel [.ctor kCell [.ctor kseq [.inj sExp Srt.kitem (.ctor symGo []), .ctor dotk []]],
    .ctor mCell [.map Srt.map m1], ctr], by whd⟩

/-- `<k> . </k> <m> es </m>`. -/
def cfgR (es : Entries) : GroundTerm := .ctor topLabel [.ctor kCell [.ctor dotk []], .ctor mCell [.map Srt.map es], ctr]

theorem lookups_ok : (lookupSig (c0.withHooks H).ctorSigs topLabel).isSome = true ∧ (lookupSig (c0.withHooks H).ctorSigs mCell).isSome = true := by
  whd

theorem collOf_map : (c0.withHooks H).collOf Srt.map = some ⟨Srt.map, .map, Srt.kitem, some Srt.kitem, mapUnit, mapElem, mapConcat⟩ := by
  whd

theorem sortOf_ki (j : Int) : (c0.withHooks H).sortOf (ki j) = some Srt.kitem := by
  rw [sortOf_ki_fxv j]; whd

/-- k is a key of `1 |-> 0` exactly where it is 1. -/
theorem hasKey_m1 (k : Int) : hasKey (ki k) m1 = true ↔ k = 1 := by
  simp only [hasKey, m1, List.any_cons, List.any_nil, Bool.or_false, beq_iff_eq, cmp_ki_fxv]

/-- `(k |-> 0) (1 |-> 0)` at k other than 1: `1 |-> 0` with the entry `k |-> 0` inserted in key order. -/
def rest (k : Int) : Entries := insertE (ki k) (ki 0) m1

/-- `<k> . </k> <m> (k |-> 0) (1 |-> 0) </m>` is a configuration for every Int k. -/
theorem sortOf_cfgRest (k : Int) : (c0.withHooks H).sortOf (cfgR (rest k)) = some topCellSort := by
  have h0 : (c0.withHooks H).sortOf (cfgR m1) = some topCellSort := by whd
  rw [← h0]
  have h1 : (c0.withHooks H).sortOf (.map Srt.map (rest k)) = some Srt.map :=
    sortOf_map_ki_fxv collOf_map sortOf_ki (es := rest k) (insertE_sorted (by whd : keysSorted m1 = true))
      fun e he => by
        rcases insertE_mem he with rfl | he
        · exact ⟨k, 0, rfl⟩
        · simp only [m1, List.mem_singleton] at he; exact ⟨1, 0, he⟩
  have h2 : (c0.withHooks H).sortOf (.map Srt.map m1) = some Srt.map := by whd
  have hm : (c0.withHooks H).sortOf (.map Srt.map (rest k)) = (c0.withHooks H).sortOf (.map Srt.map m1) := by rw [h1, h2]
  exact sortOf_ctor_congr_fxv (lookups_ok (H := H)).1 (sortsOf_cons_congr_fxv rfl
    (sortsOf_cons_congr_fxv (sortOf_ctor_congr_fxv (lookups_ok (H := H)).2 (sortsOf_cons_congr_fxv hm rfl)) rfl))

/-- The successor at k. -/
def Y (H : HookParams) (k : Int) : Config (c0.withHooks H) := ⟨cfgR (rest k), sortOf_cfgRest k⟩

/-! ## The concatenation -/

theorem silent_concat (vs : List GroundTerm) : silent mapConcat vs = false := rfl

/-- `(k |-> 0) (1 |-> 0)` has a value exactly where k is no key of `1 |-> 0`, and it is `rest k`. -/
theorem hookRes_concat (k : Int) :
    (c0.withHooks H).hookRes mapConcat [.map Srt.map [(ki k, ki 0)], .map Srt.map m1] =
      some (if k = 1 then none else some (.map Srt.map (rest k))) := by
  rw [Semantics.hookRes_of_not_silent (silent_concat _), Exec.hook_mapConcat]
  by_cases hk : k = 1
  · subst hk; rfl
  · have hn : hasKey (ki k) m1 = false := by
      cases h : hasKey (ki k) m1
      · rfl
      · exact absurd ((hasKey_m1 k).mp h) hk
    simp only [union, Option.bind, addNew, hn, hk, rest, Bool.false_eq_true, ↓reduceIte, Option.map]

/-! ## `Step` from `1 |-> 0` to `(k |-> 0) (1 |-> 0)`, for every Int k other than 1 -/

def σ (k : Int) : Subst := [(0, .ctor dotk []), (1, .map Srt.map m1), (2, ctr), (3, int k)]

theorem hmatchX (τ : Subst) (h0 : τ.lookup 0 = some (.ctor dotk [])) (h1 : τ.lookup 1 = some (.map Srt.map m1))
    (h2 : τ.lookup 2 = some ctr) : PatVal (c0.withHooks H) τ r0.lhs (X H).val := by
  rw [r0_lhs]
  exact .ctor (syms_ok (H := H)).1 (.cons (.ctor (syms_ok (H := H)).2.1 (.cons (.ctor (syms_ok (H := H)).2.2.1
    (.cons (.inj (.ctor (syms_ok (H := H)).2.2.2.1 .nil)) (.cons (.var h0) .nil))) .nil))
    (.cons (.ctor (syms_ok (H := H)).2.2.2.2.1 (.cons (.var h1) .nil)) (.cons (.var h2) .nil)))

/-- `K |-> 0` at K := k is the map `k |-> 0`. -/
theorem elemEval (k : Int) : EvalTerm (c0.withHooks H) (σ k)
    (.app mapElem [.inj Srt.int Srt.kitem (.var 3), .inj Srt.int Srt.kitem (.dv Srt.int (.int 0))])
    (some (.map Srt.map [(ki k, ki 0)])) :=
  .hook (syms_ok (H := H)).2.2.2.2.2.2.2.1 (syms_ok (H := H)).2.2.2.2.2.2.2.2.1 (.cons (.inj .var) (.cons (.inj .dv) .nil))
    (fun vs hvs => by
      obtain rfl : vs = [ki k, ki 0] := (Option.some.inj (show some [ki k, ki 0] = some vs from hvs)).symm
      exact Semantics.hookRes_of_value (Exec.hook_mapElem _ _))
    (fun h => nomatch (show some [ki k, ki 0] = none from h))

/-- `(K |-> 0) M` at K := k: `rest k` where k is no key of `1 |-> 0`, no value at the key 1. -/
theorem concatEval (k : Int) : EvalTerm (c0.withHooks H) (σ k)
    (.app mapConcat [.app mapElem [.inj Srt.int Srt.kitem (.var 3), .inj Srt.int Srt.kitem (.dv Srt.int (.int 0))],
      .var 1])
    (if k = 1 then none else some (.map Srt.map (rest k))) :=
  .hook (syms_ok (H := H)).2.2.2.2.2.2.2.2.2.1 (syms_ok (H := H)).2.2.2.2.2.2.2.2.2.2 (.cons (elemEval k) (.cons .var .nil))
    (fun vs hvs => by
      obtain rfl : vs = [GroundTerm.map Srt.map [(ki k, ki 0)], GroundTerm.map Srt.map m1] :=
        (Option.some.inj (show some [GroundTerm.map Srt.map [(ki k, ki 0)], GroundTerm.map Srt.map m1] = some vs
          from hvs)).symm
      exact hookRes_concat k)
    (fun h => nomatch (show some [GroundTerm.map Srt.map [(ki k, ki 0)], GroundTerm.map Srt.map m1] = none from h))

/-- **At the key 1 the right side has no value**: the concatenation `(1 |-> 0) (1 |-> 0)` is
undefined, so is the configuration. -/
theorem rhs_none_at_key (H : HookParams) : EvalTerm (c0.withHooks H) (σ 1) r0.rhs none := by
  rw [r0_rhs]
  have h := concatEval (H := H) 1
  simp only [↓reduceIte] at h
  exact .ctor (syms_ok (H := H)).1 (.cons (.ctor (syms_ok (H := H)).2.1 (.cons .var .nil))
    (.cons (.ctor (syms_ok (H := H)).2.2.2.2.1 (.cons h .nil)) (.cons .var .nil)))

/-- **`1 |-> 0` steps to `(k |-> 0) (1 |-> 0)`** by the rule, K := k, for k other than 1. -/
theorem stepBy {k : Int} (hk : k ≠ 1) : StepBy (c0.withHooks H) r0 (σ k) (X H) (Y H k) where
  mem := by rw [rules_eq]; simp
  hσ := fun j s hs => by
    rw [r0_vars] at hs
    match j, hs with
    | 0, hs => cases hs; exact ⟨_, rfl, by whd⟩
    | 1, hs => cases hs; exact ⟨_, rfl, by whd⟩
    | 2, hs => cases hs; exact ⟨_, rfl, by whd⟩
    | 3, hs => cases hs; exact ⟨_, rfl, sortOf_int k⟩
    | _ + 4, hs => simp at hs
  hmatch := hmatchX _ rfl rfl rfl
  hreq := fun t ht => by rw [r0_shape.1] at ht; cases ht
  hpre := by rw [r0_shape.2.2.1]; exact .top
  heval := by
    rw [r0_rhs]
    have h := concatEval (H := H) k
    simp only [hk, ↓reduceIte] at h
    exact .ctor (syms_ok (H := H)).1 (.cons (.ctor (syms_ok (H := H)).2.1 (.cons .var .nil))
      (.cons (.ctor (syms_ok (H := H)).2.2.2.2.1 (.cons h .nil)) (.cons .var .nil)))
  hens := fun t ht => by rw [r0_shape.2.1] at ht; cases ht
  hpost := by rw [r0_shape.2.2.2.1]; exact .top
  hprio := fun r' hr' hlt => by
    rw [rules_eq] at hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst hr'
    exact absurd hlt (Nat.lt_irrefl _)

theorem step {k : Int} (hk : k ≠ 1) : Step (c0.withHooks H) (X H) (Y H k) := step_iff_by.mpr ⟨r0, σ k, stepBy hk⟩

/-! ## No other successor -/

/-- **What the left side denotes**: `<k> go() ~> w </k> <m> m </m>` with the counter cell u, w, m and
u the values σ gives the variables 0, 1 and 2. -/
theorem lhs_inv {τ : Subst} {x : GroundTerm} (h : PatVal (c0.withHooks H) τ r0.lhs x) :
    ∃ w m u, x = .ctor topLabel [.ctor kCell [.ctor kseq [.inj sExp Srt.kitem (.ctor symGo []), w]],
      .ctor mCell [m], u] ∧ τ.lookup 0 = some w ∧ τ.lookup 1 = some m ∧ τ.lookup 2 = some u := by
  rw [r0_lhs] at h
  obtain ⟨-, vs, rfl, hvs⟩ := PatVal.app_inv hooks_ok.1 h (syms_ok (H := H)).1
  obtain ⟨v1, vs1, rfl, h1, hvs1⟩ := hvs.cons_inv
  obtain ⟨v2, vs2, rfl, h2, hvs2⟩ := hvs1.cons_inv
  obtain ⟨u, vs3, rfl, h3, hvs3⟩ := hvs2.cons_inv
  cases hvs3.nil_inv
  obtain ⟨-, ws, rfl, hws⟩ := PatVal.app_inv hooks_ok.2.1 h1 (syms_ok (H := H)).2.1
  obtain ⟨w1, ws1, rfl, h11, hws1⟩ := hws.cons_inv
  cases hws1.nil_inv
  obtain ⟨-, ns, rfl, hns⟩ := PatVal.app_inv hooks_ok.2.2.2.2 h2 (syms_ok (H := H)).2.2.2.2.1
  obtain ⟨m, ns1, rfl, hm, hns1⟩ := hns.cons_inv
  cases hns1.nil_inv
  obtain ⟨-, zs, rfl, hzs⟩ := PatVal.app_inv hooks_ok.2.2.1 h11 (syms_ok (H := H)).2.2.1
  obtain ⟨z1, zs1, rfl, hz1, hzs1⟩ := hzs.cons_inv
  obtain ⟨w, zs2, rfl, hz2, hzs2⟩ := hzs1.cons_inv
  cases hzs2.nil_inv
  obtain ⟨a, ha, rfl⟩ := PatVal.inj_inv hz1
  obtain ⟨-, as, rfl, has⟩ := PatVal.app_inv hooks_ok.2.2.2.1 ha (syms_ok (H := H)).2.2.2.1
  cases has.nil_inv
  exact ⟨w, m, u, rfl, PatVal.var_inv hz2, PatVal.var_inv hm, PatVal.var_inv h3⟩

/-- **A step from `<k> go() </k> <m> 1 |-> 0 </m>` is at K := k for some k other than 1, to
`(k |-> 0) (1 |-> 0)`**: at the key 1 the right side has no value. -/
theorem stepBy_inv {τ : Subst} {y : Config (c0.withHooks H)} (hb : StepBy (c0.withHooks H) r0 τ (X H) y) :
    ∃ k, k ≠ 1 ∧ τ.lookup 3 = some (int k) ∧ y = Y H k := by
  obtain ⟨w, m, u, hx, h0, h1, h2⟩ := lhs_inv hb.hmatch
  simp only [X, GroundTerm.ctor.injEq, List.cons.injEq, and_true, true_and] at hx
  obtain ⟨rfl, rfl, rfl⟩ := hx
  obtain ⟨v, h3, hv⟩ := hb.hσ 3 Srt.int (by rw [r0_vars]; rfl)
  obtain ⟨k, rfl⟩ := shape_int shapesOK hv
  have h := hb.heval
  rw [r0_rhs] at h
  obtain ⟨rs, hrs, he⟩ := EvalTerm.ctor_inv (syms_ok (H := H)).1 h
  obtain ⟨q1, rs1, rfl, hq1, hrs1⟩ := hrs.cons_inv
  obtain ⟨q2, rs2, rfl, hq2, hrs2⟩ := hrs1.cons_inv
  obtain ⟨q3, rs3, rfl, hq3, hrs3⟩ := hrs2.cons_inv
  cases hrs3.nil_inv
  rw [hq3.var_inv, h2] at he
  obtain ⟨ps, hps, rfl⟩ := EvalTerm.ctor_inv (syms_ok (H := H)).2.1 hq1
  obtain ⟨p1, ps1, rfl, hp1, hps1⟩ := hps.cons_inv
  cases hps1.nil_inv
  rw [hp1.var_inv, h0] at he
  obtain ⟨ms, hms, rfl⟩ := EvalTerm.ctor_inv (syms_ok (H := H)).2.2.2.2.1 hq2
  obtain ⟨m', ms1, rfl, hm', hms1⟩ := hms.cons_inv
  cases hms1.nil_inv
  obtain ⟨cs, hcs, hhc, -⟩ := evalHook_inv_fxv (syms_ok (H := H)).2.2.2.2.2.2.2.2.2.1 (syms_ok (H := H)).2.2.2.2.2.2.2.2.2.2 hm'
  obtain ⟨c1, cs1, rfl, hc1, hcs1⟩ := hcs.cons_inv
  obtain ⟨c2, cs2, rfl, hc2, hcs2⟩ := hcs1.cons_inv
  cases hcs2.nil_inv
  rw [hc2.var_inv, h1] at hhc
  obtain ⟨es, hes, hhe, -⟩ := evalHook_inv_fxv (syms_ok (H := H)).2.2.2.2.2.2.2.1 (syms_ok (H := H)).2.2.2.2.2.2.2.2.1 hc1
  obtain ⟨e1, es1, rfl, he1, hes1⟩ := hes.cons_inv
  obtain ⟨e2, es2, rfl, he2, hes2⟩ := hes1.cons_inv
  cases hes2.nil_inv
  obtain ⟨e1', he1', rfl⟩ := EvalTerm.inj_inv he1
  obtain ⟨e2', he2', rfl⟩ := EvalTerm.inj_inv he2
  rw [he1'.var_inv, h3, he2'.dv_inv] at hhe
  have hel := hhe _ rfl
  rw [Semantics.hookRes_of_value (Exec.hook_mapElem _ _)] at hel
  cases hel
  have hcat : (c0.withHooks H).hookRes mapConcat [GroundTerm.map Srt.map [(ki k, ki 0)], GroundTerm.map Srt.map m1] = some m' :=
    hhc _ rfl
  rw [hookRes_concat k] at hcat
  cases hcat
  by_cases hk : k = 1
  · simp only [hk, ↓reduceIte, allSome, Option.bind, Option.map] at he
    cases he
  · refine ⟨k, hk, h3, Subtype.ext ?_⟩
    simp only [hk, ↓reduceIte, allSome, Option.bind, Option.map, Option.some.injEq] at he
    exact he

/-- **The successors of `<k> go() </k> <m> 1 |-> 0 </m>`** are exactly the `(k |-> 0) (1 |-> 0)`, k an
Int that is no key of `1 |-> 0`. -/
theorem step_iff (H : HookParams) (y : Config (c0.withHooks H)) : Step (c0.withHooks H) (X H) y ↔ ∃ k, k ≠ 1 ∧ y = Y H k := by
  constructor
  · intro hs
    obtain ⟨r, τ, hb⟩ := step_iff_by.mp hs
    have hr := hb.mem
    rw [rules_eq] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    obtain ⟨k, hk, -, rfl⟩ := stepBy_inv hb
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact step hk

/-- **No step at the key**: no step by the rule has K := 1. -/
theorem no_step_at_key (H : HookParams) {τ : Subst} {y : Config (c0.withHooks H)}
    (hb : StepBy (c0.withHooks H) r0 τ (X H) y) : τ.lookup 3 ≠ some (int 1) := by
  obtain ⟨k, hk, h3, -⟩ := stepBy_inv hb
  rw [h3]
  intro h
  exact hk (by simpa [int] using h)

/-- **In every model of `Γc` the concatenation at the key has no element**: `Γ`'s axiom of the hooked
symbol `_Map_` at the two values `1 |-> 0`, `1 |-> 0`, where the hook gives no value, is
`_Map_(1 |-> 0, 1 |-> 0) = ⊥`. -/
theorem concat_key_bot (H : HookParams) :
    Γc (c0.withHooks H) ⊧ (KoreAML.den (symApp (c0.withHooks H) mapConcat (GroundTerm.koreList (c0.withHooks H) [.map Srt.map m1, .map Srt.map m1])) ≡ ⊥) :=
  fun hI => hI _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl
    ⟨⟨mapConcat, [Srt.map, Srt.map], Srt.map⟩, [.map Srt.map m1, .map Srt.map m1], none,
      by whd, by whd, rfl, fun _ => rfl, rfl⟩)))))))

/-- **In every model of `Γc`, `<k> go() </k> <m> 1 |-> 0 </m>` has a successor among the instances of
the application, and `(k |-> 0) (1 |-> 0)` is one of them**, for every Int k other than 1 (`sound_at`;
no competitor, no function). -/
theorem sound_xy (H : HookParams) {k : Int} (hk : k ≠ 1) :
    (Γc (c0.withHooks H) ⊧ (den (c0.withHooks H) (X H).val ⇒ KoreAML.sNext (famEx (c0.withHooks H) r0 (σ k)))) ∧
    (Γc (c0.withHooks H) ⊧ (den (c0.withHooks H) (Y H k).val ⇒ famEx (c0.withHooks H) r0 (σ k))) :=
  sound_at (c0.withHooks H) coreOK (X H) (Y H k) r0 (σ k) (stepBy hk)
    (fun r' hr' hlt _ _ => by
      rw [rules_eq] at hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      subst hr'
      exact absurd hlt (Nat.lt_irrefl _))
    (fun fn hfn => by rw [fns_nil] at hfn; cases hfn)

/-- **By `ExactC`**: y is a successor of `<k> go() </k> <m> 1 |-> 0 </m>` in some model of `Γc` with
the step's closure exactly where y is some `(k |-> 0) (1 |-> 0)` with k other than 1. -/
theorem exact_y (H : HookParams) (y : Config (c0.withHooks H)) :
    (∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
      (I ⊧ᴵP (Γc (c0.withHooks H) ∪ Γstep (c0.withHooks H))) ∧ ¬ (I ⊧ᴵ (den (c0.withHooks H) (X H).val ⇒ ∼ KoreAML.sNext (den (c0.withHooks H) y.val)))) ↔
    ∃ k, k ≠ 1 ∧ y = Y H k := by
  rw [← exact_hyp (c0.withHooks H) coreOK fnHyp (X H) y]
  exact step_iff H y

/-- info: 'HeldFixturesH.MapRest.step_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_iff
/-- info: 'HeldFixturesH.MapRest.rhs_none_at_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rhs_none_at_key
/-- info: 'HeldFixturesH.MapRest.no_step_at_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms no_step_at_key
/-- info: 'HeldFixturesH.MapRest.sound_xy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sound_xy
/-- info: 'HeldFixturesH.MapRest.concat_key_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms concat_key_bot
/-- info: 'HeldFixturesH.MapRest.exact_y' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms exact_y

end MapRest

namespace VarsSet

open ML Faithful

definition_of defn from "f2-examples/heldset.kompile.kore"

noncomputable abbrev c0 : Semantics := defn.sem

theorem coreOK0 : c0.coreOK = true := by decide_cheap
theorem noRaw0 : ∀ k ∈ c0.params, k.raw = false := by decide +kernel

variable {H : HookParams}

/-- A value has the sort the parsed data gives it, under every interpretation: no parameter is an
open generator. -/
theorem sortOf_eq : (c0.withHooks H).sortOf = c0.sortOf := Semantics.sortOf_withHooks c0 H noRaw0
theorem sortsOf_eq : (c0.withHooks H).sortsOf = c0.sortsOf := Semantics.sortsOf_withHooks c0 H noRaw0

/-- Decides a condition of the parsed data stated of `c0.withHooks H`: the condition does not read
the interpretation, so it is rewritten to `c0`'s and decided there. -/
local macro "whd" : tactic => `(tactic| first | decide +kernel | (rw [sortOf_eq]; decide +kernel) | (rw [sortsOf_eq]; decide +kernel) |
  (simp only [isCtor_wh_fxv, rules_wh_fxv, fns_wh_fxv, params_wh_fxv, shapesOK_wh_fxv, ctorSigs_wh_fxv,
    collOf_wh_fxv]; decide +kernel))

def sExp : Srt := 34
def kCell : Sym := 385
def sCell : Sym := 387
def symGo : Sym := 389


theorem coreOK : (c0.withHooks H).coreOK = true := (Semantics.coreOK_withHooks c0 H).trans coreOK0

noncomputable def r0 : Rule := c0.rules[0]'(by decide +kernel)

theorem rules_eq : (c0.withHooks H).rules = [r0] := by
  have h : c0.rules.length = 1 := by decide +kernel
  rw [rules_wh_fxv]
  match hr : c0.rules, h with
  | [r], _ => simp only [r0, hr, List.getElem_cons_zero]

theorem r0_vars : r0.vars = [Srt.k, Srt.set, 19, Srt.int] := rfl
theorem r0_lhs : r0.lhs = .app topLabel [.app kCell [.app kseq [.inj sExp Srt.kitem (.app symGo []),
    .var 0]], .app sCell [.var 1], .var 2] := rfl
theorem r0_rhs : r0.rhs = .app topLabel [.app kCell [.var 0],
    .app sCell [.app setConcat [.app setElem [.inj Srt.int Srt.kitem (.var 3)], .var 1]], .var 2] := rfl
theorem r0_shape : r0.req = none ∧ r0.ens = none ∧ r0.pre = .top ∧ r0.post = .top ∧ r0.exs = [3] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩


theorem fns_nil : (c0.withHooks H).fns = [] := by whd
theorem noRaw : ∀ k ∈ (c0.withHooks H).params, k.raw = false := by whd
theorem noWitness : ∀ r ∈ (c0.withHooks H).rules, r.needsWitness (c0.withHooks H) = false := by
  intro r hr
  rw [rules_eq] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  have h : r0.reqOpen = false := by decide +kernel
  simp only [Rule.needsWitness, h, Bool.false_and]
theorem shapesOK : (c0.withHooks H).shapesOK = true := by whd

theorem syms_ok : (c0.withHooks H).isCtor topLabel = true ∧ (c0.withHooks H).isCtor kCell = true ∧ (c0.withHooks H).isCtor kseq = true ∧
    (c0.withHooks H).isCtor symGo = true ∧ (c0.withHooks H).isCtor sCell = true ∧ (c0.withHooks H).isCtor dotk = true ∧ (c0.withHooks H).isCtor counterLabel = true ∧
    (c0.withHooks H).isCtor setElem = false ∧ isHook setElem = true ∧ (c0.withHooks H).isCtor setConcat = false ∧ isHook setConcat = true := by
  whd
theorem hooks_ok : patternHooks.contains topLabel = false ∧ patternHooks.contains kCell = false ∧
    patternHooks.contains kseq = false ∧ patternHooks.contains symGo = false ∧
    patternHooks.contains sCell = false := by
  whd

/-- The hypothesis on the functions holds: the text declares none, no rule needs a witness and no
parameter is an open generator. -/
theorem fnHyp : FnHyp (c0.withHooks H) :=
  have hn : ∀ fn, fn ∈ (c0.withHooks H).fns → False := fun fn hfn => by rw [fns_nil] at hfn; cases hfn
  ⟨fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim,
    fun fn hfn => (hn fn hfn).elim,
    openDecided_of_plain noWitness (fun fn hfn => (hn fn hfn).elim),
    openLaws_of_plain noRaw⟩

/-! ## The configurations -/

def ctr : GroundTerm := .ctor counterLabel [int 0]

/-- The collection holding 1. -/
def e1 : List GroundTerm := [ki 1]

/-- `<k> go() ~> . </k> <s> SetItem(1) </s>`. -/
def X (H : HookParams) : Config (c0.withHooks H) :=
  ⟨.ctor topLabel [.ctor kCell [.ctor kseq [.inj sExp Srt.kitem (.ctor symGo []), .ctor dotk []]],
    .ctor sCell [GroundTerm.set Srt.set e1], ctr], by whd⟩

/-- `<k> . </k>` with the collection es. -/
def cfgR (es : List GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor dotk []], .ctor sCell [GroundTerm.set Srt.set es], ctr]

theorem lookups_ok : (lookupSig (c0.withHooks H).ctorSigs topLabel).isSome = true ∧ (lookupSig (c0.withHooks H).ctorSigs sCell).isSome = true := by
  whd

theorem collOf_coll : (c0.withHooks H).collOf Srt.set = some ⟨Srt.set, .set, Srt.kitem, none, setUnit, setElem, setConcat⟩ := by
  whd

theorem sortOf_ki (j : Int) : (c0.withHooks H).sortOf (ki j) = some Srt.kitem := by
  rw [sortOf_ki_fxv j]; whd

/-- k is an element of the set holding 1 exactly where it is 1. -/
theorem memS_e1 (k : Int) : memS (ki k) e1 = true ↔ k = 1 := by
  simp only [memS, e1, List.any_cons, List.any_nil, Bool.or_false, beq_iff_eq, cmp_ki_fxv]

/-- `SetItem(k) S` at S the set holding 1, k other than 1: k inserted in order. -/
def rest (k : Int) : List GroundTerm := insertS (ki k) e1

theorem rest_ki (k : Int) : ∀ e ∈ rest k, ∃ j, e = ki j := fun e he => by
  rcases insertS_mem he with rfl | he
  · exact ⟨k, rfl⟩
  · simp only [e1, List.mem_singleton] at he; exact ⟨1, he⟩

/-- The successor's configuration is one for every Int k. -/
theorem sortOf_cfgRest (k : Int) : (c0.withHooks H).sortOf (cfgR (rest k)) = some topCellSort := by
  have h0 : (c0.withHooks H).sortOf (cfgR e1) = some topCellSort := by whd
  rw [← h0]
  have h1 : (c0.withHooks H).sortOf (GroundTerm.set Srt.set (rest k)) = some Srt.set :=
    sortOf_set_ki_fxv collOf_coll sortOf_ki (elemsSorted_iff.mpr (insertS_sorted
      (elemsSorted_iff.mp (by whd : elemsSorted e1 = true)))) (rest_ki k)
  have h2 : (c0.withHooks H).sortOf (GroundTerm.set Srt.set e1) = some Srt.set := by whd
  have hm : (c0.withHooks H).sortOf (GroundTerm.set Srt.set (rest k)) = (c0.withHooks H).sortOf (GroundTerm.set Srt.set e1) := by rw [h1, h2]
  exact sortOf_ctor_congr_fxv (lookups_ok (H := H)).1 (sortsOf_cons_congr_fxv rfl
    (sortsOf_cons_congr_fxv (sortOf_ctor_congr_fxv (lookups_ok (H := H)).2 (sortsOf_cons_congr_fxv hm rfl)) rfl))

/-- The successor at k. -/
def Y (H : HookParams) (k : Int) : Config (c0.withHooks H) := ⟨cfgR (rest k), sortOf_cfgRest k⟩

/-! ## The concatenation -/

theorem silent_concat (vs : List GroundTerm) : silent setConcat vs = false := rfl

/-- `SetItem(k) S` has a value exactly where k is no element of S, and it is `rest k`. -/
theorem hookRes_concat (k : Int) :
    (c0.withHooks H).hookRes setConcat [GroundTerm.set Srt.set [ki k], GroundTerm.set Srt.set e1] =
      some (if k = 1 then none else some (GroundTerm.set Srt.set (rest k))) := by
  rw [Semantics.hookRes_of_not_silent (silent_concat _), hook_setConcat_fxv]
  by_cases hk : k = 1
  · subst hk; rfl
  · have hn : memS (ki k) e1 = false := by
      cases h : memS (ki k) e1
      · rfl
      · exact absurd ((memS_e1 k).mp h) hk
    simp only [concatS, List.all_cons, List.all_nil, hn, Bool.not_false, Bool.and_true, ↓reduceIte, unionS,
      List.foldr_cons, List.foldr_nil, hk, rest, Option.map]

def resV (k : Int) : Option GroundTerm := if k = 1 then none else some (GroundTerm.set Srt.set (rest k))

/-! ## `Step` -/

def σ (k : Int) : Subst := [(0, .ctor dotk []), (1, GroundTerm.set Srt.set e1), (2, ctr), (3, int k)]

theorem hmatchX (τ : Subst) (h0 : τ.lookup 0 = some (.ctor dotk [])) (h1 : τ.lookup 1 = some (GroundTerm.set Srt.set e1))
    (h2 : τ.lookup 2 = some ctr) : PatVal (c0.withHooks H) τ r0.lhs (X H).val := by
  rw [r0_lhs]
  exact .ctor (syms_ok (H := H)).1 (.cons (.ctor (syms_ok (H := H)).2.1 (.cons (.ctor (syms_ok (H := H)).2.2.1
    (.cons (.inj (.ctor (syms_ok (H := H)).2.2.2.1 .nil)) (.cons (.var h0) .nil))) .nil))
    (.cons (.ctor (syms_ok (H := H)).2.2.2.2.1 (.cons (.var h1) .nil)) (.cons (.var h2) .nil)))

/-- `SetItem(V)` at V := k. -/
theorem elemEval (k : Int) : EvalTerm (c0.withHooks H) (σ k) (.app setElem [.inj Srt.int Srt.kitem (.var 3)])
    (some (GroundTerm.set Srt.set [ki k])) :=
  .hook (syms_ok (H := H)).2.2.2.2.2.2.2.1 (syms_ok (H := H)).2.2.2.2.2.2.2.2.1 (.cons (.inj .var) .nil)
    (fun vs hvs => by
      obtain rfl : vs = [ki k] := (Option.some.inj (show some [ki k] = some vs from hvs)).symm
      exact Semantics.hookRes_of_value (hook_setElem_fxv _))
    (fun h => nomatch (show some [ki k] = none from h))

/-- `SetItem(V) S` at V := k. -/
theorem concatEval (k : Int) : EvalTerm (c0.withHooks H) (σ k)
    (.app setConcat [.app setElem [.inj Srt.int Srt.kitem (.var 3)], .var 1]) (resV k) :=
  .hook (syms_ok (H := H)).2.2.2.2.2.2.2.2.2.1 (syms_ok (H := H)).2.2.2.2.2.2.2.2.2.2 (.cons (elemEval k) (.cons .var .nil))
    (fun vs hvs => by
      obtain rfl : vs = [GroundTerm.set Srt.set [ki k], GroundTerm.set Srt.set e1] :=
        (Option.some.inj (show some [GroundTerm.set Srt.set [ki k], GroundTerm.set Srt.set e1] = some vs from hvs)).symm
      exact hookRes_concat k)
    (fun h => nomatch (show some [GroundTerm.set Srt.set [ki k], GroundTerm.set Srt.set e1] = none from h))

/-- **The step at V := k** where the right side has a value. -/
theorem stepBy {k : Int} {v : GroundTerm} (hk : resV k = some v) (y : Config (c0.withHooks H)) (hy : y.val = .ctor topLabel
    [.ctor kCell [.ctor dotk []], .ctor sCell [v], ctr]) : StepBy (c0.withHooks H) r0 (σ k) (X H) y where
  mem := by rw [rules_eq]; simp
  hσ := fun j s hs => by
    rw [r0_vars] at hs
    match j, hs with
    | 0, hs => cases hs; exact ⟨_, rfl, by whd⟩
    | 1, hs => cases hs; exact ⟨_, rfl, by whd⟩
    | 2, hs => cases hs; exact ⟨_, rfl, by whd⟩
    | 3, hs => cases hs; exact ⟨_, rfl, sortOf_int k⟩
    | _ + 4, hs => simp at hs
  hmatch := hmatchX _ rfl rfl rfl
  hreq := fun t ht => by rw [r0_shape.1] at ht; cases ht
  hpre := by rw [r0_shape.2.2.1]; exact .top
  heval := by
    rw [r0_rhs, hy]
    have h := concatEval (H := H) k
    rw [hk] at h
    exact .ctor (syms_ok (H := H)).1 (.cons (.ctor (syms_ok (H := H)).2.1 (.cons .var .nil))
      (.cons (.ctor (syms_ok (H := H)).2.2.2.2.1 (.cons h .nil)) (.cons .var .nil)))
  hens := fun t ht => by rw [r0_shape.2.1] at ht; cases ht
  hpost := by rw [r0_shape.2.2.2.1]; exact .top
  hprio := fun r' hr' hlt => by
    rw [rules_eq] at hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst hr'
    exact absurd hlt (Nat.lt_irrefl _)

/-! ## No other successor -/

/-- **What the left side denotes**: `<k> go() ~> w </k>` with the collection m and the counter cell u,
w, m and u the values σ gives the variables 0, 1 and 2. -/
theorem lhs_inv {τ : Subst} {x : GroundTerm} (h : PatVal (c0.withHooks H) τ r0.lhs x) :
    ∃ w m u, x = .ctor topLabel [.ctor kCell [.ctor kseq [.inj sExp Srt.kitem (.ctor symGo []), w]],
      .ctor sCell [m], u] ∧ τ.lookup 0 = some w ∧ τ.lookup 1 = some m ∧ τ.lookup 2 = some u := by
  rw [r0_lhs] at h
  obtain ⟨-, vs, rfl, hvs⟩ := PatVal.app_inv hooks_ok.1 h (syms_ok (H := H)).1
  obtain ⟨v1, vs1, rfl, h1, hvs1⟩ := hvs.cons_inv
  obtain ⟨v2, vs2, rfl, h2, hvs2⟩ := hvs1.cons_inv
  obtain ⟨u, vs3, rfl, h3, hvs3⟩ := hvs2.cons_inv
  cases hvs3.nil_inv
  obtain ⟨-, ws, rfl, hws⟩ := PatVal.app_inv hooks_ok.2.1 h1 (syms_ok (H := H)).2.1
  obtain ⟨w1, ws1, rfl, h11, hws1⟩ := hws.cons_inv
  cases hws1.nil_inv
  obtain ⟨-, ns, rfl, hns⟩ := PatVal.app_inv hooks_ok.2.2.2.2 h2 (syms_ok (H := H)).2.2.2.2.1
  obtain ⟨m, ns1, rfl, hm, hns1⟩ := hns.cons_inv
  cases hns1.nil_inv
  obtain ⟨-, zs, rfl, hzs⟩ := PatVal.app_inv hooks_ok.2.2.1 h11 (syms_ok (H := H)).2.2.1
  obtain ⟨z1, zs1, rfl, hz1, hzs1⟩ := hzs.cons_inv
  obtain ⟨w, zs2, rfl, hz2, hzs2⟩ := hzs1.cons_inv
  cases hzs2.nil_inv
  obtain ⟨a, ha, rfl⟩ := PatVal.inj_inv hz1
  obtain ⟨-, as, rfl, has⟩ := PatVal.app_inv hooks_ok.2.2.2.1 ha (syms_ok (H := H)).2.2.2.1
  cases has.nil_inv
  exact ⟨w, m, u, rfl, PatVal.var_inv hz2, PatVal.var_inv hm, PatVal.var_inv h3⟩

/-- **A step from x is at V := k for an Int k where the right side has a value v, to the collection v.** -/
theorem stepBy_inv {τ : Subst} {y : Config (c0.withHooks H)} (hb : StepBy (c0.withHooks H) r0 τ (X H) y) :
    ∃ k v, τ.lookup 3 = some (int k) ∧ resV k = some v ∧
      y.val = .ctor topLabel [.ctor kCell [.ctor dotk []], .ctor sCell [v], ctr] := by
  obtain ⟨w, m, u, hx, h0, h1, h2⟩ := lhs_inv hb.hmatch
  simp only [X, GroundTerm.ctor.injEq, List.cons.injEq, and_true, true_and] at hx
  obtain ⟨rfl, rfl, rfl⟩ := hx
  obtain ⟨v, h3, hv⟩ := hb.hσ 3 Srt.int (by rw [r0_vars]; rfl)
  obtain ⟨k, rfl⟩ := shape_int shapesOK hv
  have h := hb.heval
  rw [r0_rhs] at h
  obtain ⟨rs, hrs, he⟩ := EvalTerm.ctor_inv (syms_ok (H := H)).1 h
  obtain ⟨q1, rs1, rfl, hq1, hrs1⟩ := hrs.cons_inv
  obtain ⟨q2, rs2, rfl, hq2, hrs2⟩ := hrs1.cons_inv
  obtain ⟨q3, rs3, rfl, hq3, hrs3⟩ := hrs2.cons_inv
  cases hrs3.nil_inv
  rw [hq3.var_inv, h2] at he
  obtain ⟨ps, hps, rfl⟩ := EvalTerm.ctor_inv (syms_ok (H := H)).2.1 hq1
  obtain ⟨p1, ps1, rfl, hp1, hps1⟩ := hps.cons_inv
  cases hps1.nil_inv
  rw [hp1.var_inv, h0] at he
  obtain ⟨ms, hms, rfl⟩ := EvalTerm.ctor_inv (syms_ok (H := H)).2.2.2.2.1 hq2
  obtain ⟨m', ms1, rfl, hm', hms1⟩ := hms.cons_inv
  cases hms1.nil_inv
  obtain ⟨cs, hcs, hhc, -⟩ := evalHook_inv_fxv (syms_ok (H := H)).2.2.2.2.2.2.2.2.2.1 (syms_ok (H := H)).2.2.2.2.2.2.2.2.2.2 hm'
  obtain ⟨c1, cs1, rfl, hc1, hcs1⟩ := hcs.cons_inv
  obtain ⟨c2, cs2, rfl, hc2, hcs2⟩ := hcs1.cons_inv
  cases hcs2.nil_inv
  rw [hc2.var_inv, h1] at hhc
  obtain ⟨es, hes, hhe, -⟩ := evalHook_inv_fxv (syms_ok (H := H)).2.2.2.2.2.2.2.1 (syms_ok (H := H)).2.2.2.2.2.2.2.2.1 hc1
  obtain ⟨f1, es1, rfl, hf1, hes1⟩ := hes.cons_inv
  cases hes1.nil_inv
  obtain ⟨f1', hf1', rfl⟩ := EvalTerm.inj_inv hf1
  rw [hf1'.var_inv, h3] at hhe
  have hel := hhe _ rfl
  rw [Semantics.hookRes_of_value (hook_setElem_fxv _)] at hel
  cases hel
  have hcat : (c0.withHooks H).hookRes setConcat [GroundTerm.set Srt.set [ki k], GroundTerm.set Srt.set e1] = some m' := hhc _ rfl
  have hres : resV k = m' := by rw [hookRes_concat k] at hcat; exact Option.some.inj hcat
  cases m' with
  | none => simp only [allSome, Option.bind, Option.map] at he; cases he
  | some v =>
    refine ⟨k, v, h3, hres, ?_⟩
    simp only [allSome, Option.bind, Option.map, Option.some.injEq] at he
    exact he

/-- **The successors of x** are exactly the `SetItem(k) S`, k an Int that is no element of S. -/
theorem step_iff (H : HookParams) (y : Config (c0.withHooks H)) : Step (c0.withHooks H) (X H) y ↔ ∃ k, k ≠ 1 ∧ y = Y H k := by
  constructor
  · intro hs
    obtain ⟨r, τ, hb⟩ := step_iff_by.mp hs
    have hr := hb.mem
    rw [rules_eq] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    obtain ⟨k, v, -, hk, hy⟩ := stepBy_inv hb
    by_cases h1 : k = 1
    · simp [resV, h1] at hk
    · simp only [resV, h1, ↓reduceIte, Option.some.injEq] at hk
      subst hk
      exact ⟨k, h1, Subtype.ext hy⟩
  · rintro ⟨k, hk, rfl⟩
    exact step_iff_by.mpr ⟨r0, σ k, stepBy (by simp [resV, hk]) (Y H k) rfl⟩

/-- **At the element 1 the right side has no value**: `SetItem(1) S` with 1 in S is undefined. -/
theorem rhs_none_at_key (H : HookParams) : EvalTerm (c0.withHooks H) (σ 1) r0.rhs none := by
  rw [r0_rhs]
  have h := concatEval (H := H) 1
  simp only [resV, ↓reduceIte] at h
  exact .ctor (syms_ok (H := H)).1 (.cons (.ctor (syms_ok (H := H)).2.1 (.cons .var .nil))
    (.cons (.ctor (syms_ok (H := H)).2.2.2.2.1 (.cons h .nil)) (.cons .var .nil)))

/-- **No step at the element**: no step by the rule has V := 1. -/
theorem no_step_at_key (H : HookParams) {τ : Subst} {y : Config (c0.withHooks H)}
    (hb : StepBy (c0.withHooks H) r0 τ (X H) y) : τ.lookup 3 ≠ some (int 1) := by
  obtain ⟨k, v, h3, hk, -⟩ := stepBy_inv hb
  rw [h3]
  intro h
  have h1 : k = 1 := by simpa [int] using h
  simp [resV, h1] at hk

/-- **In every model of `Γc` the concatenation at the element has no element**: `Γ`'s axiom of the
hooked symbol `_Set_` at the two values `SetItem(1)`, `SetItem(1)`. -/
theorem concat_key_bot (H : HookParams) :
    Γc (c0.withHooks H) ⊧ (KoreAML.den (symApp (c0.withHooks H) setConcat (GroundTerm.koreList (c0.withHooks H) [GroundTerm.set Srt.set e1, GroundTerm.set Srt.set e1])) ≡ ⊥) :=
  fun hI => hI _ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl
    ⟨⟨setConcat, [Srt.set, Srt.set], Srt.set⟩, [GroundTerm.set Srt.set e1, GroundTerm.set Srt.set e1], none,
      by whd, by whd, rfl, fun _ => rfl, rfl⟩)))))))

/-- **In every model of `Γc`, x has a successor among the instances of the application, and each
successor is one of them** (`sound_at`; no competitor, no function). -/
theorem sound_xy (H : HookParams) {k : Int} {v : GroundTerm} (hk : resV k = some v) (y : Config (c0.withHooks H)) (hy : y.val = .ctor topLabel
    [.ctor kCell [.ctor dotk []], .ctor sCell [v], ctr]) :
    (Γc (c0.withHooks H) ⊧ (den (c0.withHooks H) (X H).val ⇒ KoreAML.sNext (famEx (c0.withHooks H) r0 (σ k)))) ∧ (Γc (c0.withHooks H) ⊧ (den (c0.withHooks H) y.val ⇒ famEx (c0.withHooks H) r0 (σ k))) :=
  sound_at (c0.withHooks H) coreOK (X H) y r0 (σ k) (stepBy hk y hy)
    (fun r' hr' hlt _ _ => by
      rw [rules_eq] at hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      subst hr'
      exact absurd hlt (Nat.lt_irrefl _))
    (fun fn hfn => by rw [fns_nil] at hfn; cases hfn)

/-- **By `ExactC`**: y is a successor of x in some model of `Γc` with the step's closure exactly where
`Step` has it. -/
theorem exact_y (H : HookParams) (y : Config (c0.withHooks H)) :
    (∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
      (I ⊧ᴵP (Γc (c0.withHooks H) ∪ Γstep (c0.withHooks H))) ∧ ¬ (I ⊧ᴵ (den (c0.withHooks H) (X H).val ⇒ ∼ KoreAML.sNext (den (c0.withHooks H) y.val)))) ↔
    ∃ k, k ≠ 1 ∧ y = Y H k := by
  rw [← exact_hyp (c0.withHooks H) coreOK fnHyp (X H) y]
  exact step_iff H y

/-- info: 'HeldFixturesH.VarsSet.step_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_iff
/-- info: 'HeldFixturesH.VarsSet.sound_xy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sound_xy
/-- info: 'HeldFixturesH.VarsSet.exact_y' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms exact_y
/-- info: 'HeldFixturesH.VarsSet.rhs_none_at_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rhs_none_at_key
/-- info: 'HeldFixturesH.VarsSet.no_step_at_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms no_step_at_key
/-- info: 'HeldFixturesH.VarsSet.concat_key_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms concat_key_bot

end VarsSet

namespace VarsList

open ML Faithful

definition_of defn from "f2-examples/exvarslist.kompile.kore"

noncomputable abbrev c0 : Semantics := defn.sem

theorem coreOK0 : c0.coreOK = true := by decide_cheap
theorem noRaw0 : ∀ k ∈ c0.params, k.raw = false := by decide +kernel

variable {H : HookParams}

/-- A value has the sort the parsed data gives it, under every interpretation: no parameter is an
open generator. -/
theorem sortOf_eq : (c0.withHooks H).sortOf = c0.sortOf := Semantics.sortOf_withHooks c0 H noRaw0
theorem sortsOf_eq : (c0.withHooks H).sortsOf = c0.sortsOf := Semantics.sortsOf_withHooks c0 H noRaw0

/-- Decides a condition of the parsed data stated of `c0.withHooks H`: the condition does not read
the interpretation, so it is rewritten to `c0`'s and decided there. -/
local macro "whd" : tactic => `(tactic| first | decide +kernel | (rw [sortOf_eq]; decide +kernel) | (rw [sortsOf_eq]; decide +kernel) |
  (simp only [isCtor_wh_fxv, rules_wh_fxv, fns_wh_fxv, params_wh_fxv, shapesOK_wh_fxv, ctorSigs_wh_fxv,
    collOf_wh_fxv]; decide +kernel))

def sExp : Srt := 34
def kCell : Sym := 385
def lCell : Sym := 387
def symGo : Sym := 389


theorem coreOK : (c0.withHooks H).coreOK = true := (Semantics.coreOK_withHooks c0 H).trans coreOK0

noncomputable def r0 : Rule := c0.rules[0]'(by decide +kernel)

theorem rules_eq : (c0.withHooks H).rules = [r0] := by
  have h : c0.rules.length = 1 := by decide +kernel
  rw [rules_wh_fxv]
  match hr : c0.rules, h with
  | [r], _ => simp only [r0, hr, List.getElem_cons_zero]

theorem r0_vars : r0.vars = [Srt.k, Srt.list, 19, Srt.int] := rfl
theorem r0_lhs : r0.lhs = .app topLabel [.app kCell [.app kseq [.inj sExp Srt.kitem (.app symGo []),
    .var 0]], .app lCell [.var 1], .var 2] := rfl
theorem r0_rhs : r0.rhs = .app topLabel [.app kCell [.var 0],
    .app lCell [.app listConcat [.app listElem [.inj Srt.int Srt.kitem (.var 3)], .var 1]], .var 2] := rfl
theorem r0_shape : r0.req = none ∧ r0.ens = none ∧ r0.pre = .top ∧ r0.post = .top ∧ r0.exs = [3] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩


theorem fns_nil : (c0.withHooks H).fns = [] := by whd
theorem noRaw : ∀ k ∈ (c0.withHooks H).params, k.raw = false := by whd
theorem noWitness : ∀ r ∈ (c0.withHooks H).rules, r.needsWitness (c0.withHooks H) = false := by
  intro r hr
  rw [rules_eq] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  have h : r0.reqOpen = false := by decide +kernel
  simp only [Rule.needsWitness, h, Bool.false_and]
theorem shapesOK : (c0.withHooks H).shapesOK = true := by whd

theorem syms_ok : (c0.withHooks H).isCtor topLabel = true ∧ (c0.withHooks H).isCtor kCell = true ∧ (c0.withHooks H).isCtor kseq = true ∧
    (c0.withHooks H).isCtor symGo = true ∧ (c0.withHooks H).isCtor lCell = true ∧ (c0.withHooks H).isCtor dotk = true ∧ (c0.withHooks H).isCtor counterLabel = true ∧
    (c0.withHooks H).isCtor listElem = false ∧ isHook listElem = true ∧ (c0.withHooks H).isCtor listConcat = false ∧ isHook listConcat = true := by
  whd
theorem hooks_ok : patternHooks.contains topLabel = false ∧ patternHooks.contains kCell = false ∧
    patternHooks.contains kseq = false ∧ patternHooks.contains symGo = false ∧
    patternHooks.contains lCell = false := by
  whd

/-- The hypothesis on the functions holds: the text declares none, no rule needs a witness and no
parameter is an open generator. -/
theorem fnHyp : FnHyp (c0.withHooks H) :=
  have hn : ∀ fn, fn ∈ (c0.withHooks H).fns → False := fun fn hfn => by rw [fns_nil] at hfn; cases hfn
  ⟨fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim, fun fn hfn => (hn fn hfn).elim,
    fun fn hfn => (hn fn hfn).elim,
    openDecided_of_plain noWitness (fun fn hfn => (hn fn hfn).elim),
    openLaws_of_plain noRaw⟩

/-! ## The configurations -/

def ctr : GroundTerm := .ctor counterLabel [int 0]

/-- The collection holding 1. -/
def e1 : List GroundTerm := [ki 1]

/-- `<k> go() ~> . </k> <l> ListItem(1) </l>`. -/
def X (H : HookParams) : Config (c0.withHooks H) :=
  ⟨.ctor topLabel [.ctor kCell [.ctor kseq [.inj sExp Srt.kitem (.ctor symGo []), .ctor dotk []]],
    .ctor lCell [GroundTerm.list Srt.list e1], ctr], by whd⟩

/-- `<k> . </k>` with the collection es. -/
def cfgR (es : List GroundTerm) : GroundTerm :=
  .ctor topLabel [.ctor kCell [.ctor dotk []], .ctor lCell [GroundTerm.list Srt.list es], ctr]

theorem lookups_ok : (lookupSig (c0.withHooks H).ctorSigs topLabel).isSome = true ∧ (lookupSig (c0.withHooks H).ctorSigs lCell).isSome = true := by
  whd

theorem collOf_coll : (c0.withHooks H).collOf Srt.list = some ⟨Srt.list, .list, Srt.kitem, none, listUnit, listElem, listConcat⟩ := by
  whd

theorem sortOf_ki (j : Int) : (c0.withHooks H).sortOf (ki j) = some Srt.kitem := by
  rw [sortOf_ki_fxv j]; whd

/-- `ListItem(k) L` at L the list holding 1: k in front of 1. -/
def rest (k : Int) : List GroundTerm := [ki k] ++ e1

/-- The successor's configuration is one for every Int k. -/
theorem sortOf_cfgRest (k : Int) : (c0.withHooks H).sortOf (cfgR (rest k)) = some topCellSort := by
  have h0 : (c0.withHooks H).sortOf (cfgR e1) = some topCellSort := by whd
  rw [← h0]
  have h1 : (c0.withHooks H).sortOf (GroundTerm.list Srt.list (rest k)) = some Srt.list :=
    sortOf_list_ki_fxv collOf_coll sortOf_ki fun e he => by
      simp only [rest, e1, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact ⟨k, rfl⟩
      · exact ⟨1, rfl⟩
  have h2 : (c0.withHooks H).sortOf (GroundTerm.list Srt.list e1) = some Srt.list := by whd
  have hm : (c0.withHooks H).sortOf (GroundTerm.list Srt.list (rest k)) = (c0.withHooks H).sortOf (GroundTerm.list Srt.list e1) := by rw [h1, h2]
  exact sortOf_ctor_congr_fxv (lookups_ok (H := H)).1 (sortsOf_cons_congr_fxv rfl
    (sortsOf_cons_congr_fxv (sortOf_ctor_congr_fxv (lookups_ok (H := H)).2 (sortsOf_cons_congr_fxv hm rfl)) rfl))

/-- The successor at k. -/
def Y (H : HookParams) (k : Int) : Config (c0.withHooks H) := ⟨cfgR (rest k), sortOf_cfgRest k⟩

/-! ## The concatenation -/

theorem silent_concat (vs : List GroundTerm) : silent listConcat vs = false := rfl

/-- `ListItem(k) L` is the list with k in front, for every k. -/
theorem hookRes_concat (k : Int) :
    (c0.withHooks H).hookRes listConcat [GroundTerm.list Srt.list [ki k], GroundTerm.list Srt.list e1] = some (some (GroundTerm.list Srt.list (rest k))) := by
  rw [Semantics.hookRes_of_not_silent (silent_concat _), hook_listConcat_fxv]; rfl

def resV (k : Int) : Option GroundTerm := some (GroundTerm.list Srt.list (rest k))

/-! ## `Step` -/

def σ (k : Int) : Subst := [(0, .ctor dotk []), (1, GroundTerm.list Srt.list e1), (2, ctr), (3, int k)]

theorem hmatchX (τ : Subst) (h0 : τ.lookup 0 = some (.ctor dotk [])) (h1 : τ.lookup 1 = some (GroundTerm.list Srt.list e1))
    (h2 : τ.lookup 2 = some ctr) : PatVal (c0.withHooks H) τ r0.lhs (X H).val := by
  rw [r0_lhs]
  exact .ctor (syms_ok (H := H)).1 (.cons (.ctor (syms_ok (H := H)).2.1 (.cons (.ctor (syms_ok (H := H)).2.2.1
    (.cons (.inj (.ctor (syms_ok (H := H)).2.2.2.1 .nil)) (.cons (.var h0) .nil))) .nil))
    (.cons (.ctor (syms_ok (H := H)).2.2.2.2.1 (.cons (.var h1) .nil)) (.cons (.var h2) .nil)))

/-- `ListItem(V)` at V := k. -/
theorem elemEval (k : Int) : EvalTerm (c0.withHooks H) (σ k) (.app listElem [.inj Srt.int Srt.kitem (.var 3)])
    (some (GroundTerm.list Srt.list [ki k])) :=
  .hook (syms_ok (H := H)).2.2.2.2.2.2.2.1 (syms_ok (H := H)).2.2.2.2.2.2.2.2.1 (.cons (.inj .var) .nil)
    (fun vs hvs => by
      obtain rfl : vs = [ki k] := (Option.some.inj (show some [ki k] = some vs from hvs)).symm
      exact Semantics.hookRes_of_value (hook_listElem_fxv _))
    (fun h => nomatch (show some [ki k] = none from h))

/-- `ListItem(V) L` at V := k. -/
theorem concatEval (k : Int) : EvalTerm (c0.withHooks H) (σ k)
    (.app listConcat [.app listElem [.inj Srt.int Srt.kitem (.var 3)], .var 1]) (resV k) :=
  .hook (syms_ok (H := H)).2.2.2.2.2.2.2.2.2.1 (syms_ok (H := H)).2.2.2.2.2.2.2.2.2.2 (.cons (elemEval k) (.cons .var .nil))
    (fun vs hvs => by
      obtain rfl : vs = [GroundTerm.list Srt.list [ki k], GroundTerm.list Srt.list e1] :=
        (Option.some.inj (show some [GroundTerm.list Srt.list [ki k], GroundTerm.list Srt.list e1] = some vs from hvs)).symm
      exact hookRes_concat k)
    (fun h => nomatch (show some [GroundTerm.list Srt.list [ki k], GroundTerm.list Srt.list e1] = none from h))

/-- **The step at V := k** where the right side has a value. -/
theorem stepBy {k : Int} {v : GroundTerm} (hk : resV k = some v) (y : Config (c0.withHooks H)) (hy : y.val = .ctor topLabel
    [.ctor kCell [.ctor dotk []], .ctor lCell [v], ctr]) : StepBy (c0.withHooks H) r0 (σ k) (X H) y where
  mem := by rw [rules_eq]; simp
  hσ := fun j s hs => by
    rw [r0_vars] at hs
    match j, hs with
    | 0, hs => cases hs; exact ⟨_, rfl, by whd⟩
    | 1, hs => cases hs; exact ⟨_, rfl, by whd⟩
    | 2, hs => cases hs; exact ⟨_, rfl, by whd⟩
    | 3, hs => cases hs; exact ⟨_, rfl, sortOf_int k⟩
    | _ + 4, hs => simp at hs
  hmatch := hmatchX _ rfl rfl rfl
  hreq := fun t ht => by rw [r0_shape.1] at ht; cases ht
  hpre := by rw [r0_shape.2.2.1]; exact .top
  heval := by
    rw [r0_rhs, hy]
    have h := concatEval (H := H) k
    rw [hk] at h
    exact .ctor (syms_ok (H := H)).1 (.cons (.ctor (syms_ok (H := H)).2.1 (.cons .var .nil))
      (.cons (.ctor (syms_ok (H := H)).2.2.2.2.1 (.cons h .nil)) (.cons .var .nil)))
  hens := fun t ht => by rw [r0_shape.2.1] at ht; cases ht
  hpost := by rw [r0_shape.2.2.2.1]; exact .top
  hprio := fun r' hr' hlt => by
    rw [rules_eq] at hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst hr'
    exact absurd hlt (Nat.lt_irrefl _)

/-! ## No other successor -/

/-- **What the left side denotes**: `<k> go() ~> w </k>` with the collection m and the counter cell u,
w, m and u the values σ gives the variables 0, 1 and 2. -/
theorem lhs_inv {τ : Subst} {x : GroundTerm} (h : PatVal (c0.withHooks H) τ r0.lhs x) :
    ∃ w m u, x = .ctor topLabel [.ctor kCell [.ctor kseq [.inj sExp Srt.kitem (.ctor symGo []), w]],
      .ctor lCell [m], u] ∧ τ.lookup 0 = some w ∧ τ.lookup 1 = some m ∧ τ.lookup 2 = some u := by
  rw [r0_lhs] at h
  obtain ⟨-, vs, rfl, hvs⟩ := PatVal.app_inv hooks_ok.1 h (syms_ok (H := H)).1
  obtain ⟨v1, vs1, rfl, h1, hvs1⟩ := hvs.cons_inv
  obtain ⟨v2, vs2, rfl, h2, hvs2⟩ := hvs1.cons_inv
  obtain ⟨u, vs3, rfl, h3, hvs3⟩ := hvs2.cons_inv
  cases hvs3.nil_inv
  obtain ⟨-, ws, rfl, hws⟩ := PatVal.app_inv hooks_ok.2.1 h1 (syms_ok (H := H)).2.1
  obtain ⟨w1, ws1, rfl, h11, hws1⟩ := hws.cons_inv
  cases hws1.nil_inv
  obtain ⟨-, ns, rfl, hns⟩ := PatVal.app_inv hooks_ok.2.2.2.2 h2 (syms_ok (H := H)).2.2.2.2.1
  obtain ⟨m, ns1, rfl, hm, hns1⟩ := hns.cons_inv
  cases hns1.nil_inv
  obtain ⟨-, zs, rfl, hzs⟩ := PatVal.app_inv hooks_ok.2.2.1 h11 (syms_ok (H := H)).2.2.1
  obtain ⟨z1, zs1, rfl, hz1, hzs1⟩ := hzs.cons_inv
  obtain ⟨w, zs2, rfl, hz2, hzs2⟩ := hzs1.cons_inv
  cases hzs2.nil_inv
  obtain ⟨a, ha, rfl⟩ := PatVal.inj_inv hz1
  obtain ⟨-, as, rfl, has⟩ := PatVal.app_inv hooks_ok.2.2.2.1 ha (syms_ok (H := H)).2.2.2.1
  cases has.nil_inv
  exact ⟨w, m, u, rfl, PatVal.var_inv hz2, PatVal.var_inv hm, PatVal.var_inv h3⟩

/-- **A step from x is at V := k for an Int k where the right side has a value v, to the collection v.** -/
theorem stepBy_inv {τ : Subst} {y : Config (c0.withHooks H)} (hb : StepBy (c0.withHooks H) r0 τ (X H) y) :
    ∃ k v, τ.lookup 3 = some (int k) ∧ resV k = some v ∧
      y.val = .ctor topLabel [.ctor kCell [.ctor dotk []], .ctor lCell [v], ctr] := by
  obtain ⟨w, m, u, hx, h0, h1, h2⟩ := lhs_inv hb.hmatch
  simp only [X, GroundTerm.ctor.injEq, List.cons.injEq, and_true, true_and] at hx
  obtain ⟨rfl, rfl, rfl⟩ := hx
  obtain ⟨v, h3, hv⟩ := hb.hσ 3 Srt.int (by rw [r0_vars]; rfl)
  obtain ⟨k, rfl⟩ := shape_int shapesOK hv
  have h := hb.heval
  rw [r0_rhs] at h
  obtain ⟨rs, hrs, he⟩ := EvalTerm.ctor_inv (syms_ok (H := H)).1 h
  obtain ⟨q1, rs1, rfl, hq1, hrs1⟩ := hrs.cons_inv
  obtain ⟨q2, rs2, rfl, hq2, hrs2⟩ := hrs1.cons_inv
  obtain ⟨q3, rs3, rfl, hq3, hrs3⟩ := hrs2.cons_inv
  cases hrs3.nil_inv
  rw [hq3.var_inv, h2] at he
  obtain ⟨ps, hps, rfl⟩ := EvalTerm.ctor_inv (syms_ok (H := H)).2.1 hq1
  obtain ⟨p1, ps1, rfl, hp1, hps1⟩ := hps.cons_inv
  cases hps1.nil_inv
  rw [hp1.var_inv, h0] at he
  obtain ⟨ms, hms, rfl⟩ := EvalTerm.ctor_inv (syms_ok (H := H)).2.2.2.2.1 hq2
  obtain ⟨m', ms1, rfl, hm', hms1⟩ := hms.cons_inv
  cases hms1.nil_inv
  obtain ⟨cs, hcs, hhc, -⟩ := evalHook_inv_fxv (syms_ok (H := H)).2.2.2.2.2.2.2.2.2.1 (syms_ok (H := H)).2.2.2.2.2.2.2.2.2.2 hm'
  obtain ⟨c1, cs1, rfl, hc1, hcs1⟩ := hcs.cons_inv
  obtain ⟨c2, cs2, rfl, hc2, hcs2⟩ := hcs1.cons_inv
  cases hcs2.nil_inv
  rw [hc2.var_inv, h1] at hhc
  obtain ⟨es, hes, hhe, -⟩ := evalHook_inv_fxv (syms_ok (H := H)).2.2.2.2.2.2.2.1 (syms_ok (H := H)).2.2.2.2.2.2.2.2.1 hc1
  obtain ⟨f1, es1, rfl, hf1, hes1⟩ := hes.cons_inv
  cases hes1.nil_inv
  obtain ⟨f1', hf1', rfl⟩ := EvalTerm.inj_inv hf1
  rw [hf1'.var_inv, h3] at hhe
  have hel := hhe _ rfl
  rw [Semantics.hookRes_of_value (hook_listElem_fxv _)] at hel
  cases hel
  have hcat : (c0.withHooks H).hookRes listConcat [GroundTerm.list Srt.list [ki k], GroundTerm.list Srt.list e1] = some m' := hhc _ rfl
  have hres : resV k = m' := by rw [hookRes_concat k] at hcat; exact Option.some.inj hcat
  cases m' with
  | none => simp only [allSome, Option.bind, Option.map] at he; cases he
  | some v =>
    refine ⟨k, v, h3, hres, ?_⟩
    simp only [allSome, Option.bind, Option.map, Option.some.injEq] at he
    exact he

/-- **The successors of x** are exactly the `ListItem(k) L`, k an Int. -/
theorem step_iff (H : HookParams) (y : Config (c0.withHooks H)) : Step (c0.withHooks H) (X H) y ↔ ∃ k, y = Y H k := by
  constructor
  · intro hs
    obtain ⟨r, τ, hb⟩ := step_iff_by.mp hs
    have hr := hb.mem
    rw [rules_eq] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    obtain ⟨k, v, -, hk, hy⟩ := stepBy_inv hb
    simp only [resV, Option.some.injEq] at hk
    subst hk
    exact ⟨k, Subtype.ext hy⟩
  · rintro ⟨k, rfl⟩
    exact step_iff_by.mpr ⟨r0, σ k, stepBy rfl (Y H k) rfl⟩

/-- **In every model of `Γc`, x has a successor among the instances of the application, and each
successor is one of them** (`sound_at`; no competitor, no function). -/
theorem sound_xy (H : HookParams) {k : Int} {v : GroundTerm} (hk : resV k = some v) (y : Config (c0.withHooks H)) (hy : y.val = .ctor topLabel
    [.ctor kCell [.ctor dotk []], .ctor lCell [v], ctr]) :
    (Γc (c0.withHooks H) ⊧ (den (c0.withHooks H) (X H).val ⇒ KoreAML.sNext (famEx (c0.withHooks H) r0 (σ k)))) ∧ (Γc (c0.withHooks H) ⊧ (den (c0.withHooks H) y.val ⇒ famEx (c0.withHooks H) r0 (σ k))) :=
  sound_at (c0.withHooks H) coreOK (X H) y r0 (σ k) (stepBy hk y hy)
    (fun r' hr' hlt _ _ => by
      rw [rules_eq] at hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      subst hr'
      exact absurd hlt (Nat.lt_irrefl _))
    (fun fn hfn => by rw [fns_nil] at hfn; cases hfn)

/-- **By `ExactC`**: y is a successor of x in some model of `Γc` with the step's closure exactly where
`Step` has it. -/
theorem exact_y (H : HookParams) (y : Config (c0.withHooks H)) :
    (∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M),
      (I ⊧ᴵP (Γc (c0.withHooks H) ∪ Γstep (c0.withHooks H))) ∧ ¬ (I ⊧ᴵ (den (c0.withHooks H) (X H).val ⇒ ∼ KoreAML.sNext (den (c0.withHooks H) y.val)))) ↔
    ∃ k, y = Y H k := by
  rw [← exact_hyp (c0.withHooks H) coreOK fnHyp (X H) y]
  exact step_iff H y

/-- info: 'HeldFixturesH.VarsList.step_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step_iff
/-- info: 'HeldFixturesH.VarsList.sound_xy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sound_xy
/-- info: 'HeldFixturesH.VarsList.exact_y' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms exact_y

end VarsList
end HeldFixturesH
