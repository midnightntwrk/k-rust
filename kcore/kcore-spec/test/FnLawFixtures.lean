/-
  The law axioms of functions in the kompiled texts of the fixtures e2-fn-assoc, e2-fn-assoc-bad,
  e2-fn-assoc-rest, e2-fn-idem and e2-fn-assoc-unit (test/constructs/fixtures/NAME), read by the
  reader: `f2-examples/NAME.kompile.kore`, the text whose sha256 the fixture's kompile.txt records,
  with its paths restored.

  Each text writes its law axioms on a function production (`[assoc]` of `pl`, of `pk`, of `pu`;
  `[idem]` of `pm`; `[unit(zero)]` of `pu`). The reader classes each as a law of the function stated
  at values under `FnLaws` (`fnLawSentences`: the account's `fnLaw` lines, printed below as the
  account prints them; no law sentence is left to `lawUnmatched`), holds it in `Definition.laws`
  (`laws_eq`, the text's equation with its variables numbered in order), not in the semantics, and
  each law is `lawSorted` (`sorted`). The account's entry for each (`Parse.fnLawEntry`, `entries`):
  - e2-fn-assoc (`pl(A, B) => A +Int B`), e2-fn-assoc-bad (`pl(A, B) => A -Int B`), e2-fn-idem
    (`pm(A, B) => maxInt(A, B)`): no term of the law reads the interpretation, so the entry is
    "FnLaws owed, open". It is one fact at every interpretation: on e2-fn-assoc true at every one
    (`Assoc.fnLaws`), on e2-fn-assoc-bad false at every one, at (1, 2, 3) (`Bad.not_lawAt`): the
    entry says the law is owed, not that it holds.
  - e2-fn-assoc-rest (`pk` declared, no rule): `pk` is a parameter no hook implements, so the law
    reads the interpretation and the entry is "a condition on the interpretation", "not
    discharged at HookParams.none".
  - e2-fn-assoc-unit: test/FnUnitKompiled.lean (`laws_eq`, `fnLaws`) and test/FnLawWording.lean
    (`text_entries`) state these on the same text; its account lines are checked here.

  On e2-fn-assoc the theory with the law's sentence has a model under every interpretation
  (`Assoc.consistent`, `consistent_with_laws` at the reader's `defn.laws`): `coreOK` by the kernel,
  `FnDet`, `FnSolves`, `ClausePreDecided`, `OpenLaws` from `FnFacts.of_nil` (the text's obligation
  lists are empty and it has no parameter), `FnLaws` from `pl`'s clause, `lawSorted` by the kernel.

  Fixture e2-fn-unit (`[unit(zero)]` without `[assoc]` on a function) has no kompiled text:
  kompile rejects it (its kompile.txt, exit 113), and rows.toml holds it R-b.

  Run from the package root: `lake env lean -j1 test/FnLawFixtures.lean`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.FnLawFixtures

open KCore ML Faithful

/-! ## The account's lines for the law axioms -/

/-- The account's lines for the text at `path` (as `kcore account` prints them): each law axiom on
a function with its index, symbol, keys and entry, then the law axioms no reading takes. -/
def fnLawLinesFL (path : String) : IO (List String) := do
  match Kore.parseDefinition (← IO.FS.readFile path) with
  | .error e => return [s!"KORE read error {e}"]
  | .ok k => match Parse.parse k with
    | .error r => return [s!"refused: {r.toText}"]
    | .ok d =>
      let fl := ((Parse.fnLawSentences k d).zip d.laws).map fun ((i, h, ls), l) =>
        s!"sentence {i} ({h}): fnLaw ({", ".intercalate ls}): {Parse.fnLawEntry d.sem l}"
      return fl ++ [s!"laws {d.laws.length}, law sentences {(Parse.fnLawSentences k d).length}, unmatched {(Parse.lawUnmatched k d).map Parse.Refusal.toText}"]

/--
info: f2-examples/e2-fn-assoc.kompile.kore
sentence 249 (Lblpl): fnLaw (assoc): FnLaws owed, open: no term of the law reads the interpretation, so it is one fact at every interpretation, not decided here
laws 1, law sentences 1, unmatched []
f2-examples/e2-fn-assoc-bad.kompile.kore
sentence 249 (Lblpl): fnLaw (assoc): FnLaws owed, open: no term of the law reads the interpretation, so it is one fact at every interpretation, not decided here
laws 1, law sentences 1, unmatched []
f2-examples/e2-fn-assoc-rest.kompile.kore
sentence 249 (Lblpk): fnLaw (assoc): FnLaws owed: a condition on the interpretation (the law reads the parameter Lblpk: its value is the interpretation's); not discharged at HookParams.none
laws 1, law sentences 1, unmatched []
f2-examples/e2-fn-idem.kompile.kore
sentence 249 (Lblpm): fnLaw (idem): FnLaws owed, open: no term of the law reads the interpretation, so it is one fact at every interpretation, not decided here
laws 1, law sentences 1, unmatched []
f2-examples/e2-fn-assoc-unit.kompile.kore
sentence 250 (Lblpu): fnLaw (assoc): FnLaws owed, open: no term of the law reads the interpretation, so it is one fact at every interpretation, not decided here
sentence 251 (Lblpu): fnLaw (unit): FnLaws owed, open: no term of the law reads the interpretation, so it is one fact at every interpretation, not decided here
sentence 252 (Lblpu): fnLaw (unit): FnLaws owed, open: no term of the law reads the interpretation, so it is one fact at every interpretation, not decided here
laws 3, law sentences 3, unmatched []
-/
#guard_msgs in
#eval show IO Unit from do
  for f in ["e2-fn-assoc", "e2-fn-assoc-bad", "e2-fn-assoc-rest", "e2-fn-idem", "e2-fn-assoc-unit"] do
    let p := s!"f2-examples/{f}.kompile.kore"
    IO.println p
    for l in ← fnLawLinesFL p do IO.println l

/-! ## The laws and entries, shared -/

/-- `f(f(K1, K2), K3) = f(K1, f(K2, K3))`, the text's `[assoc]` axiom of `f`. -/
def assocFL (f : Sym) : LawEq :=
  ⟨[Srt.int, Srt.int, Srt.int], .app f [.app f [.var 0, .var 1], .var 2], .app f [.var 0, .app f [.var 1, .var 2]]⟩

/-- `f(K, K) = K`, the text's `[idem]` axiom of `f`. -/
def idemFL (f : Sym) : LawEq := ⟨[Srt.int], .app f [.var 0, .var 0], .var 0⟩

def openEntryFL : String :=
  "FnLaws owed, open: no term of the law reads the interpretation, so it is one fact at every interpretation, not decided here"

/-- `f(A, B) => op(A, B)`. -/
def clOpFL (op : Sym) : Clause :=
  ⟨[Srt.int, Srt.int], [.var 0, .var 1], none, .app op [.var 0, .var 1], none, 50, false, [], .top, .top⟩

/-- The function `f`, declared total, with the one clause `f(A, B) => op(A, B)`. -/
def fnOpFL (f op : Sym) : Fn := ⟨f, [Srt.int, Srt.int], Srt.int, [clOpFL op], true⟩

/-! ## Evaluation, shared -/

section
variable {d : Semantics}

theorem evVarFL {σ : Subst} {i : Nat} {v : GroundTerm} (h : σ.lookup i = some v) :
    EvalTerm d σ (.var i) (some v) :=
  h ▸ EvalTerm.var

theorem evVarFL_inv {σ : Subst} {i : Nat} {r : Option GroundTerm} (h : EvalTerm d σ (.var i) r) :
    r = σ.lookup i := by
  cases h; rfl

/-- A call of the binary function `f` at two defined arguments. -/
theorem evCall2FL {f : Sym} (hk : d.isCtor f = false) (hh : isHook f = false) (hp : d.isParam f = false)
    {σ : Subst} {t u : Term} {x y : GroundTerm} {r : Option GroundTerm}
    (ht : EvalTerm d σ t (some x)) (hu : EvalTerm d σ u (some y)) (hf : Eval d f [x, y] r) :
    EvalTerm d σ (.app f [t, u]) r :=
  .call hk hh (.cons ht (.cons hu .nil)) rfl hf hp

/-- A binary interpreted Int symbol at two variables bound to Ints. -/
theorem evHook2FL {op : Sym} (hk : d.isCtor op = false) (hh : isHook op = true) {σ : Subst}
    {i j : Nat} {x y : GroundTerm} {v : GroundTerm} (hi : σ.lookup i = some x) (hj : σ.lookup j = some y)
    (hv : hook op [x, y] = some (some v)) : EvalTerm d σ (.app op [.var i, .var j]) (some v) :=
  .hook hk hh (.cons (evVarFL hi) (.cons (evVarFL hj) .nil))
    (fun vs hvs => by
      obtain rfl : [x, y] = vs := Option.some.inj hvs
      exact Semantics.hookRes_of_value hv)
    (fun h => nomatch h)

theorem ws2FL (a b : Int) : d.WellSorted [Srt.int, Srt.int] [(0, int a), (1, int b)] := by
  intro i s hi
  match i, hi with
  | 0, hi => cases hi; exact ⟨_, rfl, sortOf_int _⟩
  | 1, hi => cases hi; exact ⟨_, rfl, sortOf_int _⟩
  | n + 2, hi => simp at hi

theorem ws3FL (a b e : Int) : d.WellSorted [Srt.int, Srt.int, Srt.int] [(0, int a), (1, int b), (2, int e)] := by
  intro i s hi
  match i, hi with
  | 0, hi => cases hi; exact ⟨_, rfl, sortOf_int _⟩
  | 1, hi => cases hi; exact ⟨_, rfl, sortOf_int _⟩
  | 2, hi => cases hi; exact ⟨_, rfl, sortOf_int _⟩
  | n + 3, hi => simp at hi

/-- `f(A, B) => op(A, B)`, alone among `f`'s clauses, decides at every pair of Ints where `op` is
an interpreted Int symbol with a value there. -/
theorem eval_opFL {f op : Sym} (hl : d.lookupFn f = some (fnOpFL f op)) (hk : d.isCtor op = false)
    (hh : isHook op = true) {a b : Int} {v : GroundTerm} (hv : hook op [int a, int b] = some (some v)) :
    Eval d f [int a, int b] (some v) :=
  .clause (cl := clOpFL op) (σ := [(0, int a), (1, int b)]) hl (List.mem_singleton_self _) (ws2FL a b)
    (.cons (.var rfl) (.cons (.var rfl) .nil)) (fun _ h => nomatch h) .top
    (fun cl' hcl' _ hlt => by
      change cl' ∈ [clOpFL op] at hcl'
      rw [List.mem_singleton] at hcl'; subst hcl'; exact absurd hlt (Nat.lt_irrefl _))
    rfl (evHook2FL (i := 0) (j := 1) hk hh rfl rfl hv) (fun _ h => nomatch h) .top

/-- A variable of sort Int under a well-sorted σ is an Int literal. -/
theorem lookup_intFL (hs : d.shapesOK = true) (hr : ∀ k ∈ d.params, k.raw = false) (H : HookParams)
    {vars : List Srt} {σ : Subst} (hw : (d.withHooks H).WellSorted vars σ) (i : Nat)
    (hi : vars[i]? = some Srt.int) : ∃ a, σ.lookup i = some (int a) := by
  obtain ⟨v, hv, hsv⟩ := hw i _ hi
  rw [Semantics.sortOf_withHooks d H hr] at hsv
  obtain ⟨a, rfl⟩ := shape_int hs hsv
  exact ⟨a, hv⟩

/-- Two terms with one common result under a coherent semantics have the same results. -/
theorem iff_ofFL (hc : CoherentAll d) {σ : Subst} {t u : Term} {v : GroundTerm}
    (ht : EvalTerm d σ t (some v)) (hu : EvalTerm d σ u (some v)) (r : Option GroundTerm) :
    EvalTerm d σ t r ↔ EvalTerm d σ u r :=
  ⟨fun h => EvalTerm.functional hc ht h ▸ hu, fun h => EvalTerm.functional hc hu h ▸ ht⟩

end

/-- The hypotheses of `consistent_with_laws` that do not read the laws, under every
interpretation, for a semantics `coreOK` accepts whose obligation lists are empty, whose clauses'
predicates are `\top` and which has no open generator. -/
theorem model_of_nilFL {c : Semantics} (hc : c.coreOK = true) (hv : c.rightValued = true)
    (h1 : c.rankObligations [] ++ c.decObligationsL = []) (h2 : c.totalObligationsRP [] [] = [])
    (h3 : c.agreeObligationsI = []) (h4 : c.matchObligationsL = [])
    (h5 : c.params.all (fun k => !k.raw) = true) (hpreTop : c.clausesPreTop = true) (H : HookParams)
    (hnoEx : c.FnsNoExs := by first | assumption | exact Semantics.fnsNoExs_of_all (by decide +kernel) | exact Semantics.fnsNoExs_of_all rfl) :
    (c.withHooks H).coreOK = true ∧ FnDet (c.withHooks H) ∧ FnSolves (c.withHooks H) ∧
      ClausePreDecided (c.withHooks H) ∧ OpenLaws (c.withHooks H) := by
  have hcH : (c.withHooks H).coreOK = true := (Semantics.coreOK_withHooks _ H).trans hc
  have hob : FnFacts (c.withHooks H) [] [] :=
    FnFacts.of_nil
      (by rw [Semantics.rankObligations_withHooks, Semantics.decObligationsL_withHooks]; exact h1)
      ((Semantics.totalObligationsRP_withHooks _ H _ _).trans h2)
      ((Det.Semantics.agreeObligationsI_withHooks _ H).trans h3)
      ((Det.Semantics.matchObligationsL_withHooks _ H).trans h4) h5
  have hrh := Semantics.rightHeld_withHooks_of_valued hv H
  have hpH := (Semantics.clausesPreTop_withHooks _ H).trans hpreTop
  have hnoExH : (c.withHooks H).FnsNoExs := hnoEx
  have hm := fnModel_of_fnFacts hcH hrh hob hpH
  exact ⟨hcH, hm.1, hm.2, clausePreDecided_of_fnFactsN hcH (fun f _ => hrh.heldOwed f) hob hpH, hob.2.2.2.2⟩

/-! ## e2-fn-assoc: `pl(A, B) => A +Int B` with `[assoc]` -/

namespace Assoc

definition_of defn from "f2-examples/e2-fn-assoc.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

def pl : Sym := 384

theorem names : c.symName pl = "Lblpl" := by decide +kernel

/-- The reader's laws of the text: its one law axiom, the associativity of `pl`. -/
theorem laws_eq : defn.laws = [assocFL pl] := by kernel_rfl

theorem sorted : lawSorted c (assocFL pl) = true := by decide +kernel

theorem entries : defn.laws.map (Parse.fnLawEntry c) = [openEntryFL] := by decide +kernel

theorem coreOK_text : c.coreOK = true := by decide_cheap

/-- The text's one function is `pl` with its clause. -/
theorem fns_eq : c.fns = [fnOpFL pl intAdd] := by kernel_rfl

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem ctor_pl : c.isCtor pl = false := by decide +kernel
theorem ctor_add : c.isCtor intAdd = false := by decide +kernel
theorem param_pl : c.isParam pl = false := by decide +kernel

private theorem hok : c.ok = true := by decide +kernel
private theorem hsr : c.srReady = true := by decide +kernel
private theorem hmr : c.matchReady = true := by decide +kernel
private theorem hcf : c.clausesFixed = true := by decide +kernel
private theorem hag : c.agreeObligations = [] := by decide +kernel
private theorem hsh : c.shapesOK = true := by decide +kernel

theorem coherent (H : HookParams) : CoherentAll (cH H) :=
  Det.coherentAll_of_nil ((Semantics.ok_withHooks c H).trans hok) ((Semantics.srReady_withHooks c H).trans hsr)
    ((Semantics.matchReady_withHooks c H).trans hmr) ((Semantics.clausesFixed_withHooks c H).trans hcf)
    ((Semantics.agreeObligations_withHooks c H).trans hag)

theorem look_pl (H : HookParams) : (cH H).lookupFn pl = some (fnOpFL pl intAdd) := by
  rw [Semantics.lookupFn_withHooks]; kernel_rfl

/-- `pl(a, b)` is `a + b` at every pair of Ints, under every interpretation. -/
theorem eval_pl (H : HookParams) (a b : Int) : Eval (cH H) pl [int a, int b] (some (int (a + b))) :=
  eval_opFL (look_pl H) ctor_add (by decide) rfl

/-- **Associativity holds at values, under every interpretation**: both sides are `a + b + e`. -/
theorem assoc_lawAt (H : HookParams) : LawAt (cH H) (assocFL pl) := by
  intro σ hσ r
  obtain ⟨a, ha⟩ := lookup_intFL hsh noRaw H hσ 0 rfl
  obtain ⟨b, hb⟩ := lookup_intFL hsh noRaw H hσ 1 rfl
  obtain ⟨e, he⟩ := lookup_intFL hsh noRaw H hσ 2 rfl
  have hl : EvalTerm (cH H) σ (assocFL pl).lhs (some (int (a + b + e))) :=
    evCall2FL (d := cH H) ctor_pl (by decide) param_pl
      (evCall2FL (d := cH H) ctor_pl (by decide) param_pl (evVarFL ha) (evVarFL hb) (eval_pl H a b))
      (evVarFL he) (eval_pl H (a + b) e)
  have hr : EvalTerm (cH H) σ (assocFL pl).rhs (some (int (a + (b + e)))) :=
    evCall2FL (d := cH H) ctor_pl (by decide) param_pl (evVarFL ha)
      (evCall2FL (d := cH H) ctor_pl (by decide) param_pl (evVarFL hb) (evVarFL he) (eval_pl H b e))
      (eval_pl H a (b + e))
  rw [Int.add_assoc] at hl
  exact iff_ofFL (coherent H) hl hr r

/-- **The text's laws hold at values, under every interpretation**: the `FnLaws` the account lists
as owed, open, for sentence 249. -/
theorem fnLaws (H : HookParams) : FnLaws (cH H) defn.laws := by
  rw [laws_eq]
  intro l hl
  rw [List.mem_singleton] at hl; subst hl
  exact assoc_lawAt H

/-- **The theory of the text with its law's sentence has a model, under every interpretation**:
`consistent_with_laws` at the reader's laws. -/
theorem consistent (H : HookParams) :
    ∃ (M : Type) (_ : Inhabited M) (I : ML.Interpretation KoreAML.Sym M),
      (I ⊧ᴵP (Γc (cH H) ∪ Γstep (cH H))) ∧ ∀ l ∈ defn.laws, I ⊧ᴵ lawPattern (cH H) l :=
  have hm := model_of_nilFL coreOK_text (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) H
  consistent_with_laws hm.1 hm.2.1 hm.2.2.1 hm.2.2.2.1 hm.2.2.2.2 (fnLaws H)
    (fun l hl => by
      rw [laws_eq, List.mem_singleton] at hl; subst hl
      exact (lawSorted_withHooks _ H _).trans sorted)

end Assoc

/-! ## e2-fn-assoc-bad: `pl(A, B) => A -Int B` with `[assoc]` -/

namespace Bad

definition_of defn from "f2-examples/e2-fn-assoc-bad.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

def pl : Sym := 384

theorem names : c.symName pl = "Lblpl" := by decide +kernel

theorem laws_eq : defn.laws = [assocFL pl] := by kernel_rfl

theorem sorted : lawSorted c (assocFL pl) = true := by decide +kernel

/-- The entry is the one of e2-fn-assoc: owed, open. -/
theorem entries : defn.laws.map (Parse.fnLawEntry c) = [openEntryFL] := by decide +kernel

theorem fns_eq : c.fns = [fnOpFL pl intSub] := by kernel_rfl

theorem ctor_pl : c.isCtor pl = false := by decide +kernel
theorem ctor_sub : c.isCtor intSub = false := by decide +kernel
theorem param_pl : c.isParam pl = false := by decide +kernel

theorem look_pl (H : HookParams) : (cH H).lookupFn pl = some (fnOpFL pl intSub) := by
  rw [Semantics.lookupFn_withHooks]; kernel_rfl

theorem eval_pl (H : HookParams) (a b : Int) : Eval (cH H) pl [int a, int b] (some (int (a - b))) :=
  eval_opFL (look_pl H) ctor_sub (by decide) rfl

/-- **The law fails at values, under every interpretation**: at (1, 2, 3) the left side is
`(1 - 2) - 3 = -4`, the right side `1 - (2 - 3) = 2`. -/
theorem not_lawAt (H : HookParams) : ¬ LawAt (cH H) (assocFL pl) := by
  intro h
  let σ : Subst := [(0, int 1), (1, int 2), (2, int 3)]
  have hl : EvalTerm (cH H) σ (assocFL pl).lhs (some (int (1 - 2 - 3))) :=
    evCall2FL (d := cH H) ctor_pl (by decide) param_pl
      (evCall2FL (d := cH H) ctor_pl (by decide) param_pl (evVarFL (i := 0) rfl) (evVarFL (i := 1) rfl)
        (eval_pl H 1 2))
      (evVarFL (i := 2) rfl) (eval_pl H (1 - 2) 3)
  have hr : EvalTerm (cH H) σ (assocFL pl).rhs (some (int (1 - (2 - 3)))) :=
    evCall2FL (d := cH H) ctor_pl (by decide) param_pl (evVarFL (i := 0) rfl)
      (evCall2FL (d := cH H) ctor_pl (by decide) param_pl (evVarFL (i := 1) rfl) (evVarFL (i := 2) rfl)
        (eval_pl H 2 3))
      (eval_pl H 1 (2 - 3))
  have hr' := (h σ (ws3FL 1 2 3) _).mp hl
  have := EvalTerm.functional (Det.coherentAll_of_nil
      ((Semantics.ok_withHooks c H).trans (by decide +kernel))
      ((Semantics.srReady_withHooks c H).trans (by decide +kernel))
      ((Semantics.matchReady_withHooks c H).trans (by decide +kernel))
      ((Semantics.clausesFixed_withHooks c H).trans (by decide +kernel))
      ((Semantics.agreeObligations_withHooks c H).trans (by decide +kernel))) hr hr'
  exact absurd this (by decide)

end Bad

/-! ## e2-fn-assoc-rest: `pk` with `[assoc]` and no rule -/

namespace Rest

definition_of defn from "f2-examples/e2-fn-assoc-rest.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def pk : Sym := 384

theorem names : c.symName pk = "Lblpk" := by decide +kernel

theorem laws_eq : defn.laws = [assocFL pk] := by kernel_rfl

theorem sorted : lawSorted c (assocFL pk) = true := by decide +kernel

/-- `pk` is no function of the text: a parameter no hook implements. -/
theorem pk_param : c.fns = [] ∧ c.isParam pk = true ∧ (c.lookupParam pk).map (·.impl) = some none := by
  decide +kernel

def restEntryFL : String :=
  "FnLaws owed: a condition on the interpretation (the law reads the parameter Lblpk: its value is the interpretation's); not discharged at HookParams.none"

/-- The law reads the parameter: a condition on the interpretation, not discharged at
`HookParams.none`. -/
theorem entries : defn.laws.map (Parse.fnLawEntry c) = [restEntryFL] := by decide +kernel

end Rest

/-! ## e2-fn-idem: `pm(A, B) => maxInt(A, B)` with `[idem]` -/

namespace Idem

definition_of defn from "f2-examples/e2-fn-idem.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

def pm : Sym := 384

theorem names : c.symName pm = "Lblpm" := by decide +kernel

theorem laws_eq : defn.laws = [idemFL pm] := by kernel_rfl

theorem sorted : lawSorted c (idemFL pm) = true := by decide +kernel

theorem entries : defn.laws.map (Parse.fnLawEntry c) = [openEntryFL] := by decide +kernel

end Idem

end KCore.FnLawFixtures

/--
info: 'KCore.FnLawFixtures.Assoc.consistent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms KCore.FnLawFixtures.Assoc.consistent

/-- info: 'KCore.FnLawFixtures.Bad.not_lawAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KCore.FnLawFixtures.Bad.not_lawAt
