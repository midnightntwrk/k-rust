/-
  The premise set of `f2-examples/e6-param-rat.kompile.kore` (the kompiled text of construct fixture
  e6-param-rat, which imports module RAT) has no model, for every interpretation H of the parameter
  symbols: `no_model_text`. The premise set is the one a derivation from the text's sentences uses
  (`Pre H := TiePair.Pre (cH H) textPats`):
  - the text's 74 function sentences as written (`fnText`, `fnText_index`): the 43 equations of the
    18 functions of the text and the 31 equations of its sort predicates, each the translation of its
    sentence (`trS ad := trAxiom kore.symbolDecls kore.aliasNames ad`); Γ's equations are these
    translations, item for item (`shape`);
  - definedness;
  - Γ's item of the text's one rule (`ΓRules`);
  - the families, the parts of Γ no sentence states (`TiePair.Families`): the signature, Cons-Dist,
    Cons-Inj and no junk of the constructors (among them `<_,_>Rat` against `inj{Int,Rat}`, which no
    sentence of the text states), the graphs of the registry's hooks (the Int and Bool operations and
    `=/=K` the evaluation calls), the values with distinct Int literals distinct elements, the
    collections, and the interpretation's values where the text is silent.

  The argument. maxRat's two equations (sentences 317 and 318, rat.md:223-224) have one priority and
  both decide at (<1,1>Rat, 1): the `requires` `_>=Rat_` is `true` both ways, and they give the two
  arguments. `Eval` has both results (`maxRat_first`, by the evaluator; `maxRat_second`, by the
  second equation, whose `requires` the evaluator computes, `ge_swapped`); each is a theorem of Γ
  (`TiePair.eval_some_sound`, which asks `coreOK` only), and Γ holds the two values of Rat apart
  (`values_apart`), so Γ has no model (`no_model`), nor with the step's closure (`not_consistent`),
  and `FnHyp` is false (`not_fnHyp`). Every premise of Γ is a consequence of `Pre H`
  (`TiePair.gamma_from`, from `shape`), so `Pre H` has none either (`no_model_text`), nor with the
  step's closure (`not_consistent_text`).

  The sentences the evaluation reads: of the 43 equations of the text's functions, 19
  (`sentences19`): two of `_*Rat_`, three of `_+Rat_`, and those of `_-Rat_`, `_/Rat_`, `_<Rat_`,
  `_=/=Rat_`, `_>=Rat_`, two of `_>Rat_`, two of `gcdInt`, two of `makeRat/2`, one of `makeRat/3`,
  and maxRat's two (`heads19`). The reading `c19`, which keeps of the text's functions only the
  clauses of those 19 sentences (`c19_items`: its equations are those 19 sentences and the sort
  predicates' 31, as written), evaluates maxRat(<1,1>Rat, 1) to <1,1>Rat and `_>=Rat_`(1, <1,1>Rat)
  to `true`, the second equation's `requires` (`c19_evals`). That is a computation: `c19` is not
  `ok`, and `no_model_text` is stated of the premise set with all 74 sentences, not of the 19 alone.

  Run from the package root: `lake env lean -j1 test/TieE6ParamRatNoModel.lean` (peak 5.7 GiB under
  a 12 GiB scope, about 80 s).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieE6ParamRatNoModel

open KCore ML Faithful KoreAML

kore_term kore from "f2-examples/e6-param-rat.kompile.kore"
definition_of defn from "f2-examples/e6-param-rat.kompile.kore"
user_axioms U from "f2-examples/e6-param-rat.kompile.kore" module "E6-PARAM-RAT"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

/-- `tr s`: the item `Theory.ofDefinition kore` holds for the sentence. -/
noncomputable def trS (ad : AxiomDecl) : Item := trAxiom kore.symbolDecls kore.aliasNames ad

theorem noRaw : ∀ k ∈ c.params, k.raw = false := by decide +kernel
theorem coreOK : c.coreOK = true := by decide_cheap
theorem coreOKH (H : HookParams) : (cH H).coreOK = true := (Semantics.coreOK_withHooks c H).trans coreOK
theorem hok : c.ok = true := by decide +kernel
theorem hsr : c.srReady = true := by decide +kernel
theorem hmr : c.matchReady = true := by decide +kernel
theorem hokH (H : HookParams) : (cH H).ok = true := (Semantics.ok_withHooks c H).trans hok

def maxRat : Sym := 402
def geRat : Sym := 396
def ratCtor : Sym := 385
def rat : Srt := 32

theorem names : c.symName maxRat = "LblmaxRat" ∧ c.symName geRat = "Lbl'Unds-GT-Eqls'Rat'Unds'" ∧
    c.symName ratCtor = "Lbl'-LT-UndsCommUnds-GT-'Rat'Unds'RAT-COMMON'Unds'Rat'Unds'Int'Unds'Int" ∧
    c.sortName rat = "Rat" ∧ c.isCtor ratCtor = true ∧ (Srt.int, rat) ∈ c.subsorts := by decide +kernel

/-- `<n,n>Rat`. -/
def pair (n : Int) : GroundTerm := .ctor ratCtor [int n, int n]
/-- The Int `1` as a Rat. -/
def one : GroundTerm := .inj Srt.int rat (int 1)

theorem sort_pair (n : Int) : c.sortOf (pair n) = some rat := by
  show c.sortOf (.ctor ratCtor [.dv Srt.int (.int n), .dv Srt.int (.int n)]) = some rat
  rfl
theorem sort_one : c.sortOf one = some rat := by decide +kernel
theorem ne : pair 1 ≠ one := by decide

theorem sort_pairH (H : HookParams) (n : Int) : (cH H).sortOf (pair n) = some rat := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; exact sort_pair n
theorem sort_oneH (H : HookParams) : (cH H).sortOf one = some rat := by
  rw [Semantics.sortOf_withHooks _ _ noRaw]; exact sort_one

/-- The function numbered `f`, as `lookupFn` finds it. -/
noncomputable def fnOf (f : Sym) : Fn := (c.lookupFn f).getD ⟨0, [], 0, [], false⟩

theorem hfn (f : Sym) (h : (c.lookupFn f).isSome = true) : c.lookupFn f = some (fnOf f) := by
  unfold fnOf; cases hl : c.lookupFn f with
  | none => rw [hl] at h; cases h
  | some fn => rfl
theorem hfnH (H : HookParams) (f : Sym) (h : (c.lookupFn f).isSome = true) :
    (cH H).lookupFn f = some (fnOf f) := by rw [Semantics.lookupFn_withHooks]; exact hfn f h

/-- What `Cert.evalFC` computes is `Eval`'s under every H. -/
theorem eval_of {f : Sym} {vs : List GroundTerm} {k : Nat} {r : Option GroundTerm}
    (hf : (c.lookupFn f).isSome = true) (hvs : c.sortsOf vs = some (fnOf f).args)
    (h : Cert.evalFC c k f vs = some r) (H : HookParams) : Eval (cH H) f vs r :=
  TiePair.eval_withHooks hok hsr hmr noRaw H (hfn f hf) hvs h

/-- The second of two equations `f(R, S) => R requires g(R, S)`, `f(R, S) => S requires g(S, R)`
of one priority gives `S` where `g(S, R)` is `true`. -/
theorem eval_second {c' : Semantics} {f g : Sym} {fn : Fn} {cl : Clause} {a b : GroundTerm} {s : Srt}
    (hfn : c'.lookupFn f = some fn) (hmem : cl ∈ fn.clauses)
    (hvars : cl.vars = [s, s]) (hpats : cl.pats = [.var 0, .var 1])
    (hreq : cl.req = some (.app g [.var 1, .var 0])) (hpre : cl.pre = .top) (hpost : cl.post = .top)
    (hexs : cl.exs = []) (hens : cl.ens = none) (hrhs : cl.rhs = .var 1)
    (hprio : ∀ cl' ∈ fn.clauses, ¬ cl'.prio < cl.prio)
    (hsa : c'.sortOf a = some s) (hsb : c'.sortOf b = some s)
    (hg : EvalTerm c' [(0, a), (1, b)] (.app g [.var 1, .var 0]) (some (bool true))) :
    Eval c' f [a, b] (some b) := by
  refine Eval.clause (cl := cl) (σ := [(0, a), (1, b)]) hfn hmem ?_ ?_ ?_ ?_ ?_ hexs ?_ ?_ ?_
  · intro i t hi
    rw [hvars] at hi
    match i, hi with
    | 0, hi => simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi; exact ⟨a, rfl, hsa⟩
    | 1, hi => simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hi
               subst hi; exact ⟨b, rfl, hsb⟩
    | _ + 2, hi => simp at hi
  · rw [hpats]; exact .cons (.var rfl) (.cons (.var rfl) .nil)
  · intro t ht; rw [hreq] at ht; cases ht; exact hg
  · rw [hpre]; exact .top
  · intro cl' hcl' _ hlt; exact absurd hlt (hprio cl' hcl')
  · rw [hrhs]; exact EvalTerm.var (σ := [(0, a), (1, b)]) (i := 1)
  · intro t ht; rw [hens] at ht; cases ht
  · rw [hpost]; exact .top

/-- `g(S, R)` as a term over `R`, `S`, from the function's value at the two arguments. -/
theorem call_swapped {c' : Semantics} {g : Sym} {a b : GroundTerm} {r : Option GroundTerm}
    (hc : c'.isCtor g = false) (hh : isHook g = false) (hp : c'.isParam g = false)
    (hE : Eval c' g [b, a] r) : EvalTerm c' [(0, a), (1, b)] (.app g [.var 1, .var 0]) r :=
  EvalTerm.call (rs := [some b, some a]) hc hh
    (.cons (EvalTerm.var (σ := [(0, a), (1, b)]) (i := 1)) (.cons (EvalTerm.var (σ := [(0, a), (1, b)]) (i := 0)) .nil))
    rfl hE hp

/-! ## maxRat at (<1,1>Rat, 1) -/

theorem maxRat_first (H : HookParams) : Eval (cH H) maxRat [pair 1, one] (some (pair 1)) :=
  eval_of (k := 60) (by decide +kernel) (by decide +kernel) (by decide +kernel) H

theorem ge_swapped (H : HookParams) : Eval (cH H) geRat [one, pair 1] (some (bool true)) :=
  eval_of (k := 60) (by decide +kernel) (by decide +kernel) (by decide +kernel) H

theorem maxRat_second (H : HookParams) : Eval (cH H) maxRat [pair 1, one] (some one) :=
  eval_second (cl := (fnOf maxRat).clauses[1]'(by decide +kernel)) (g := geRat) (s := rat)
    (hfnH H maxRat (by decide +kernel)) (List.getElem_mem _)
    (by decide +kernel) (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    (by decide +kernel) (by decide +kernel) (by with_unfolding_all rfl) (by decide +kernel)
    (sort_pairH H 1) (sort_oneH H)
    (call_swapped (by show c.isCtor geRat = false; decide +kernel) (by decide +kernel)
      (by show c.isParam geRat = false; decide +kernel) (ge_swapped H))

/-! ## Γ has no model -/

theorem rat_apart : apartSort c rat = true := by decide +kernel

theorem sorts_args (H : HookParams) :
    (cH H).sortsOf [pair 1, one] = some (fnOf maxRat).args := by
  rw [Semantics.sortsOf_withHooks _ _ noRaw]; exact (by decide +kernel)

/-- **Γ of the text has no model, for every H**: maxRat has the two values at (<1,1>Rat, 1), each a
theorem of Γ, and Γ holds them apart. -/
theorem no_model (H : HookParams) :
    ¬ ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Γ (cH H) := by
  rintro ⟨M, _, I, hI⟩
  obtain ⟨hsok, hsr', hnn, hg, -, -, -, -, hno⟩ := hypSound_of_core (coreOKH H)
  haveI : OvlOK (cH H) := hno
  have htr := (sortCtx_of_all hsok hsr' (OvlOK.ovlCase hno)).trans
  have hD := defOK hI
  have hf : (c.lookupFn maxRat).isSome = true := by decide +kernel
  have s1 : Γ (cH H) ⊧ (TiePair.app (cH H) maxRat [pair 1, one] ≡ den (cH H) (pair 1)) :=
    TiePair.eval_some_sound (hpreTop := Semantics.preTop_of_okAll (Semantics.okAll_of_ok (hokH H))) (cH H)
      (hypSound_of_core (coreOKH H)) (Semantics.ok_clauseBinds (hokH H)) (maxRat_first H) (hfnH H maxRat hf)
      (sorts_args H)
  have s2 : Γ (cH H) ⊧ (TiePair.app (cH H) maxRat [pair 1, one] ≡ den (cH H) one) :=
    TiePair.eval_some_sound (hpreTop := Semantics.preTop_of_okAll (Semantics.okAll_of_ok (hokH H))) (cH H)
      (hypSound_of_core (coreOKH H)) (Semantics.ok_clauseBinds (hokH H)) (maxRat_second H) (hfnH H maxRat hf)
      (sorts_args H)
  have e1 := (KoreAML.interp_equal hD).mp (s1 hI KoreAML.val0 default)
  have e2 := (KoreAML.interp_equal hD).mp (s2 hI KoreAML.val0 default)
  have he : elemOf (cH H) I (pair 1) = elemOf (cH H) I one := by
    have a1 := (elemOf_spec hI (sort_pairH H 1) KoreAML.val0).1
    have a2 := (elemOf_spec hI (sort_oneH H) KoreAML.val0).1
    exact (a2 _).mp ((e2 _).mp ((e1 _).mpr ((a1 _).mpr rfl)))
  exact ne (values_apart hI hg htr rat_apart (sort_pairH H 1) (sort_oneH H) he)

/-- Γ with the step's closure has no model, for every H. -/
theorem not_consistent (H : HookParams) : ¬ Consistent (cH H) :=
  fun ⟨M, i, I, hI⟩ => no_model H ⟨M, i, I, fun φ hφ => hI φ (Or.inl (Or.inl hφ))⟩

/-- `FnHyp`, the fact the package names as owed, is false of the text, for every H. -/
theorem not_fnHyp (H : HookParams) : ¬ FnHyp (cH H) :=
  fun hf => not_consistent H (consistent_of_fnHyp _ (coreOKH H) hf)

/-! ## The text's function sentences -/

/-- The text sentences of Γ's equations, in `fnItems`'s order, found by head symbol and priority
(`TiePair.fnTextOf`); `shape` is what makes them the equations' sentences. -/
noncomputable def fnText : List AxiomDecl := TiePair.fnTextOf c U.all

/-- The 74 sentences: the 43 equations of the text's functions, then the 31 of its sort predicates. -/
theorem fnText_index : fnText.map (·.index) =
    [188, 189, 192, 193, 194, 195, 203, 204, 205, 206, 213, 214, 215, 216, 217, 220, 221, 226, 229, 230,
     233, 234, 235, 236, 237, 238, 239, 240, 271, 272, 273, 312, 313, 314, 315, 316, 317, 318, 321, 322,
     325, 326, 327, 293, 301, 300, 299, 298, 305, 304, 309, 308, 303, 302, 279, 278, 292, 291, 281, 280,
     287, 286, 289, 288, 295, 294, 297, 296, 283, 282, 285, 284, 307, 306] := by decide +kernel

/-- From position 43 on, the sentences are equations of sort predicates (`isRat`, `isInt`, ...). -/
theorem fnText_tail : (fnText.drop 43).all (fun ad =>
    ((AttrsAgree.eqnHead ad.ax.pattern).getD "").startsWith "Lblis") = true := by decide +kernel

/-- The function sentences' translations, in `fnItems`'s order. -/
noncomputable def textPats : List P := fnText.map (trS · |>.pat)

/-- **Γ's equations are the text's sentences' translations, item for item** (one kernel decision). -/
theorem shape : TiePair.shapeB (TiePair.gammaPats c) textPats = true := by decide +kernel

theorem shapeH (H : HookParams) : TiePair.shapeB (TiePair.gammaPats (cH H)) textPats = true := by
  rw [TiePair.gammaPats_withHooks]; exact shape

/-- The premises of a derivation from the text: the function sentences as written, definedness, Γ's
rule item, and the families. -/
noncomputable abbrev Pre (H : HookParams) : Premises KoreAML.Sym := TiePair.Pre (cH H) textPats

/-- **The text's function sentences as written, with definedness, Γ's rule item and the families,
have no model, for every H.** -/
theorem no_model_text (H : HookParams) :
    ¬ ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP Pre H := by
  rintro ⟨M, _, I, hI⟩
  exact no_model H ⟨M, inferInstance, I, fun φ hφ => TiePair.gamma_from (shapeH H) φ hφ hI⟩

/-- The same with the step's closure. -/
theorem not_consistent_text (H : HookParams) :
    ¬ ∃ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), I ⊧ᴵP (Pre H ∪ Γstep (cH H)) :=
  fun ⟨M, i, I, hI⟩ => no_model_text H ⟨M, i, I, fun φ hφ => hI φ (Or.inl hφ)⟩

/-! ## The 19 sentences the evaluation reads -/

/-- The indices of the 19 sentences. -/
def sentences19 : List Nat :=
  [194, 195, 203, 205, 206, 213, 217, 221, 226, 230, 233, 235, 271, 273, 312, 313, 315, 317, 318]

/-- Each is one of the text's function sentences, of the function its head names. -/
theorem heads19 : (fnText.filter (sentences19.contains ·.index)).map
      (fun ad => (ad.index, (AttrsAgree.eqnHead ad.ax.pattern).getD "")) =
    [(194, "Lbl'UndsStar'Rat'Unds'"), (195, "Lbl'UndsStar'Rat'Unds'"), (203, "Lbl'UndsPlus'Rat'Unds'"),
     (205, "Lbl'UndsPlus'Rat'Unds'"), (206, "Lbl'UndsPlus'Rat'Unds'"), (213, "Lbl'Unds'-Rat'Unds'"),
     (217, "Lbl'UndsSlsh'Rat'Unds'"), (221, "Lbl'Unds-LT-'Rat'Unds'"), (226, "Lbl'UndsEqlsSlshEqls'Rat'Unds'"),
     (230, "Lbl'Unds-GT-Eqls'Rat'Unds'"), (233, "Lbl'Unds-GT-'Rat'Unds'"), (235, "Lbl'Unds-GT-'Rat'Unds'"),
     (271, "LblgcdInt'LParUndsCommUndsRParUnds'RAT'Unds'Int'Unds'Int'Unds'Int"),
     (273, "LblgcdInt'LParUndsCommUndsRParUnds'RAT'Unds'Int'Unds'Int'Unds'Int"),
     (312, "LblmakeRat'LParUndsCommUndsRParUnds'RAT'Unds'Rat'Unds'Int'Unds'Int"),
     (313, "LblmakeRat'LParUndsCommUndsRParUnds'RAT'Unds'Rat'Unds'Int'Unds'Int"),
     (315, "LblmakeRat'LParUndsCommUndsCommUndsRParUnds'RAT'Unds'Rat'Unds'Int'Unds'Int'Unds'Int"),
     (317, "LblmaxRat"), (318, "LblmaxRat")] := by decide +kernel

/-- Each function of `fns` keeps the clauses whose sentence (the next of `ads`, in order) is among
`keep`. -/
def restrictRsn (keep : List Nat) : List Fn → List AxiomDecl → List Fn
  | [], _ => []
  | fn :: fns, ads =>
    { fn with clauses := ((fn.clauses.zip (ads.take fn.clauses.length)).filter
        (fun p => keep.contains p.2.index)).map (·.1) } :: restrictRsn keep fns (ads.drop fn.clauses.length)

/-- The reading with the text's functions cut down to the clauses of the 19 sentences. -/
noncomputable def c19 : Semantics := { c with fns := restrictRsn sentences19 c.fns fnText }

/-- **Its equations are the 19 sentences and the sort predicates' 31, as written.** -/
theorem c19_items : TiePair.gammaPats c19 =
    (((fnText.take 43).filter (sentences19.contains ·.index)) ++ fnText.drop 43).map (trS · |>.pat) := by
  decide +kernel

/-- **With only those clauses, the evaluator gives maxRat(<1,1>Rat, 1) the first argument, and the
second equation's `requires` `_>=Rat_`(1, <1,1>Rat) the value `true`.** -/
theorem c19_evals : Cert.evalFC c19 60 maxRat [pair 1, one] = some (some (pair 1)) ∧
    Cert.evalFC c19 60 geRat [one, pair 1] = some (some (bool true)) := by decide +kernel

end KCore.TieE6ParamRatNoModel

#check @KCore.TieE6ParamRatNoModel.coreOK
#check @KCore.TieE6ParamRatNoModel.names
#check @KCore.TieE6ParamRatNoModel.maxRat_first
#check @KCore.TieE6ParamRatNoModel.ge_swapped
#check @KCore.TieE6ParamRatNoModel.maxRat_second
#check @KCore.TieE6ParamRatNoModel.no_model
#check @KCore.TieE6ParamRatNoModel.not_consistent
#check @KCore.TieE6ParamRatNoModel.not_fnHyp
#check @KCore.TieE6ParamRatNoModel.fnText_index
#check @KCore.TieE6ParamRatNoModel.fnText_tail
#check @KCore.TieE6ParamRatNoModel.shape
#check @KCore.TieE6ParamRatNoModel.no_model_text
#check @KCore.TieE6ParamRatNoModel.not_consistent_text
#check @KCore.TieE6ParamRatNoModel.heads19
#check @KCore.TieE6ParamRatNoModel.c19_items
#check @KCore.TieE6ParamRatNoModel.c19_evals
#print axioms KCore.TieE6ParamRatNoModel.coreOK
#print axioms KCore.TieE6ParamRatNoModel.maxRat_first
#print axioms KCore.TieE6ParamRatNoModel.maxRat_second
#print axioms KCore.TieE6ParamRatNoModel.no_model
#print axioms KCore.TieE6ParamRatNoModel.not_consistent
#print axioms KCore.TieE6ParamRatNoModel.not_fnHyp
#print axioms KCore.TieE6ParamRatNoModel.fnText_index
#print axioms KCore.TieE6ParamRatNoModel.fnText_tail
#print axioms KCore.TieE6ParamRatNoModel.shape
#print axioms KCore.TieE6ParamRatNoModel.no_model_text
#print axioms KCore.TieE6ParamRatNoModel.not_consistent_text
#print axioms KCore.TieE6ParamRatNoModel.heads19
#print axioms KCore.TieE6ParamRatNoModel.c19_items
#print axioms KCore.TieE6ParamRatNoModel.c19_evals
