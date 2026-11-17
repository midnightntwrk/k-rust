/-
  Matching and evaluation read by the head of a pattern or term, as equivalences `simp` rewrites
  with, and the introduction forms of a function clause and of a rule.

  Each `_iff` states exactly what the constructors of `PatVal`, `PatVals`, `EvalTerm` or
  `EvalTerms` for that head require. An application is read under the side condition that picks
  its constructor; where the side condition alone leaves two constructors possible (a symbol that
  is both a constructor and a map pattern symbol), the right-hand side is their disjunction.

  Two readings of a match. Against a value of known head (a configuration already known), the
  value-directed forms (`PatVal.app_ctor_iff`, `PatVal.inj_inj_iff`, `PatVals.cons_cons_iff`, …)
  leave no existential. Against an unknown value (the instance of a symbolic state), a constructor
  pattern denotes exactly its instance under σ (`PatVal.iff_inst`), which `simp` computes once σ's
  values are named.

  A symbolic step is proved with them: a rule gives progress by `Step.progress_of_rule`, a
  function's clause gives its result by `Eval.of_clause_bind` and its only result by
  `Eval.inv_of_clause_bind`, and a configuration that a rule's left-hand side and a symbolic
  state's pattern both denote is read by rewriting both with these lemmas.
-/
import KcoreSpec.Symbolic
import KcoreSpec.EvalLemmas
import KcoreSpec.SubjectReduction

set_option autoImplicit false

namespace KCore

variable {c : Semantics} {σ : Subst}

/-! ## `PatVal` and `PatVals` -/

@[simp] theorem PatVal.var_iff {i : Nat} {v : GroundTerm} :
    PatVal c σ (.var i) v ↔ σ.lookup i = some v :=
  ⟨PatVal.var_inv, .var⟩

@[simp] theorem PatVal.dv_iff {s : Srt} {lit : Lit} {v : GroundTerm} :
    PatVal c σ (.dv s lit) v ↔ v = .dv s lit := by
  constructor
  · intro h
    generalize ht : Term.dv s lit = t at h
    cases h with
    | dv => cases ht; rfl
    | _ => cases ht
  · rintro rfl; exact .dv

@[simp] theorem PatVal.inj_iff {a b : Srt} {p : Term} {v : GroundTerm} :
    PatVal c σ (.inj a b p) v ↔ ∃ w, PatVal c σ p w ∧ v = injNormal a b w :=
  ⟨PatVal.inj_inv, fun ⟨_, h, hv⟩ => hv ▸ .inj h⟩

@[simp] theorem PatVal.as_iff {p : Term} {i : Nat} {v : GroundTerm} :
    PatVal c σ (.as p i) v ↔ PatVal c σ p v ∧ σ.lookup i = some v :=
  ⟨PatVal.as_inv, fun ⟨h, hi⟩ => .as h hi⟩

/-- A constructor's application denotes the constructor terms of its arguments' values, and, if
the symbol is also a map pattern symbol, what that symbol's operation builds from them. -/
theorem PatVal.ctor_iff {f : Sym} {ps : List Term} {v : GroundTerm} (hc : c.isCtor f = true) :
    PatVal c σ (.app f ps) v ↔
      (∃ vs, v = .ctor f vs ∧ PatVals c σ ps vs) ∨
      (patternHooks.contains f = true ∧ ∃ vs, PatVals c σ ps vs ∧ KCore.hook f vs = some (some v)) := by
  constructor
  · intro h
    generalize ht : Term.app f ps = t at h
    cases h with
    | ctor _ hs => cases ht; exact .inl ⟨_, rfl, hs⟩
    | hook hp hs hv => cases ht; exact .inr ⟨hp, _, hs, hv⟩
    | coll hc' _ _ _ => cases ht; rw [hc] at hc'; cases hc'
    | ovl hc' _ _ _ => cases ht; rw [hc] at hc'; cases hc'
    | _ => cases ht
  · rintro (⟨vs, rfl, hs⟩ | ⟨hp, vs, hs, hv⟩)
    · exact .ctor hc hs
    · exact .hook hp hs hv

/-- A map pattern symbol's application denotes what its operation builds from its arguments'
values, and, if the symbol is also a constructor, the constructor terms of those values. -/
theorem PatVal.hook_iff {f : Sym} {ps : List Term} {v : GroundTerm}
    (hp : patternHooks.contains f = true) :
    PatVal c σ (.app f ps) v ↔
      (∃ vs, PatVals c σ ps vs ∧ KCore.hook f vs = some (some v)) ∨
      (c.isCtor f = true ∧ ∃ vs, v = .ctor f vs ∧ PatVals c σ ps vs) := by
  constructor
  · intro h
    generalize ht : Term.app f ps = t at h
    cases h with
    | ctor hc hs => cases ht; exact .inr ⟨hc, _, rfl, hs⟩
    | hook _ hs hv => cases ht; exact .inl ⟨_, hs, hv⟩
    | coll _ hp' _ _ => cases ht; rw [Semantics.isCollPat_of_hook c hp] at hp'; cases hp'
    | ovl _ ho _ _ => cases ht; rw [c.isOvl_of_patternHook hp] at ho; cases ho
    | _ => cases ht
  · rintro (⟨vs, hs, hv⟩ | ⟨hc, vs, rfl, hs⟩)
    · exact .hook hp hs hv
    · exact .ctor hc hs

/-- A collection pattern symbol's application denotes the collection its operation builds from
its arguments' values. -/
theorem PatVal.coll_iff {f : Sym} {ps : List Term} {v : GroundTerm}
    (hc : c.isCtor f = false) (hp : c.isCollPat f = true) :
    PatVal c σ (.app f ps) v ↔ ∃ vs, PatVals c σ ps vs ∧ c.collVal f vs = some v := by
  constructor
  · intro h
    generalize ht : Term.app f ps = t at h
    cases h with
    | ctor hc' _ => cases ht; rw [hc] at hc'; cases hc'
    | hook hph _ _ => cases ht; rw [Semantics.isCollPat_of_hook c hph] at hp; cases hp
    | coll _ _ hs hv => cases ht; exact ⟨_, hs, hv⟩
    | ovl _ ho _ _ => cases ht; rw [c.isOvl_of_collPat hp] at ho; cases ho
    | _ => cases ht
  · rintro ⟨vs, hs, hv⟩
    exact .coll hc hp hs hv

/-- An overloading symbol's application denotes the normal form of its arguments' values. -/
theorem PatVal.ovl_iff {f : Sym} {ps : List Term} {v : GroundTerm} (ho : c.isOvl f = true) :
    PatVal c σ (.app f ps) v ↔ ∃ vs, PatVals c σ ps vs ∧ c.norm f vs = v := by
  constructor
  · intro h
    have hp := c.isOvl_parts ho
    generalize ht : Term.app f ps = t at h
    cases h with
    | ctor hc' _ => cases ht; rw [hp.1] at hc'; cases hc'
    | hook hph _ _ => cases ht; rw [c.isOvl_of_patternHook hph] at ho; cases ho
    | coll _ hcp _ _ => cases ht; rw [c.isOvl_of_collPat hcp] at ho; cases ho
    | ovl _ _ hs hv => cases ht; exact ⟨_, hs, hv⟩
    | _ => cases ht
  · rintro ⟨vs, hs, hv⟩
    exact .ovl (c.isOvl_parts ho).1 ho hs hv

/-- A constructor's application that is not a map pattern symbol denotes exactly the constructor
terms of its arguments' values. -/
theorem PatVal.ctor_iff_of_not_hook {f : Sym} {ps : List Term} {v : GroundTerm}
    (hc : c.isCtor f = true) (hp : patternHooks.contains f = false) :
    PatVal c σ (.app f ps) v ↔ ∃ vs, v = .ctor f vs ∧ PatVals c σ ps vs := by
  rw [PatVal.ctor_iff hc, hp]
  simp only [Bool.false_eq_true, false_and, or_false]

/-! ### Against a value of known head

With the value's head known, a constructor's pattern (one that is not a map pattern symbol) is
read without an existential: it denotes a constructor term of its own symbol and nothing else. -/

theorem PatVal.app_ctor_iff {f g : Sym} {ps : List Term} {vs : List GroundTerm}
    (hc : c.isCtor f = true) (hp : patternHooks.contains f = false) :
    PatVal c σ (.app f ps) (.ctor g vs) ↔ f = g ∧ PatVals c σ ps vs := by
  rw [PatVal.ctor_iff_of_not_hook hc hp]
  constructor
  · rintro ⟨_, h, hs⟩
    cases h
    exact ⟨rfl, hs⟩
  · rintro ⟨rfl, hs⟩
    exact ⟨_, rfl, hs⟩

theorem PatVal.app_inj_iff {f : Sym} {ps : List Term} {a b : Srt} {u : GroundTerm}
    (hc : c.isCtor f = true) (hp : patternHooks.contains f = false) :
    PatVal c σ (.app f ps) (.inj a b u) ↔ False := by
  rw [PatVal.ctor_iff_of_not_hook hc hp]
  exact ⟨fun ⟨_, h, _⟩ => (nomatch h), False.elim⟩

theorem PatVal.app_dv_iff {f : Sym} {ps : List Term} {s : Srt} {lit : Lit}
    (hc : c.isCtor f = true) (hp : patternHooks.contains f = false) :
    PatVal c σ (.app f ps) (.dv s lit) ↔ False := by
  rw [PatVal.ctor_iff_of_not_hook hc hp]
  exact ⟨fun ⟨_, h, _⟩ => (nomatch h), False.elim⟩

theorem PatVal.app_map_iff {f : Sym} {ps : List Term} {s : Srt}
    {es : List (GroundTerm × GroundTerm)}
    (hc : c.isCtor f = true) (hp : patternHooks.contains f = false) :
    PatVal c σ (.app f ps) (.map s es) ↔ False := by
  rw [PatVal.ctor_iff_of_not_hook hc hp]
  exact ⟨fun ⟨_, h, _⟩ => (nomatch h), False.elim⟩

theorem PatVal.app_set_iff {f : Sym} {ps : List Term} {s : Srt} {es : List GroundTerm}
    (hc : c.isCtor f = true) (hp : patternHooks.contains f = false) :
    PatVal c σ (.app f ps) (.set s es) ↔ False := by
  rw [PatVal.ctor_iff_of_not_hook hc hp]
  exact ⟨fun ⟨_, h, _⟩ => (nomatch h), False.elim⟩

theorem PatVal.app_list_iff {f : Sym} {ps : List Term} {s : Srt} {es : List GroundTerm}
    (hc : c.isCtor f = true) (hp : patternHooks.contains f = false) :
    PatVal c σ (.app f ps) (.list s es) ↔ False := by
  rw [PatVal.ctor_iff_of_not_hook hc hp]
  exact ⟨fun ⟨_, h, _⟩ => (nomatch h), False.elim⟩

/-- A symbol that is neither a constructor, nor a map pattern symbol, nor a collection pattern
symbol, nor an overloading symbol (a function, a hook, a parameter) is not a pattern: its
application denotes nothing. -/
theorem PatVal.app_none_iff {f : Sym} {ps : List Term} {v : GroundTerm}
    (hc : c.isCtor f = false) (hp : patternHooks.contains f = false) (hl : c.isCollPat f = false)
    (ho : c.isOvl f = false) :
    PatVal c σ (.app f ps) v ↔ False := by
  refine ⟨fun h => ?_, False.elim⟩
  generalize ht : Term.app f ps = t at h
  cases h with
  | ctor hc' _ => cases ht; rw [hc] at hc'; cases hc'
  | hook hp' _ _ => cases ht; rw [hp] at hp'; cases hp'
  | coll _ hl' _ _ => cases ht; rw [hl] at hl'; cases hl'
  | ovl _ ho' _ _ => cases ht; rw [ho] at ho'; cases ho'
  | _ => cases ht

/-! ### Injections

`injNormal a b u` is `inj{a,b}(u)` unless `u` is itself an injection `inj{a',_}(u')`, which it
re-heads to `inj{a',b}(u')`: an injection's value is never a constructor term, a domain value or a
collection, and the injection of a value of known head is read as follows. -/

@[simp] theorem injNormal_ctor (a b : Srt) (f : Sym) (vs : List GroundTerm) :
    injNormal a b (.ctor f vs) = .inj a b (.ctor f vs) := rfl
@[simp] theorem injNormal_dv (a b s : Srt) (lit : Lit) :
    injNormal a b (.dv s lit) = .inj a b (.dv s lit) := rfl
@[simp] theorem injNormal_map (a b s : Srt) (es : List (GroundTerm × GroundTerm)) :
    injNormal a b (.map s es) = .inj a b (.map s es) := rfl
@[simp] theorem injNormal_set (a b s : Srt) (es : List GroundTerm) :
    injNormal a b (.set s es) = .inj a b (.set s es) := rfl
@[simp] theorem injNormal_list (a b s : Srt) (es : List GroundTerm) :
    injNormal a b (.list s es) = .inj a b (.list s es) := rfl
@[simp] theorem injNormal_reheads (a b a' b' : Srt) (u : GroundTerm) :
    injNormal a b (.inj a' b' u) = .inj a' b u := rfl

@[simp] theorem GroundTerm.isInj_ctor (f : Sym) (vs : List GroundTerm) :
    (GroundTerm.ctor f vs).isInj = false := rfl
@[simp] theorem GroundTerm.isInj_inj (a b : Srt) (u : GroundTerm) :
    (GroundTerm.inj a b u).isInj = true := rfl
@[simp] theorem GroundTerm.isInj_dv (s : Srt) (lit : Lit) :
    (GroundTerm.dv s lit).isInj = false := rfl
@[simp] theorem GroundTerm.isInj_map (s : Srt) (es : List (GroundTerm × GroundTerm)) :
    (GroundTerm.map s es).isInj = false := rfl
@[simp] theorem GroundTerm.isInj_set (s : Srt) (es : List GroundTerm) :
    (GroundTerm.set s es).isInj = false := rfl
@[simp] theorem GroundTerm.isInj_list (s : Srt) (es : List GroundTerm) :
    (GroundTerm.list s es).isInj = false := rfl

/-- When `injNormal` gives `inj{a',b'}(u')`: `b'` is the target, and either the value was an
injection `inj{a',_}(u')` (re-headed), or it was `u'` itself, not an injection, and `a'` is `a`. -/
theorem injNormal_eq_inj {a b a' b' : Srt} {u u' : GroundTerm} :
    injNormal a b u = .inj a' b' u' ↔
      b = b' ∧ ((∃ x, u = .inj a' x u') ∨ (a = a' ∧ u.isInj = false ∧ u = u')) := by
  cases u with
  | inj a'' x w =>
    constructor
    · intro h; cases h; exact ⟨rfl, .inl ⟨x, rfl⟩⟩
    · rintro ⟨rfl, ⟨x', h⟩ | ⟨-, h, -⟩⟩
      · cases h; rfl
      · cases h
  | _ =>
    constructor
    · intro h; cases h; exact ⟨rfl, .inr ⟨rfl, rfl, rfl⟩⟩
    · rintro ⟨rfl, ⟨x', h⟩ | ⟨rfl, -, rfl⟩⟩
      · cases h
      · rfl

/-- An injection's pattern denotes `inj{a',b'}(u)` exactly when `b'` is its target and its
argument denotes either an injection `inj{a',x}(u)` (which `injNormal` re-heads), or `u` itself,
not an injection, with `a'` its source. -/
@[simp high] theorem PatVal.inj_inj_iff {a b a' b' : Srt} {p : Term} {u : GroundTerm} :
    PatVal c σ (.inj a b p) (.inj a' b' u) ↔
      b = b' ∧
        ((∃ x, PatVal c σ p (.inj a' x u)) ∨ (a = a' ∧ u.isInj = false ∧ PatVal c σ p u)) := by
  rw [PatVal.inj_iff]
  constructor
  · rintro ⟨w, hw, he⟩
    obtain ⟨rfl, ⟨x, rfl⟩ | ⟨rfl, hu, rfl⟩⟩ := injNormal_eq_inj.mp he.symm
    · exact ⟨rfl, .inl ⟨x, hw⟩⟩
    · exact ⟨rfl, .inr ⟨rfl, hu, hw⟩⟩
  · rintro ⟨rfl, ⟨x, h⟩ | ⟨rfl, hu, h⟩⟩
    · exact ⟨_, h, rfl⟩
    · exact ⟨_, h, (injNormal_eq_inj.mpr ⟨rfl, .inr ⟨rfl, hu, rfl⟩⟩).symm⟩

theorem PatVal.isInj_of_inj {a b : Srt} {p : Term} {v : GroundTerm}
    (h : PatVal c σ (.inj a b p) v) :
    v.isInj = true := by
  obtain ⟨w, -, rfl⟩ := PatVal.inj_iff.mp h
  cases w <;> rfl

@[simp high] theorem PatVal.inj_ctor_iff {a b : Srt} {p : Term} {g : Sym} {vs : List GroundTerm} :
    PatVal c σ (.inj a b p) (.ctor g vs) ↔ False :=
  ⟨fun h => Bool.noConfusion h.isInj_of_inj, False.elim⟩
@[simp high] theorem PatVal.inj_dv_iff {a b : Srt} {p : Term} {s : Srt} {lit : Lit} :
    PatVal c σ (.inj a b p) (.dv s lit) ↔ False :=
  ⟨fun h => Bool.noConfusion h.isInj_of_inj, False.elim⟩
@[simp high] theorem PatVal.inj_map_iff {a b : Srt} {p : Term} {s : Srt}
    {es : List (GroundTerm × GroundTerm)} :
    PatVal c σ (.inj a b p) (.map s es) ↔ False :=
  ⟨fun h => Bool.noConfusion h.isInj_of_inj, False.elim⟩
@[simp high] theorem PatVal.inj_set_iff {a b : Srt} {p : Term} {s : Srt} {es : List GroundTerm} :
    PatVal c σ (.inj a b p) (.set s es) ↔ False :=
  ⟨fun h => Bool.noConfusion h.isInj_of_inj, False.elim⟩
@[simp high] theorem PatVal.inj_list_iff {a b : Srt} {p : Term} {s : Srt} {es : List GroundTerm} :
    PatVal c σ (.inj a b p) (.list s es) ↔ False :=
  ⟨fun h => Bool.noConfusion h.isInj_of_inj, False.elim⟩

/-- The injection of a constructor's pattern (not a map pattern symbol): its value is the
injection of a constructor term, which `injNormal` leaves as it is. -/
theorem PatVal.inj_app_iff {a b : Srt} {f : Sym} {ps : List Term} {v : GroundTerm}
    (hc : c.isCtor f = true) (hp : patternHooks.contains f = false) :
    PatVal c σ (.inj a b (.app f ps)) v ↔ ∃ vs, v = .inj a b (.ctor f vs) ∧ PatVals c σ ps vs := by
  simp only [PatVal.inj_iff, PatVal.ctor_iff_of_not_hook hc hp]
  constructor
  · rintro ⟨_, ⟨vs, rfl, hs⟩, rfl⟩; exact ⟨vs, rfl, hs⟩
  · rintro ⟨vs, rfl, hs⟩; exact ⟨_, ⟨vs, rfl, hs⟩, rfl⟩

theorem PatVal.inj_app_inj_iff {a b a' b' : Srt} {f : Sym} {ps : List Term} {u : GroundTerm}
    (hc : c.isCtor f = true) (hp : patternHooks.contains f = false) :
    PatVal c σ (.inj a b (.app f ps)) (.inj a' b' u) ↔
      a = a' ∧ b = b' ∧ PatVal c σ (.app f ps) u := by
  rw [PatVal.inj_app_iff hc hp, PatVal.ctor_iff_of_not_hook hc hp]
  constructor
  · rintro ⟨vs, h, hs⟩
    cases h
    exact ⟨rfl, rfl, vs, rfl, hs⟩
  · rintro ⟨rfl, rfl, vs, rfl, hs⟩
    exact ⟨vs, rfl, hs⟩

@[simp] theorem PatVals.nil_iff {vs : List GroundTerm} : PatVals c σ [] vs ↔ vs = [] :=
  ⟨PatVals.nil_inv, fun h => h ▸ .nil⟩

@[simp] theorem PatVals.cons_iff {p : Term} {ps : List Term} {vs : List GroundTerm} :
    PatVals c σ (p :: ps) vs ↔ ∃ v vs', vs = v :: vs' ∧ PatVal c σ p v ∧ PatVals c σ ps vs' :=
  ⟨PatVals.cons_inv, fun ⟨_, _, hv, h, hs⟩ => hv ▸ .cons h hs⟩

@[simp high] theorem PatVals.nil_nil_iff : PatVals c σ [] [] ↔ True := iff_true_intro .nil

@[simp high] theorem PatVals.nil_cons_iff {v : GroundTerm} {vs : List GroundTerm} :
    PatVals c σ [] (v :: vs) ↔ False := ⟨fun h => (nomatch PatVals.nil_inv h), False.elim⟩

@[simp high] theorem PatVals.cons_nil_iff {p : Term} {ps : List Term} :
    PatVals c σ (p :: ps) [] ↔ False :=
  ⟨fun h => (by obtain ⟨_, _, h, -⟩ := PatVals.cons_inv h; cases h), False.elim⟩

@[simp high] theorem PatVals.cons_cons_iff {p : Term} {ps : List Term} {v : GroundTerm}
    {vs : List GroundTerm} : PatVals c σ (p :: ps) (v :: vs) ↔ PatVal c σ p v ∧ PatVals c σ ps vs :=
  ⟨fun h => (by obtain ⟨_, _, h, hp, hs⟩ := PatVals.cons_inv h; cases h; exact ⟨hp, hs⟩),
   fun h => .cons h.1 h.2⟩

/-! ### Constructor patterns as instances

A pattern built from variables, domain values, constructors (none a map pattern symbol),
injections and aliases denotes exactly one value under σ, its instance, when each alias's variable
holds its subpattern's instance. Read this way, a match against an unknown value becomes an
equation `p.inst σ = some v` that `simp` computes from the values σ gives the variables, without
one existential per subterm. -/

mutual
  /-- `p` is a constructor pattern of `c`: no map or collection pattern symbol, no function. -/
  def Term.ctorPat (c : Semantics) : Term → Bool
    | .var _ => true
    | .dv _ _ => true
    | .app f ps => c.isCtor f && !patternHooks.contains f && Term.ctorPatList c ps
    | .inj _ _ p => Term.ctorPat c p
    | .as p _ => Term.ctorPat c p
  def Term.ctorPatList (c : Semantics) : List Term → Bool
    | [] => true
    | p :: ps => Term.ctorPat c p && Term.ctorPatList c ps
end

mutual
  /-- The instance of a pattern read as a constructor pattern: its variables' values under σ,
  built up by constructors and injections (`injNormal`); an alias is its subpattern's instance. -/
  def Term.inst (σ : Subst) : Term → Option GroundTerm
    | .var i => σ.lookup i
    | .dv s lit => some (.dv s lit)
    | .app f ps => (Term.instList σ ps).map (.ctor f)
    | .inj a b p => (Term.inst σ p).map (injNormal a b)
    | .as p _ => Term.inst σ p
  def Term.instList (σ : Subst) : List Term → Option (List GroundTerm)
    | [] => some []
    | p :: ps => (Term.inst σ p).bind fun v => (Term.instList σ ps).map (v :: ·)
end

mutual
  /-- Each alias `p #as i` of the pattern has its variable's value equal to `p`'s instance. -/
  def Term.Aliases (σ : Subst) : Term → Prop
    | .var _ => True
    | .dv _ _ => True
    | .app _ ps => Term.AliasesList σ ps
    | .inj _ _ p => Term.Aliases σ p
    | .as p i => σ.lookup i = Term.inst σ p ∧ Term.Aliases σ p
  def Term.AliasesList (σ : Subst) : List Term → Prop
    | [] => True
    | p :: ps => Term.Aliases σ p ∧ Term.AliasesList σ ps
end

attribute [simp] Term.inst Term.instList Term.Aliases Term.AliasesList

mutual
  /-- A constructor pattern denotes its instance, and only it, when its aliases hold. -/
  theorem PatVal.iff_inst : ∀ {p : Term} {v : GroundTerm}, p.ctorPat c = true →
      (PatVal c σ p v ↔ p.inst σ = some v ∧ p.Aliases σ)
    | .var i, v, _ => by simp only [PatVal.var_iff, Term.inst, Term.Aliases, and_true]
    | .dv s lit, v, _ => by
      simp only [PatVal.dv_iff, Term.inst, Term.Aliases, and_true, Option.some.injEq]
      exact eq_comm
    | .app f ps, v, h => by
      simp only [Term.ctorPat, Bool.and_eq_true, Bool.not_eq_true'] at h
      obtain ⟨⟨hc, hp⟩, hps⟩ := h
      rw [PatVal.ctor_iff_of_not_hook hc hp]
      simp only [Term.inst, Term.Aliases]
      constructor
      · rintro ⟨vs, rfl, hs⟩
        obtain ⟨h1, h2⟩ := (PatVals.iff_inst hps).mp hs
        exact ⟨by rw [h1]; rfl, h2⟩
      · rintro ⟨h1, h2⟩
        obtain ⟨vs, hvs, rfl⟩ := Option.map_eq_some_iff.mp h1
        exact ⟨vs, rfl, (PatVals.iff_inst hps).mpr ⟨hvs, h2⟩⟩
    | .inj a b p, v, h => by
      simp only [Term.ctorPat] at h
      rw [PatVal.inj_iff]
      simp only [Term.inst, Term.Aliases]
      constructor
      · rintro ⟨w, hw, rfl⟩
        obtain ⟨h1, h2⟩ := (PatVal.iff_inst h).mp hw
        exact ⟨by rw [h1]; rfl, h2⟩
      · rintro ⟨h1, h2⟩
        obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h1
        exact ⟨w, (PatVal.iff_inst h).mpr ⟨hw, h2⟩, rfl⟩
    | .as p i, v, h => by
      simp only [Term.ctorPat] at h
      rw [PatVal.as_iff, PatVal.iff_inst h]
      simp only [Term.inst, Term.Aliases]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, h3.trans h1.symm, h2⟩
      · rintro ⟨h1, h3, h2⟩
        exact ⟨⟨h1, h2⟩, h3.trans h1⟩
  theorem PatVals.iff_inst : ∀ {ps : List Term} {vs : List GroundTerm},
      Term.ctorPatList c ps = true →
      (PatVals c σ ps vs ↔ Term.instList σ ps = some vs ∧ Term.AliasesList σ ps)
    | [], vs, _ => by
      simp only [PatVals.nil_iff, Term.instList, Term.AliasesList, and_true, Option.some.injEq]
      exact eq_comm
    | p :: ps, vs, h => by
      simp only [Term.ctorPatList, Bool.and_eq_true] at h
      rw [PatVals.cons_iff]
      simp only [Term.instList, Term.AliasesList]
      constructor
      · rintro ⟨v, vs', rfl, hp, hs⟩
        obtain ⟨h1, h2⟩ := (PatVal.iff_inst h.1).mp hp
        obtain ⟨h3, h4⟩ := (PatVals.iff_inst h.2).mp hs
        exact ⟨by rw [h1, Option.bind_some, h3]; rfl, h2, h4⟩
      · rintro ⟨h1, h2, h4⟩
        obtain ⟨v, hv, h1⟩ := Option.bind_eq_some_iff.mp h1
        obtain ⟨vs', hvs, rfl⟩ := Option.map_eq_some_iff.mp h1
        exact ⟨v, vs', rfl, (PatVal.iff_inst h.1).mpr ⟨hv, h2⟩,
          (PatVals.iff_inst h.2).mpr ⟨hvs, h4⟩⟩
end

/-! ## `EvalTerm` and `EvalTerms` -/

@[simp] theorem EvalTerm.var_iff {i : Nat} {r : Option GroundTerm} :
    EvalTerm c σ (.var i) r ↔ r = σ.lookup i :=
  ⟨EvalTerm.var_inv, fun h => h ▸ .var⟩

@[simp] theorem EvalTerm.dv_iff {s : Srt} {lit : Lit} {r : Option GroundTerm} :
    EvalTerm c σ (.dv s lit) r ↔ r = some (.dv s lit) := by
  constructor
  · intro h
    generalize ht : Term.dv s lit = t at h
    cases h with
    | dv => cases ht; rfl
    | _ => cases ht
  · rintro rfl; exact .dv

@[simp] theorem EvalTerm.inj_iff {a b : Srt} {t : Term} {r : Option GroundTerm} :
    EvalTerm c σ (.inj a b t) r ↔ ∃ r', EvalTerm c σ t r' ∧ r = r'.map (injNormal a b) :=
  ⟨EvalTerm.inj_inv, fun ⟨_, h, hr⟩ => hr ▸ .inj h⟩

/-- An alias pattern is not a term: it has no result. -/
@[simp] theorem EvalTerm.as_iff {t : Term} {i : Nat} {r : Option GroundTerm} :
    EvalTerm c σ (.as t i) r ↔ False := by
  refine ⟨fun h => ?_, False.elim⟩
  generalize ht : Term.as t i = u at h
  cases h <;> cases ht

/-- A constructor's application builds the constructor term of its arguments' results. -/
theorem EvalTerm.ctor_iff {f : Sym} {ts : List Term} {r : Option GroundTerm}
    (hc : c.isCtor f = true) :
    EvalTerm c σ (.app f ts) r ↔ ∃ rs, EvalTerms c σ ts rs ∧ r = (allSome rs).map (.ctor f) :=
  ⟨EvalTerm.ctor_inv hc, fun ⟨_, hts, hr⟩ => hr ▸ .ctor hc hts⟩

/-- An interpreted hooked symbol's application has its result (`hookRes`) on its arguments' values,
and is undefined when one is. -/
theorem EvalTerm.hook_iff {f : Sym} {ts : List Term} {r : Option GroundTerm}
    (hc : c.isCtor f = false) (hh : isHook f = true) :
    EvalTerm c σ (.app f ts) r ↔ ∃ rs, EvalTerms c σ ts rs ∧
      (∀ vs, allSome rs = some vs → c.hookRes f vs = some r) ∧ (allSome rs = none → r = none) := by
  constructor
  · intro h
    generalize ht : Term.app f ts = t at h
    cases h with
    | ctor h _ => cases ht; rw [hc] at h; cases h
    | hook _ _ hts hh' hund => cases ht; exact ⟨_, hts, hh', hund⟩
    | param _ h _ _ _ => cases ht; rw [hh] at h; cases h
    | call _ h _ _ _ _ => cases ht; rw [hh] at h; cases h
    | callUndef _ h _ _ _ => cases ht; rw [hh] at h; cases h
    | ovl _ ho _ => cases ht; rw [(c.isOvl_parts ho).2.1] at hh; cases hh
    | ovlFn _ ho => cases ht; rw [(c.isOvl_parts ho).2.1] at hh; cases hh
    | _ => cases ht
  · rintro ⟨_, hts, hh', hund⟩
    exact .hook hc hh hts hh' hund

/-- A parameter symbol's application has the value `paramVal` gives its arguments' results. -/
theorem EvalTerm.param_iff {f : Sym} {ts : List Term} {r : Option GroundTerm}
    (hc : c.isCtor f = false) (hh : isHook f = false) (hp : c.isParam f = true) :
    EvalTerm c σ (.app f ts) r ↔ ∃ rs, EvalTerms c σ ts rs ∧ r = (allSome rs).bind (c.paramVal f) :=
  ⟨EvalTerm.param_inv hc hh hp, fun ⟨_, hts, hr⟩ => .param hc hh hp hts hr⟩

/-- A function's application is a call on its arguments' values, and undefined when one is. -/
theorem EvalTerm.call_iff {f : Sym} {ts : List Term} {r : Option GroundTerm}
    (hc : c.isCtor f = false) (hh : isHook f = false) (hp : c.isParam f = false) (ho : c.isOvl f = false) :
    EvalTerm c σ (.app f ts) r ↔ ∃ rs, EvalTerms c σ ts rs ∧
      ((∃ vs, allSome rs = some vs ∧ Eval c f vs r) ∨ (allSome rs = none ∧ r = none)) := by
  refine ⟨EvalTerm.call_inv hc hh hp ho, ?_⟩
  rintro ⟨_, hts, ⟨_, hvs, hf⟩ | ⟨hvs, rfl⟩⟩
  · exact .call hc hh hts hvs hf hp
  · exact .callUndef hc hh hts hvs hp

@[simp] theorem EvalTerms.nil_iff {rs : List (Option GroundTerm)} : EvalTerms c σ [] rs ↔ rs = [] :=
  ⟨EvalTerms.nil_inv, fun h => h ▸ .nil⟩

@[simp] theorem EvalTerms.cons_iff {t : Term} {ts : List Term} {rs : List (Option GroundTerm)} :
    EvalTerms c σ (t :: ts) rs ↔ ∃ r rs', rs = r :: rs' ∧ EvalTerm c σ t r ∧ EvalTerms c σ ts rs' :=
  ⟨EvalTerms.cons_inv, fun ⟨_, _, hr, h, hs⟩ => hr ▸ .cons h hs⟩

@[simp high] theorem EvalTerms.nil_nil_iff : EvalTerms c σ [] [] ↔ True := iff_true_intro .nil

@[simp high] theorem EvalTerms.nil_cons_iff {r : Option GroundTerm}
    {rs : List (Option GroundTerm)} :
    EvalTerms c σ [] (r :: rs) ↔ False := ⟨fun h => (nomatch EvalTerms.nil_inv h), False.elim⟩

@[simp high] theorem EvalTerms.cons_nil_iff {t : Term} {ts : List Term} :
    EvalTerms c σ (t :: ts) [] ↔ False :=
  ⟨fun h => (by obtain ⟨_, _, h, -⟩ := EvalTerms.cons_inv h; cases h), False.elim⟩

@[simp high] theorem EvalTerms.cons_cons_iff {t : Term} {ts : List Term} {r : Option GroundTerm}
    {rs : List (Option GroundTerm)} :
    EvalTerms c σ (t :: ts) (r :: rs) ↔ EvalTerm c σ t r ∧ EvalTerms c σ ts rs :=
  ⟨fun h => (by obtain ⟨_, _, h, ht, hs⟩ := EvalTerms.cons_inv h; cases h; exact ⟨ht, hs⟩),
   fun h => .cons h.1 h.2⟩

/-! ## Introduction forms -/

/-- The `i`-th clause of `f` gives `f`'s result at `vs`: its patterns denote `vs` under a
well-sorted σ, its `requires` evaluates to `true`, its predicate is true (by default shown for
the predicate `\top`), the clauses of a smaller priority fail, its right-hand side has the result
`r` under σ, and its `ensures` evaluates to `true` (by default shown for a clause without one). -/
theorem Eval.of_clause {f : Sym} {fn : Fn} {i : Nat} {cl : Clause} {vs : List GroundTerm}
    {r : Option GroundTerm}
    (hfn : c.lookupFn f = some fn) (hi : fn.clauses[i]? = some cl)
    (hpre : ∀ cl' ∈ fn.clauses, cl'.prio < cl.prio → Fails c vs cl')
    (hσ : c.WellSorted cl.vars σ) (hmatch : PatVals c σ cl.pats vs)
    (hreq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
    (hrhs : EvalTerm c σ cl.rhs r)
    (hens : ∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true)) := by
      exact fun _ h => nomatch h)
    (hholds : Holds c cl.vars.length σ cl.pre true := by exact .top) : Eval c f vs r :=
  .clause hfn (List.mem_of_getElem? hi) hσ hmatch hreq hholds (fun cl' h _ hlt => hpre cl' h hlt) hrhs hens

/-- `Eval.of_clause` with the clause as a package's data lemma states it,
`(c.lookupFn f).bind (·.clauses[i]?) = some cl`; the clauses of a smaller priority are read the
same way. -/
theorem Eval.of_clause_bind {f : Sym} {i : Nat} {cl : Clause} {vs : List GroundTerm}
    {r : Option GroundTerm}
    (hcl : (c.lookupFn f).bind (·.clauses[i]?) = some cl)
    (hpre : ∀ (j : Nat) (cl' : Clause), (c.lookupFn f).bind (·.clauses[j]?) = some cl' → cl'.prio < cl.prio →
      Fails c vs cl')
    (hσ : c.WellSorted cl.vars σ) (hmatch : PatVals c σ cl.pats vs)
    (hreq : ∀ t, cl.req = some t → EvalTerm c σ t (some (bool true)))
    (hrhs : EvalTerm c σ cl.rhs r)
    (hens : ∀ t, cl.ens = some t → EvalTerm c σ t (some (bool true)) := by
      exact fun _ h => nomatch h)
    (hholds : Holds c cl.vars.length σ cl.pre true := by exact .top) : Eval c f vs r := by
  cases hfn : c.lookupFn f with
  | none => rw [hfn] at hcl; cases hcl
  | some fn =>
    rw [hfn] at hcl hpre
    refine Eval.of_clause hfn hcl (fun cl' hm hlt => ?_) hσ hmatch hreq hrhs hens hholds
    obtain ⟨j, hj, hjc⟩ := List.getElem_of_mem hm
    exact hpre j cl' (by rw [Option.bind_some, List.getElem?_eq_getElem hj, hjc]) hlt

/-- A clause without a `requires`, a predicate or an `ensures` that matches, every other clause of a priority at
most its own matching under no well-sorted σ, the clause not `aside` (so every clause of a larger
priority reads it), gives `f`'s only result: every result of `f` at `vs`
is its right-hand side's under some σ that matches. (Without functionality of `EvalTerm`, a `requires`
could both hold and fail, so a clause with one, or another clause that matches, does not determine
the result here.) -/
theorem Eval.inv_of_clause_bind {f : Sym} {i : Nat} {cl : Clause} {vs : List GroundTerm}
    {r : Option GroundTerm}
    (hcl : (c.lookupFn f).bind (·.clauses[i]?) = some cl)
    (hpre : ∀ j, j ≠ i → ∀ cl', (c.lookupFn f).bind (·.clauses[j]?) = some cl' → cl'.prio ≤ cl.prio →
      ∀ σ', c.WellSorted cl'.vars σ' → ¬ PatVals c σ' cl'.pats vs)
    (hnoreq : cl.req = none) (hσ : c.WellSorted cl.vars σ) (hmatch : PatVals c σ cl.pats vs)
    (h : Eval c f vs r) (hnoens : cl.ens = none := by rfl) (hna : cl.aside = false := by rfl)
    (hnopre : cl.pre = .top := by rfl) :
    ∃ σ', c.WellSorted cl.vars σ' ∧ PatVals c σ' cl.pats vs ∧ EvalTerm c σ' cl.rhs r := by
  -- the clause applies at `vs`, so it does not fail there
  have hnf : ¬ Fails c vs cl := fun ⟨hf⟩ => by
    cases hf σ (hσ.at _) hmatch with
    | intro ht _ _ => rw [hnoreq] at ht; cases ht
    | pre hp => rw [hnopre] at hp; exact absurd hp.top_eq (by simp)
  cases h with
  | @clause _ fn _ cl' σ' _ hfn hmem hσ' hmatch' _ _ hprio' hrhs _ =>
    rw [hfn] at hcl hpre
    simp only [Option.bind_some] at hcl hpre
    by_cases he : cl' = cl
    · subst he; exact ⟨σ', hσ', hmatch', hrhs⟩
    · obtain ⟨j, hj, hjc⟩ := List.getElem_of_mem hmem
      have hji : j ≠ i := fun hji => he (by
        subst hji
        rw [List.getElem?_eq_getElem hj, hjc] at hcl
        exact Option.some.inj hcl)
      by_cases hle : cl'.prio ≤ cl.prio
      · exact absurd hmatch' (hpre j hji cl' (by rw [List.getElem?_eq_getElem hj, hjc]) hle σ' hσ')
      · exact absurd (hprio' cl (List.mem_of_getElem? hcl) hna (by omega)) hnf
  | rest hfn hnone =>
    rw [hfn] at hcl
    exact absurd (hnone cl (List.mem_of_getElem? hcl)) hnf
  | @ensFails _ fn _ cl' σ' _ _ hfn hmem hσ' hmatch' _ _ hprio' ht _ _ =>
    rw [hfn] at hcl hpre
    simp only [Option.bind_some] at hcl hpre
    by_cases he : cl' = cl
    · subst he; rw [hnoens] at ht; cases ht
    · obtain ⟨j, hj, hjc⟩ := List.getElem_of_mem hmem
      have hji : j ≠ i := fun hji => he (by
        subst hji
        rw [List.getElem?_eq_getElem hj, hjc] at hcl
        exact Option.some.inj hcl)
      by_cases hle : cl'.prio ≤ cl.prio
      · exact absurd hmatch' (hpre j hji cl' (by rw [List.getElem?_eq_getElem hj, hjc]) hle σ' hσ')
      · exact absurd (hprio' cl (List.mem_of_getElem? hcl) hna (by omega)) hnf

/-- The `i`-th rule takes `x` to `y` when it fires there. -/
theorem Step.of_rule (hs : c.sortedOK = true) {x y : Config c} {i : Nat} {r : Rule}
    (hr : c.rules[i]? = some r) (h : Fires c r σ x y) : Step c x y :=
  (step_iff_fires hs).mpr ⟨r, List.mem_of_getElem? hr, σ, h⟩

/-- Progress by the `i`-th rule: a well-sorted σ under which its left-hand side denotes `x`, its
`requires` true, no rule of a smaller priority applying, its right-hand side defined and its
`ensures` true. The
successor is the right-hand side's value, a configuration by subject reduction (`step_of_apply`;
the overloading symbols' condition `OvlCase`, decided by default). -/
theorem Step.exists_of_rule_all (hok : c.okAll = true) (hsr : c.srReady = true) {x : Config c} {i : Nat}
    {r : Rule} (hr : c.rules[i]? = some r) (hσ : c.WellSorted r.vars σ)
    (hm : PatVal c σ r.lhs x.val) (hreq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true)))
    (hpre : Holds c r.vars.length σ r.pre true)
    (hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val)
    {v : GroundTerm} (he : EvalTerm c σ r.rhs (some v))
    (hens : ∀ t, r.ens = some t → EvalTerm c σ t (some (bool true)))
    (hpost : Holds c r.vars.length σ r.post true)
    (hov : c.OvlCase := by exact Semantics.ovlCase_of (by decide +kernel)) : ∃ y : Config c, y.val = v ∧ Step c x y :=
  ⟨_, rfl, step_of_apply_all hok hsr hov (List.mem_of_getElem? hr) hσ hm hreq hpre he hens hpost hprio⟩

/-- `Step.exists_of_rule_all` as the progress half of a symbolic step. -/
theorem Step.progress_of_rule_all (hok : c.okAll = true) (hsr : c.srReady = true) {x : Config c} {i : Nat}
    {r : Rule} (hr : c.rules[i]? = some r) (hσ : c.WellSorted r.vars σ)
    (hm : PatVal c σ r.lhs x.val) (hreq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true)))
    (hpre : Holds c r.vars.length σ r.pre true)
    (hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val)
    {v : GroundTerm} (he : EvalTerm c σ r.rhs (some v))
    (hens : ∀ t, r.ens = some t → EvalTerm c σ t (some (bool true)))
    (hpost : Holds c r.vars.length σ r.post true)
    (hov : c.OvlCase := by exact Semantics.ovlCase_of (by decide +kernel)) : Reachability.Progress (Step c) x :=
  let ⟨y, _, h⟩ := Step.exists_of_rule_all hok hsr hr hσ hm hreq hpre hprio he hens hpost hov
  ⟨y, h⟩

/-- `Step.exists_of_rule_all` in a core that `ok` accepts: its rules' predicates are `\top`
(`ok_rule`). -/
theorem Step.exists_of_rule (hok : c.ok = true) (hsr : c.srReady = true) {x : Config c} {i : Nat}
    {r : Rule} (hr : c.rules[i]? = some r) (hσ : c.WellSorted r.vars σ)
    (hm : PatVal c σ r.lhs x.val) (hreq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true)))
    (hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val)
    {v : GroundTerm} (he : EvalTerm c σ r.rhs (some v))
    (hens : ∀ t, r.ens = some t → EvalTerm c σ t (some (bool true)))
    (hov : c.OvlCase := by exact Semantics.ovlCase_of (by decide +kernel)) : ∃ y : Config c, y.val = v ∧ Step c x y :=
  Step.exists_of_rule_all (Semantics.okAll_of_ok hok) hsr hr hσ hm hreq
    ((Semantics.ok_rule hok (List.mem_of_getElem? hr)).2.1 ▸ .top) hprio he hens
    ((Semantics.ok_rule hok (List.mem_of_getElem? hr)).2.2.1 ▸ .top) hov

/-- `Step.exists_of_rule` as the progress half of a symbolic step. -/
theorem Step.progress_of_rule (hok : c.ok = true) (hsr : c.srReady = true) {x : Config c} {i : Nat}
    {r : Rule} (hr : c.rules[i]? = some r) (hσ : c.WellSorted r.vars σ)
    (hm : PatVal c σ r.lhs x.val) (hreq : ∀ t, r.req = some t → EvalTerm c σ t (some (bool true)))
    (hprio : ∀ r' ∈ c.rules, r'.prio < r.prio → NotApplies c r' x.val)
    {v : GroundTerm} (he : EvalTerm c σ r.rhs (some v))
    (hens : ∀ t, r.ens = some t → EvalTerm c σ t (some (bool true)))
    (hov : c.OvlCase := by exact Semantics.ovlCase_of (by decide +kernel)) : Reachability.Progress (Step c) x :=
  Step.progress_of_rule_all (Semantics.okAll_of_ok hok) hsr hr hσ hm hreq
    ((Semantics.ok_rule hok (List.mem_of_getElem? hr)).2.1 ▸ .top) hprio he hens
    ((Semantics.ok_rule hok (List.mem_of_getElem? hr)).2.2.1 ▸ .top) hov

/-! ## Which rule fired

A package states `rules_cases : r ∈ c.rules → c.rules[0]? = some r ∨ … ∨ c.rules[n-1]? = some r`
(its Surface module), the disjunction `AtOneOf c.rules r 0 n` written out, so that a case split
on it gives one case per rule, whose data its lemma `rule{i}` gives. `Step.cases_of` turns a step
into such a case split, each case with what the rule's firing requires (`Fires`). -/

/-- `a` is at one of the positions `k`, …, `k + n - 1` of `l`: the disjunction
`l[k]? = some a ∨ … ∨ l[k + n - 1]? = some a`, `False` when `n` is 0. -/
def AtOneOf {α : Type} (l : List α) (a : α) (k : Nat) : Nat → Prop
  | 0 => False
  | 1 => l[k]? = some a
  | n + 2 => l[k]? = some a ∨ AtOneOf l a (k + 1) (n + 1)

theorem AtOneOf.of_getElem? {α : Type} {l : List α} {a : α} :
    ∀ {k n i : Nat}, l[i]? = some a → k ≤ i → i < k + n → AtOneOf l a k n
  | _, 0, _, _, h1, h2 => absurd h2 (by omega)
  | k, 1, i, h, h1, h2 => by
    obtain rfl : i = k := by omega
    exact h
  | k, n + 2, i, h, h1, h2 => by
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact .inl h
    · exact .inr (AtOneOf.of_getElem? h hlt (by omega))

/-- An element of a list of length `n` is at one of its positions `0`, …, `n - 1`. -/
theorem atOneOf_of_mem {α : Type} {l : List α} {a : α} {n : Nat} (hn : l.length = n) (h : a ∈ l) :
    AtOneOf l a 0 n :=
  let ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
  AtOneOf.of_getElem? hi (Nat.zero_le _) (by
    have := (List.getElem?_eq_some_iff.mp hi).1
    omega)

/-- A step is by a rule that fires: its match under a well-sorted σ, its `requires`, its
right-hand side's value, its `ensures`, its predicates, and no rule of a smaller priority applying (`Fires`). The rule has every
property `P` that each firing rule has: with `P` a package's `rules_cases`, a case split on it is
one case per rule. -/
theorem Step.cases_of {P : Rule → Prop} {x y : Config c}
    (hcases : ∀ {r σ}, r ∈ c.rules → Fires c r σ x y → P r) (h : Step c x y) :
    ∃ r σ, P r ∧ Fires c r σ x y :=
  let ⟨r, hr, σ, hf⟩ := h.fires
  ⟨r, σ, hcases hr hf, hf⟩

end KCore
