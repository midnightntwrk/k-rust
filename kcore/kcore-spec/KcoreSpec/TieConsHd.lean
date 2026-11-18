/-
  The constructor sentences of a text decided without enumerating Γ's constructor items.

  `tieConsB` searches every constructor sort N, every generator g of N and every pair of them, and
  each of `tieFunB`, `tieInjB` and `tieDistB` asks whether an item is in `consItemsK c` by scanning
  that list. Where a sort has many generators (KItem, with an injection from each cell sort of a
  deep configuration) the list holds the distinctness item of every pair of them, so the scan, run
  for each sentence, is quadratic in the generators.

  `tchConsB` decides the same sentences with the item's membership shown once, here: Cons-Fun,
  Cons-Inj and Cons-Dist are in `consItemsK c` for the generators `consItemsK` builds them from
  (`funItem_mem`, `injItem_mem`, `distItem_mem`). It asks of a generator what those lemmas take
  (non-open, not a function-overloaded symbol, a distinct pair not of two injections and not
  `distGuarded`), and the rest of `tieFunB`, `tieInjB` and `tieDistB` as written (`tchFunShapeB`,
  `tchInjShapeB`, `tchDistShapeB`). It tries only the sort the sentence is stated at and the
  generators whose head is the one the sentence applies (`tchHdB`, a necessary condition of the
  shape: the translated application with its arguments stripped is the generator's head).
  `tchConsB_sound`: what it accepts, `tieConsB` accepts.
-/
import KcoreSpec.TieCons
import KcoreSpec.FaithfulNeg

set_option autoImplicit false

namespace KCore
open ML Faithful
namespace Faithful

/-- The pattern with its last `n` arguments removed (`appList h xs` with `n = xs.length` is `h`). -/
def tchStrip : Nat → KoreAML.P → KoreAML.P
  | n + 1, .application p _ => tchStrip n p
  | _, p => p

/-- The head `KoreAML.Cons.genPat N g` applies to its arguments. -/
def tchBase (N : String) : KoreAML.Gen → KoreAML.P
  | .ctor k => KoreAML.sym (.symbol k.name)
  | .inj A => KoreAML.appList (KoreAML.sym (.symbol "inj")) [KoreAML.Cons.sortP A, KoreAML.Cons.sortP N]

/-- The sort a constructor sentence is stated at, and the translations of the applications whose
generators it names: the right side of a `functional` or `subsort` sentence, the first conjunct of
a no-confusion sentence of one generator, the two conjuncts of one of two. -/
def tchKeys (a : Kore.Axiom) : Option (Kore.KSort × KoreAML.P × Option KoreAML.P) :=
  let t := KoreAML.tableOf a.sortVars a.pattern
  match a.pattern with
  | .exist _ _ (.equals s _ _ body) => some (s, KoreAML.tr ⟨t, []⟩ body, none)
  | .implies s (.and _ [p1, _]) _ => some (s, KoreAML.tr ⟨t, []⟩ p1, none)
  | .not s (.and _ [p1, p2]) => some (s, KoreAML.tr ⟨t, []⟩ p1, some (KoreAML.tr ⟨t, []⟩ p2))
  | _ => none

/-- The generator `g` of N heads the translated application `q`. -/
def tchHdB (c : Semantics) (N : Srt) (g : Gen) (q : KoreAML.P) : Bool :=
  decide (tchStrip (Gen.toK c g).argSorts.length q = tchBase (c.sortName N) (Gen.toK c g))

/-- `tieFunB` but its last conjunct (Γ holds the generator's Cons-Fun item). -/
def tchFunShapeB (c : Semantics) (N : Srt) (g : KoreAML.Gen) (a : Kore.Axiom) : Bool :=
  match a.pattern with
  | .exist r val (.equals s r' (.var (.evar val')) body) =>
    let t := KoreAML.tableOf a.sortVars a.pattern
    let ks := tieKeyVars (KoreAML.freeOf [] a.pattern).eraseDups
    decide (s = KoreAML.srt (c.sortName N)) && decide (r = KoreAML.R) && decide (r' = KoreAML.R) &&
    decide (val' = val) && decide (N < nRegSorts + c.sortNames.length) &&
    decide ((a.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] a.pattern).eraseDups =
      .sortVar "R" :: ks.map KoreAML.evarKey) &&
    decide (val.sort = KoreAML.srt (c.sortName N)) && decide (ks.map (·.sort) = g.argSorts.map KoreAML.srt) &&
    decide (KoreAML.tr ⟨t, []⟩ body =
      KoreAML.Cons.genPat (c.sortName N) g ((ks.map fun k => t.ev (KoreAML.evarKey k)).map .evar)) &&
    decide (t.ev (KoreAML.evarKey val) ∉ t.ev (.sortVar "R") :: ks.map fun k => t.ev (KoreAML.evarKey k))
  | _ => false

/-- `tieInjB` but its last two conjuncts (Γ holds the generator's Cons-Fun and Cons-Inj items). -/
def tchInjShapeB (c : Semantics) (N : Srt) (g : KoreAML.Gen) (a : Kore.Axiom) : Bool :=
  match a.pattern with
  | .implies s (.and s' [p1, p2]) q =>
    let t := KoreAML.tableOf a.sortVars a.pattern
    let vs := tieKeyVars (KoreAML.freeOf [] a.pattern).eraseDups
    let xs := vs.take g.argSorts.length
    let ys := vs.drop g.argSorts.length
    let ix := xs.map fun k => t.ev (KoreAML.evarKey k)
    let iy := ys.map fun k => t.ev (KoreAML.evarKey k)
    decide (s = KoreAML.srt (c.sortName N)) && decide (s' = KoreAML.srt (c.sortName N)) &&
    decide ((a.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] a.pattern).eraseDups =
      (xs ++ ys).map KoreAML.evarKey) &&
    decide (xs.map (·.sort) = g.argSorts.map KoreAML.srt) && decide (ys.map (·.sort) = g.argSorts.map KoreAML.srt) &&
    decide (KoreAML.tr ⟨t, []⟩ p1 = KoreAML.Cons.genPat (c.sortName N) g (ix.map .evar)) &&
    decide (KoreAML.tr ⟨t, []⟩ p2 = KoreAML.Cons.genPat (c.sortName N) g (iy.map .evar)) &&
    decide (KoreAML.tr ⟨t, []⟩ q = KoreAML.Cons.genPat (c.sortName N) g
      ((ix.zip iy).map fun p => KoreAML.sAnd (.evar p.1) (.evar p.2)))
  | _ => false

/-- `tieDistB` but its last three conjuncts (Γ holds the generators' Cons-Fun items and their
Cons-Dist item). -/
def tchDistShapeB (c : Semantics) (N : Srt) (g g' : KoreAML.Gen) (a : Kore.Axiom) : Bool :=
  match a.pattern with
  | .not s (.and s' [p1, p2]) =>
    let t := KoreAML.tableOf a.sortVars a.pattern
    let vs := tieKeyVars (KoreAML.freeOf [] a.pattern).eraseDups
    let xs := vs.take g.argSorts.length
    let ys := vs.drop g.argSorts.length
    let ix := xs.map fun k => t.ev (KoreAML.evarKey k)
    let iy := ys.map fun k => t.ev (KoreAML.evarKey k)
    decide (s = KoreAML.srt (c.sortName N)) && decide (s' = KoreAML.srt (c.sortName N)) &&
    decide ((a.sortVars.map KoreAML.sortVarKey ++ KoreAML.freeOf [] a.pattern).eraseDups =
      (xs ++ ys).map KoreAML.evarKey) &&
    decide (xs.map (·.sort) = g.argSorts.map KoreAML.srt) && decide (ys.map (·.sort) = g'.argSorts.map KoreAML.srt) &&
    decide (KoreAML.tr ⟨t, []⟩ p1 = KoreAML.Cons.genPat (c.sortName N) g (ix.map .evar)) &&
    decide (KoreAML.tr ⟨t, []⟩ p2 = KoreAML.Cons.genPat (c.sortName N) g' (iy.map .evar))
  | _ => false

/-- Not two injections: `consItemsK` states the distinctness of two injections by their sorts'
order and lower bounds, of any other pair by `distItem` or `distUncItem`. -/
def tchNotInjs : Gen → Gen → Bool
  | .inj _, .inj _ => false
  | _, _ => true

/-- **The constructor sentences, decided at the sentence's sort and heads.** A sort N of
`consSorts c` that the sentence is stated at, and a non-open generator of N heading its
application, not a function-overloaded symbol, of whose `functional` (or `subsort`) sentence or
no-confusion sentence the sentence has the shape; or two distinct such generators, not two
injections and not `distGuarded` in either order, of whose no-confusion sentence it has the shape. -/
def tchConsB (c : Semantics) (a : Kore.Axiom) : Bool :=
  match tchKeys a with
  | none => false
  | some (s, q1, q2) => (consSorts c).any fun N =>
    decide (s = KoreAML.srt (c.sortName N)) &&
    let fr := (c.gens N).filter (!c.isOpenGen ·)
    (fr.any fun g => tchHdB c N g q1 && !c.fnOvl g &&
      (tchFunShapeB c N (Gen.toK c g) a || (!g.argSorts.isEmpty && tchInjShapeB c N (Gen.toK c g) a))) ||
    (match q2 with
      | none => false
      | some q => fr.any fun g => tchHdB c N g q1 && !c.fnOvl g && fr.any fun g' =>
          tchHdB c N g' q && !c.fnOvl g' && decide (Gen.toK c g ≠ Gen.toK c g') && tchNotInjs g g' &&
          !c.distGuarded g g' && !c.distGuarded g' g && tchDistShapeB c N (Gen.toK c g) (Gen.toK c g') a)

section
variable {c : Semantics}

theorem tch_and {x y : Bool} (hx : x = true) (hy : y = true) : (x && y) = true := by simp [hx, hy]

theorem tch_any_of_mem {it : KoreAML.Item} (h : it ∈ consItemsK c) :
    (consItemsK c).any (fun x => decide (x.pat = it.pat)) = true :=
  List.any_eq_true.mpr ⟨it, h, decide_eq_true rfl⟩

theorem tieFunB_of_shape {N : Srt} {g : KoreAML.Gen} {a : Kore.Axiom} (hs : tchFunShapeB c N g a = true)
    (hm : KoreAML.Cons.funItem (c.sortName N) g ∈ consItemsK c) : tieFunB c N g a = true := by
  unfold tchFunShapeB at hs
  unfold tieFunB
  split at hs
  · rename_i heq
    split
    · rename_i heq2
      rw [heq] at heq2; cases heq2
      exact tch_and hs (tch_any_of_mem hm)
    · rename_i hno; exact absurd heq (hno _ _ _ _ _ _)
  · exact absurd hs Bool.false_ne_true

theorem tieInjB_of_shape {N : Srt} {g : KoreAML.Gen} {a : Kore.Axiom} (hs : tchInjShapeB c N g a = true)
    (hf : KoreAML.Cons.funItem (c.sortName N) g ∈ consItemsK c)
    (hi : KoreAML.Cons.injItem (c.sortName N) g ∈ consItemsK c) : tieInjB c N g a = true := by
  unfold tchInjShapeB at hs
  unfold tieInjB
  split at hs
  · rename_i heq
    split
    · rename_i heq2
      rw [heq] at heq2; cases heq2
      exact tch_and (tch_and hs (tch_any_of_mem hf)) (tch_any_of_mem hi)
    · rename_i hno; exact (hno _ _ _ _ _ heq).elim
  · exact absurd hs Bool.false_ne_true

theorem tieDistB_of_shape {N : Srt} {g g' : KoreAML.Gen} {a : Kore.Axiom} (hs : tchDistShapeB c N g g' a = true)
    (hf : KoreAML.Cons.funItem (c.sortName N) g ∈ consItemsK c)
    (hf' : KoreAML.Cons.funItem (c.sortName N) g' ∈ consItemsK c)
    (hd : KoreAML.Cons.distItem (c.sortName N) g g' ∈ consItemsK c ∨
      KoreAML.Cons.distItem (c.sortName N) g' g ∈ consItemsK c) : tieDistB c N g g' a = true := by
  unfold tchDistShapeB at hs
  unfold tieDistB
  split at hs
  · rename_i heq
    split
    · rename_i heq2
      rw [heq] at heq2; cases heq2
      refine tch_and (tch_and (tch_and hs (tch_any_of_mem hf)) (tch_any_of_mem hf')) ?_
      rcases hd with hd | hd
      · simp only [tch_any_of_mem hd, Bool.true_or]
      · simp only [tch_any_of_mem hd, Bool.or_true]
    · rename_i hno; exact (hno _ _ _ _ heq).elim
  · exact absurd hs Bool.false_ne_true

/-- **What `tchConsB` accepts, `tieConsB` accepts.** -/
theorem tchConsB_sound {a : Kore.Axiom} (h : tchConsB c a = true) : tieConsB c a = true := by
  unfold tchConsB at h
  split at h
  · exact absurd h Bool.false_ne_true
  rename_i s q1 q2 _
  obtain ⟨N, hN, h⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨-, h⟩ := h
  unfold tieConsB
  refine List.any_eq_true.mpr ⟨N, hN, ?_⟩
  have hk : ∀ g ∈ (c.gens N).filter (!c.isOpenGen ·), Gen.toK c g ∈ (c.gens N).map (Gen.toK c) :=
    fun g hg => List.mem_map.mpr ⟨g, (List.mem_filter.mp hg).1, rfl⟩
  simp only [List.any_eq_true, Bool.or_eq_true]
  rcases h with h | h
  · obtain ⟨g, hg, h⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨-, hnf⟩, h⟩ := h
    refine ⟨Gen.toK c g, hk g hg, ?_⟩
    rcases h with h | ⟨hne, h⟩
    · exact Or.inl (Or.inl (tieFunB_of_shape h (funItem_mem hN hg hnf)))
    · have hne' : g.argSorts ≠ [] := fun h0 => by simp [h0] at hne
      exact Or.inl (Or.inr (tieInjB_of_shape h (funItem_mem hN hg hnf) (injItem_mem hN hg hne' hnf)))
  · split at h
    · exact absurd h Bool.false_ne_true
    obtain ⟨g, hg, h⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨-, hnf⟩, h⟩ := h
    obtain ⟨g', hg', h⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨-, hnf'⟩, hne⟩, hni⟩, hgd⟩, hgd'⟩, hs⟩ := h
    refine ⟨Gen.toK c g, hk g hg, Or.inr ⟨Gen.toK c g', hk g' hg', ?_⟩⟩
    have hni2 : ∀ a b, g = .inj a → g' = .inj b → False := by
      intro a b ha hb; subst ha hb; exact absurd hni (by simp [tchNotInjs])
    have hgg : g ≠ g' := fun e => hne (e ▸ rfl)
    refine tieDistB_of_shape hs (funItem_mem hN hg hnf) (funItem_mem hN hg' hnf') ?_
    rcases mem_pairs_of hgg hg hg' with hp | hp
    · exact Or.inl (distItem_mem hN hp hni2 hgd)
    · exact Or.inr (distItem_mem hN hp (fun a b hb ha => hni2 b a ha hb) hgd')

/-- `tchConsB` over a list gives `tieConsB` over it. -/
theorem tchConsB_all {l : List KoreAML.AxiomDecl} (h : l.all (fun ad => tchConsB c ad.ax) = true) :
    l.all (fun ad => tieConsB c ad.ax) = true :=
  List.all_eq_true.mpr fun ad had => tchConsB_sound (List.all_eq_true.mp h ad had)

end

end Faithful
end KCore
