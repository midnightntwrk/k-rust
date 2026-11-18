/-
  The heads at which the premises of `Γc c ∪ Γstep c` apply their symbols.

  - **The heads of an AML pattern (`headsP`).** A KORE application `σ{s̄}(φ̄)` is translated as the
    chain `σ s̄ φ̄` from the symbol `.symbol σ` (`KoreAML.tr`, T-app with its sort arguments); the
    sorts are chains from sort symbols (`trSort`), and no translated pattern is one (`root_tr`).
    So the head of a chain from `.symbol n` is `n` with the leading arguments that are sorts
    (`sortArgB`), the longest such prefix, exactly: `Lblite SortInt φ` has the head
    `(Lblite, [SortInt])` and not `(Lblite, [])`.
  - **The translation keeps the heads (`headsP_tr`).** Every head of the translation of a KORE
    pattern is the translation of one of the pattern's heads (`appHeadsOf`) whose sort arguments
    are sort constructors.
-/
import KcoreSpec.GenEqsWalk
import KcoreSpec.TieHeads

set_option autoImplicit false

namespace KCore

open ML Faithful

namespace GHWalk

open KoreAML (P)

/-- The pattern is a sort as the translation writes one: a chain from a sort symbol. -/
def sortArgB (p : P) : Bool :=
  match GenEqs.root p with
  | some (.sort _) => true
  | _ => false

/-- The heads of the applications of a pattern that is applied to `args`: at a chain from the
symbol `.symbol n`, the name with the longest prefix of its arguments that are sorts; then the
heads of the arguments and of the other parts. -/
def headsA : List P → P → List (String × List P)
  | args, .application a b => headsA (b :: args) a ++ headsA [] b
  | args, .symbol (.symbol n) => [(n, args.takeWhile sortArgB)]
  | _, .implication a b => headsA [] a ++ headsA [] b
  | _, .existential _ a => headsA [] a
  | _, .mu _ a => headsA [] a
  | _, _ => []

/-- **The heads of a pattern**: each the name of a symbol `.symbol n` that a chain starts at, with
the sorts it is applied to. -/
def headsP (φ : P) : List (String × List P) := headsA [] φ

/-- A KORE head as the translation writes it: its sort arguments translated. -/
def headP (t : KoreAML.VarTable) (h : String × List Kore.KSort) : String × List P :=
  (h.1, h.2.map (KoreAML.trSort t))

/-- The heads of `gammaHeads`, as the translation writes them. -/
def gammaHeadsP (c : Semantics) : List (String × List P) := (gammaHeads c).map (headP [])

/-! ## Computing heads -/

@[simp] theorem headsA_app (args : List P) (a b : P) :
    headsA args (a ⬝ b) = headsA (b :: args) a ++ headsA [] b := rfl
@[simp] theorem headsA_imp (args : List P) (a b : P) :
    headsA args (a ⇒ b) = headsA [] a ++ headsA [] b := rfl
@[simp] theorem headsA_ex (args : List P) (x : EVar) (a : P) :
    headsA args (.existential x a) = headsA [] a := rfl
@[simp] theorem headsA_mu (args : List P) (X : SVar) (a : P) : headsA args (.mu X a) = headsA [] a := rfl
@[simp] theorem headsA_bot (args : List P) : headsA args (⊥ : P) = [] := rfl
@[simp] theorem headsA_evar (args : List P) (x : EVar) : headsA args (.evar x : P) = [] := rfl
@[simp] theorem headsA_svar (args : List P) (X : SVar) : headsA args (.svar X : P) = [] := rfl
@[simp] theorem headsA_symbol (args : List P) (n : String) :
    headsA args (.symbol (.symbol n) : P) = [(n, args.takeWhile sortArgB)] := rfl
@[simp] theorem headsA_defined (args : List P) : headsA args (.symbol HasDefined.defined : P) = [] := rfl
@[simp] theorem headsA_inh (args : List P) : headsA args (.symbol .inh : P) = [] := rfl
@[simp] theorem headsA_sortSort (args : List P) : headsA args (.symbol .sortSort : P) = [] := rfl
@[simp] theorem headsA_sort (args : List P) (n : String) : headsA args (.symbol (.sort n) : P) = [] := rfl
@[simp] theorem headsA_ceil (args : List P) : headsA args (.symbol .ceil : P) = [] := rfl
@[simp] theorem headsA_next (args : List P) : headsA args (.symbol .next : P) = [] := rfl
@[simp] theorem headsA_dv (args : List P) (l : String) : headsA args (.symbol (.dv l) : P) = [] := rfl
@[simp] theorem headsA_str (args : List P) (l : String) : headsA args (.symbol (.str l) : P) = [] := rfl
@[simp] theorem headsA_untranslated (args : List P) (l : String) :
    headsA args (.symbol (.untranslated l) : P) = [] := rfl

@[simp] theorem headsP_def (φ : P) : headsP φ = headsA [] φ := rfl

/-- A chain's heads: its start's, applied to its arguments, and its arguments'. -/
theorem headsA_appList : ∀ (xs : List P) (h : P) (args : List P),
    headsA args (KoreAML.appList h xs) = headsA (xs ++ args) h ++ xs.flatMap (headsA [])
  | [], h, args => by simp [KoreAML.appList]
  | x :: xs, h, args => by
    rw [KoreAML.appList, headsA_appList xs (h ⬝ x) args, headsA_app]
    simp [List.append_assoc]

/-- A pattern whose chain does not start at a symbol has the heads of its parts whatever it is
applied to. -/
theorem headsA_of_root_none : ∀ {φ : P}, GenEqs.root φ = none → ∀ args, headsA args φ = headsA [] φ
  | .application a _, h, args => by
    simp only [GenEqs.root] at h
    simp only [headsA_app, headsA_of_root_none h (_ :: args), headsA_of_root_none h [_]]
  | .implication _ _, _, _ => rfl
  | .existential _ _, _, _ => rfl
  | .mu _ _, _, _ => rfl
  | .evar _, _, _ => rfl
  | .svar _, _, _ => rfl
  | .bottom, _, _ => rfl
  | .symbol _, h, _ => by simp [GenEqs.root] at h

@[simp] theorem root_app (a b : P) : GenEqs.root (a ⬝ b) = GenEqs.root a := rfl

theorem root_appList : ∀ (xs : List P) (h : P), GenEqs.root (KoreAML.appList h xs) = GenEqs.root h
  | [], _ => rfl
  | x :: xs, h => by rw [KoreAML.appList, root_appList xs (h ⬝ x)]; rfl

/-! ## The connectives -/

section Conn

variable (args : List P)

theorem headsA_neg (a : P) : headsA args (∼a) = headsA [] a := by simp [Pattern.negation]
theorem headsA_or (a b : P) : headsA args (a ⋁ b) = headsA [] a ++ headsA [] b := by
  simp [Pattern.disjunction, Pattern.negation]
theorem headsA_and (a b : P) : headsA args (a ⋀ b) = headsA [] a ++ headsA [] b := by
  simp [Pattern.conjunction, Pattern.disjunction, Pattern.negation]
theorem headsA_ceilD (a : P) : headsA args ⌈a⌉ = headsA [] a := by simp
theorem headsA_total (a : P) : headsA args (ML.total a) = headsA [] a := by
  simp [ML.total, Pattern.negation]
theorem headsA_eq (a b : P) : headsA args (a ≡ b) = headsA [] a ++ headsA [] b ++ (headsA [] b ++ headsA [] a) := by
  simp [ML.equal, ML.total, Pattern.equivalence, Pattern.conjunction, Pattern.disjunction, Pattern.negation,
]
theorem headsA_member (x : EVar) (a : P) : headsA args (x ∈∈ a) = headsA [] a := by
  simp [ML.member, Pattern.conjunction, Pattern.disjunction, Pattern.negation]
theorem headsA_included (a b : P) : headsA args (a ⊆⊆ b) = headsA [] a ++ headsA [] b := by
  simp [ML.included, ML.total, Pattern.negation]
theorem headsA_forall (x : EVar) (a : P) : headsA args (∀∀ x a) = headsA [] a := by
  simp [Pattern.universal, Pattern.negation]
theorem headsA_inhOf (s : P) : headsA args (KoreAML.inhOf s) = headsA [] s := by
  simp [KoreAML.inhOf, KoreAML.sym]

end Conn

/-! ## Sorts, and the start of a translated pattern -/

theorem trArgs_appListG (ctx : KoreAML.Ctx) : ∀ (acc : P) (ps : List Kore.Pattern),
    KoreAML.trArgs ctx acc ps = KoreAML.appList acc (ps.map (KoreAML.tr ctx))
  | acc, [] => by rw [KoreAML.trArgs]; rfl
  | acc, p :: ps => by rw [KoreAML.trArgs, trArgs_appListG ctx _ ps]; rfl

theorem trSortApp_appListG (t : KoreAML.VarTable) : ∀ (acc : P) (ss : List Kore.KSort),
    KoreAML.trSortApp t acc ss = KoreAML.appList acc (ss.map (KoreAML.trSort t))
  | acc, [] => by rw [KoreAML.trSortApp]; rfl
  | acc, s :: ss => by rw [KoreAML.trSortApp, trSortApp_appListG t _ ss]; rfl

open KoreAML in
mutual
/-- A sort holds no head. -/
theorem headsA_trSort (t : VarTable) : ∀ (s : Kore.KSort) (args : List P), headsA args (trSort t s) = []
  | .var _, _ => by rw [trSort]; rfl
  | .ctor _ ss, args => by
    rw [trSort, trSortApp_appListG, headsA_appList]
    simp only [sym, headsA_sort, List.nil_append]
    exact headsA_trSortL t ss
theorem headsA_trSortL (t : VarTable) : ∀ (ss : List Kore.KSort), (ss.map (trSort t)).flatMap (headsA []) = []
  | [] => rfl
  | s :: ss => by rw [List.map_cons, List.flatMap_cons, headsA_trSort t s [], headsA_trSortL t ss]; rfl
end

theorem sortArgB_symbol (n : String) (xs : List P) :
    sortArgB (KoreAML.appList (KoreAML.sym (.symbol n)) xs) = false := by
  simp [sortArgB, root_appList, KoreAML.sym, GenEqs.root]

theorem sortArgB_trLeftAssocRest (ctx : KoreAML.Ctx) (n : String) (ss : List P) :
    ∀ (ps : List Kore.Pattern) (acc : P), sortArgB acc = false →
      sortArgB (KoreAML.trLeftAssocRest ctx (KoreAML.appList (KoreAML.sym (.symbol n)) ss) acc ps) = false
  | [], _, h => by rw [KoreAML.trLeftAssocRest]; exact h
  | p :: ps, acc, _ => by
    rw [KoreAML.trLeftAssocRest]
    refine sortArgB_trLeftAssocRest ctx n ss ps _ ?_
    simpa [sortArgB, root_appList, KoreAML.sym, GenEqs.root] using sortArgB_symbol n ss

open KoreAML in
mutual
/-- **No translated pattern is a sort**: its chain starts at a symbol other than a sort symbol, or
it is no chain. -/
theorem sortArgB_tr (ctx : Ctx) : ∀ p : Kore.Pattern, sortArgB (tr ctx p) = false
  | .var (.evar _) => by rw [tr]; rfl
  | .var (.svar _) => by rw [tr]; rfl
  | .app h ss ps => by
    rw [tr]
    split
    · rfl
    · rw [trArgs_appListG, trSortApp_appListG]
      simp [sortArgB, root_appList, sym, GenEqs.root]
  | .string _ => by rw [tr]; rfl
  | .top _ => by rw [tr]; rfl
  | .bottom _ => by rw [tr]; rfl
  | .not _ _ => by rw [tr]; rfl
  | .and s ps => by rw [tr]; exact sortArgB_trAndList ctx ps _
  | .or s ps => by rw [tr]; exact sortArgB_trOrList ctx ps _
  | .implies _ _ _ => by rw [tr]; rfl
  | .iff _ _ _ => by rw [tr]; rfl
  | .exist _ _ _ => by rw [tr]; rfl
  | .forall _ _ _ => by rw [tr]; rfl
  | .mu _ _ => by rw [tr]; rfl
  | .nu _ _ => by rw [tr]; rfl
  | .ceil _ _ _ => by rw [tr]; rfl
  | .floor _ _ _ => by rw [tr]; rfl
  | .equals _ _ _ _ => by rw [tr]; rfl
  | .in _ _ _ _ => by rw [tr]; rfl
  | .next _ _ => by rw [tr]; rfl
  | .rewrites _ _ _ => by rw [tr]; rfl
  | .dv _ _ => by rw [tr]; rfl
  | .leftAssoc h ss ps => by
    rw [tr, trSortApp_appListG]
    cases ps with
    | nil => rw [trLeftAssoc]; exact sortArgB_symbol _ _
    | cons p ps =>
      rw [trLeftAssoc]
      exact sortArgB_trLeftAssocRest ctx _ _ ps _ (sortArgB_tr ctx p)
  | .rightAssoc h ss ps => by
    rw [tr, trSortApp_appListG]
    exact sortArgB_trRightAssoc ctx ps _ (sortArgB_symbol _ _)
theorem sortArgB_trAndList (ctx : Ctx) : ∀ (ps : List Kore.Pattern) (s : P), sortArgB (trAndList ctx s ps) = false
  | [], _ => by rw [trAndList]; rfl
  | [p], _ => by rw [trAndList]; exact sortArgB_tr ctx p
  | _ :: _ :: _, _ => by rw [trAndList]; rfl
theorem sortArgB_trOrList (ctx : Ctx) : ∀ (ps : List Kore.Pattern) (s : P), sortArgB (trOrList ctx s ps) = false
  | [], _ => by rw [trOrList]; rfl
  | [p], _ => by rw [trOrList]; exact sortArgB_tr ctx p
  | _ :: _ :: _, _ => by rw [trOrList]; rfl
theorem sortArgB_trRightAssoc (ctx : Ctx) : ∀ (ps : List Kore.Pattern) (head : P), sortArgB head = false →
    sortArgB (trRightAssoc ctx head ps) = false
  | [], _, h => by rw [trRightAssoc]; exact h
  | [p], _, _ => by rw [trRightAssoc]; exact sortArgB_tr ctx p
  | _ :: _ :: _, head, h => by
    rw [trRightAssoc]
    simpa [sortArgB, GenEqs.root] using h
end

/-! ## Substituting a set variable -/

theorem root_substSvar (X : SVar) {χ : P} (hχ : GenEqs.root χ = none) :
    ∀ a : P, GenEqs.root (a.substSvar X χ) = GenEqs.root a
  | .application a _ => by simp only [Pattern.substSvar, root_app]; exact root_substSvar X hχ a
  | .svar Y => by
    simp only [Pattern.substSvar]
    split
    · exact hχ
    · rfl
  | .mu Y _ => by
    simp only [Pattern.substSvar]
    split <;> rfl
  | .symbol _ => rfl
  | .evar _ => rfl
  | .bottom => rfl
  | .implication _ _ => rfl
  | .existential _ _ => rfl

theorem sortArgB_substSvar (X : SVar) {χ : P} (hχ : GenEqs.root χ = none) (a : P) :
    sortArgB (a.substSvar X χ) = sortArgB a := by
  simp only [sortArgB, root_substSvar X hχ a]

/-- Substituting a pattern that is no chain for a set variable: each head is one of the
pattern's, its sort arguments substituted or not, or one of the substituted pattern's. -/
theorem headsA_substSvar (X : SVar) {χ : P} (hχ : GenEqs.root χ = none) :
    ∀ (φ : P) (args : List P), ∀ h ∈ headsA (args.map (·.substSvar X χ)) (φ.substSvar X χ),
      h ∈ headsA args φ ∨ (∃ h' ∈ headsA args φ, h = (h'.1, h'.2.map (·.substSvar X χ))) ∨ h ∈ headsP χ
  | .application a b, args, h, hh => by
    simp only [Pattern.substSvar, headsA_app, List.mem_append] at hh ⊢
    rcases hh with hh | hh
    · rcases headsA_substSvar X hχ a (b :: args) h (by simpa using hh) with h1 | ⟨h', h2, rfl⟩ | h3
      · exact .inl (.inl h1)
      · exact .inr (.inl ⟨h', .inl h2, rfl⟩)
      · exact .inr (.inr h3)
    · rcases headsA_substSvar X hχ b [] h (by simpa using hh) with h1 | ⟨h', h2, rfl⟩ | h3
      · exact .inl (.inr h1)
      · exact .inr (.inl ⟨h', .inr h2, rfl⟩)
      · exact .inr (.inr h3)
  | .symbol (.symbol n), args, h, hh => by
    simp only [Pattern.substSvar, headsA_symbol, List.mem_singleton] at hh
    refine .inr (.inl ⟨_, List.mem_singleton_self _, ?_⟩)
    have hs : (sortArgB ∘ fun x : P => x.substSvar X χ) = sortArgB := funext fun a => sortArgB_substSvar X hχ a
    rw [hh, List.takeWhile_map, hs]
  | .symbol .defined, _, _, hh => absurd hh List.not_mem_nil
  | .symbol .inh, _, _, hh => absurd hh List.not_mem_nil
  | .symbol .sortSort, _, _, hh => absurd hh List.not_mem_nil
  | .symbol (.sort _), _, _, hh => absurd hh List.not_mem_nil
  | .symbol .ceil, _, _, hh => absurd hh List.not_mem_nil
  | .symbol .next, _, _, hh => absurd hh List.not_mem_nil
  | .symbol (.dv _), _, _, hh => absurd hh List.not_mem_nil
  | .symbol (.str _), _, _, hh => absurd hh List.not_mem_nil
  | .symbol (.untranslated _), _, _, hh => absurd hh List.not_mem_nil
  | .svar Y, args, h, hh => by
    simp only [Pattern.substSvar] at hh
    split at hh
    · rw [headsA_of_root_none hχ] at hh; exact .inr (.inr hh)
    · simp at hh
  | .mu Y a, args, h, hh => by
    simp only [Pattern.substSvar] at hh
    split at hh
    · exact .inl (by simpa using hh)
    · rcases headsA_substSvar X hχ a [] h (by simpa using hh) with h1 | ⟨h', h2, rfl⟩ | h3
      · exact .inl (by simpa using h1)
      · exact .inr (.inl ⟨h', by simpa using h2, rfl⟩)
      · exact .inr (.inr h3)
  | .existential x a, args, h, hh => by
    simp only [Pattern.substSvar, headsA_ex] at hh
    rcases headsA_substSvar X hχ a [] h (by simpa using hh) with h1 | ⟨h', h2, rfl⟩ | h3
    · exact .inl (by simpa using h1)
    · exact .inr (.inl ⟨h', by simpa using h2, rfl⟩)
    · exact .inr (.inr h3)
  | .implication a b, args, h, hh => by
    simp only [Pattern.substSvar, headsA_imp, List.mem_append] at hh ⊢
    rcases hh with hh | hh
    · rcases headsA_substSvar X hχ a [] h (by simpa using hh) with h1 | ⟨h', h2, rfl⟩ | h3
      · exact .inl (.inl h1)
      · exact .inr (.inl ⟨h', .inl h2, rfl⟩)
      · exact .inr (.inr h3)
    · rcases headsA_substSvar X hχ b [] h (by simpa using hh) with h1 | ⟨h', h2, rfl⟩ | h3
      · exact .inl (.inr h1)
      · exact .inr (.inl ⟨h', .inr h2, rfl⟩)
      · exact .inr (.inr h3)
  | .evar _, _, _, hh => by simp [Pattern.substSvar] at hh
  | .bottom, _, _, hh => by simp [Pattern.substSvar] at hh

/-! ## The translation keeps the heads -/

theorem appList_appendG : ∀ (h : P) (xs ys : List P),
    KoreAML.appList h (xs ++ ys) = KoreAML.appList (KoreAML.appList h xs) ys
  | _, [], _ => rfl
  | h, x :: xs, ys => appList_appendG (h ⬝ x) xs ys

theorem takeWhile_append_ofG {f : P → Bool} : ∀ (xs ys : List P), (∀ x ∈ xs, f x = true) →
    (∀ y ∈ ys.head?, f y = false) → (xs ++ ys).takeWhile f = xs
  | [], [], _, _ => rfl
  | [], y :: ys, _, hy => by simp [List.takeWhile_cons, hy y rfl]
  | x :: xs, ys, hx, hy => by
    rw [List.cons_append, List.takeWhile_cons, hx x (List.mem_cons_self ..),
      takeWhile_append_ofG xs ys (fun z hz => hx z (List.mem_cons_of_mem _ hz)) hy]
    rfl

/-- The heads of a chain from `.symbol n` applied to sorts that hold no head, then to arguments the
first of which is no sort: `n` with those sorts, and the arguments' heads. -/
theorem headsP_chain (n : String) (ss xs : List P) (hs : ∀ s ∈ ss, sortArgB s = true ∧ headsA [] s = [])
    (hx : ∀ y ∈ xs.head?, sortArgB y = false) :
    ∀ h ∈ headsA [] (KoreAML.appList (KoreAML.sym (.symbol n)) (ss ++ xs)), h = (n, ss) ∨ ∃ x ∈ xs, h ∈ headsA [] x := by
  intro h hh
  rw [headsA_appList, KoreAML.sym, headsA_symbol, List.append_nil,
    takeWhile_append_ofG ss xs (fun s hs' => (hs s hs').1) hx] at hh
  rcases List.mem_append.mp hh with hh | hh
  · exact .inl (List.mem_singleton.mp hh)
  · obtain ⟨x, hx', hh⟩ := List.mem_flatMap.mp hh
    rcases List.mem_append.mp hx' with hx' | hx'
    · rw [(hs x hx').2] at hh; exact absurd hh List.not_mem_nil
    · exact .inr ⟨x, hx', hh⟩

/-- The heads of the KORE pattern meet `okP` as the translation at `t` writes them, and their sort
arguments are sorts the translation writes as chains from sort symbols. -/
def KHeadsOK (t : KoreAML.VarTable) (okP : String × List P → Prop) (hs : List (String × List Kore.KSort)) :
    Prop :=
  ∀ h ∈ hs, okP (headP t h) ∧ ∀ s ∈ h.2, sortArgB (KoreAML.trSort t s) = true

theorem KHeadsOK.append {t : KoreAML.VarTable} {okP : String × List P → Prop}
    {a b : List (String × List Kore.KSort)} (h : KHeadsOK t okP (a ++ b)) : KHeadsOK t okP a ∧ KHeadsOK t okP b :=
  ⟨fun x hx => h x (List.mem_append_left _ hx), fun x hx => h x (List.mem_append_right _ hx)⟩

/-- `okP` holds of a head with its sort arguments substituted where it holds of the head. -/
def SubstStable (okP : String × List P → Prop) : Prop :=
  ∀ n ss, okP (n, ss) → ∀ (X : SVar) (χ : P), okP (n, ss.map (·.substSvar X χ))

theorem sorts_ok {t : KoreAML.VarTable} (ss : List Kore.KSort)
    (h : ∀ s ∈ ss, sortArgB (KoreAML.trSort t s) = true) :
    ∀ s ∈ ss.map (KoreAML.trSort t), sortArgB s = true ∧ headsA [] s = [] := by
  intro s hs
  obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
  exact ⟨h s' hs', headsA_trSort t s' []⟩

/-- The heads of `νX. a` at the sort `s`: those of `a`, with their sort arguments substituted or not. -/
theorem headsP_sNu (s : P) (X : SVar) (a : P) (hs : headsA [] s = []) :
    ∀ h ∈ headsP (KoreAML.sNu s X a), h ∈ headsP a ∨
      ∃ h' ∈ headsP a, h = (h'.1, h'.2.map (·.substSvar X (KoreAML.sNot s (.svar X)))) := by
  intro h hh
  simp only [KoreAML.sNu, KoreAML.sNot, headsP_def, headsA_and, headsA_neg, headsA_inhOf, headsA_mu, hs,
    List.append_nil] at hh
  rcases headsA_substSvar X (χ := (∼(.svar X : P)) ⋀ KoreAML.inhOf s) rfl a [] h (by simpa using hh) with
    h1 | h2 | h3
  · exact .inl h1
  · exact .inr h2
  · simp only [headsP_def, headsA_and, headsA_neg, headsA_inhOf, headsA_svar, hs, List.append_nil] at h3
    exact absurd h3 List.not_mem_nil

/-- The simplification set for the connectives of the translation. -/
macro "gh_conn" h:ident : tactic => `(tactic| simp only [KoreAML.sTop, KoreAML.sBot, KoreAML.sNot, KoreAML.sAnd,
  KoreAML.sOr, KoreAML.sImp, KoreAML.sIff, KoreAML.sExists, KoreAML.sForall, KoreAML.sCeil, KoreAML.sFloor,
  KoreAML.sEquals, KoreAML.sIn, KoreAML.sNext, KoreAML.sRewrites, headsA_neg, headsA_and, headsA_or,
  headsA_member, headsA_inhOf, headsA_app, headsA_ex, headsA_mu, headsA_imp, headsA_bot, headsA_evar,
  headsA_svar, headsA_trSort, KoreAML.sym, headsA_ceil, headsA_next, headsA_dv, headsA_str, headsP_def,
  List.mem_append, List.not_mem_nil, false_or, or_false, or_self] at $h:ident)

open KoreAML in
/-- A right-associated application's heads, from its operands'. -/
theorem headsP_trRightAssoc (ctx : Ctx) (okP : String × List P → Prop)
    (n : String) (ss : List Kore.KSort)
    (hk0 : okP (headP ctx.vars (n, ss)) ∧ ∀ s ∈ ss, sortArgB (trSort ctx.vars s) = true) :
    ∀ (ps : List Kore.Pattern), (∀ p ∈ ps, ∀ h ∈ headsP (tr ctx p), okP h) →
      ∀ h ∈ headsP (trRightAssoc ctx (KoreAML.appList (sym (.symbol n)) (ss.map (trSort ctx.vars))) ps), okP h
  | [], _, h, hh => by
    rw [trRightAssoc] at hh
    rcases headsP_chain _ _ [] (sorts_ok ss hk0.2) (fun _ h => nomatch h) h (by rw [List.append_nil]; exact hh) with
      rfl | ⟨_, hx, _⟩
    · exact hk0.1
    · cases hx
  | [p], hp, h, hh => by
    rw [trRightAssoc] at hh
    exact hp p (List.mem_singleton_self _) h hh
  | p :: q :: ps, hp, h, hh => by
    rw [trRightAssoc] at hh
    have e : KoreAML.appList (sym (.symbol n)) (ss.map (trSort ctx.vars)) ⬝ tr ctx p ⬝
        trRightAssoc ctx (KoreAML.appList (sym (.symbol n)) (ss.map (trSort ctx.vars))) (q :: ps) =
        KoreAML.appList (sym (.symbol n)) (ss.map (trSort ctx.vars) ++
          [tr ctx p, trRightAssoc ctx (KoreAML.appList (sym (.symbol n)) (ss.map (trSort ctx.vars))) (q :: ps)]) := by
      rw [appList_appendG]; rfl
    rw [headsP_def, e] at hh
    rcases headsP_chain _ _ _ (sorts_ok ss hk0.2) (by intro y hy; cases hy; exact sortArgB_tr ctx p) h hh with
      rfl | ⟨x, hx, hm⟩
    · exact hk0.1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hp _ (List.mem_cons_self ..) h hm
      · exact headsP_trRightAssoc ctx okP n ss hk0 (q :: ps) (fun x hx => hp x (List.mem_cons_of_mem _ hx)) h hm

open KoreAML in
theorem headsP_trAndList (ctx : Ctx) (okP : String × List P → Prop) :
    ∀ (ps : List Kore.Pattern) (s : P), headsA [] s = [] → (∀ p ∈ ps, ∀ h ∈ headsP (tr ctx p), okP h) →
      ∀ h ∈ headsP (trAndList ctx s ps), okP h
  | [], s, hs, _, h, hh => by rw [trAndList] at hh; gh_conn hh; rw [hs] at hh; exact absurd hh List.not_mem_nil
  | [p], _, _, hp, h, hh => by rw [trAndList] at hh; exact hp p (List.mem_singleton_self _) h hh
  | p :: q :: ps, s, hs, hp, h, hh => by
    rw [trAndList] at hh; gh_conn hh
    rcases hh with hh | hh
    · exact hp p (List.mem_cons_self ..) h hh
    · exact headsP_trAndList ctx okP (q :: ps) s hs (fun x hx => hp x (List.mem_cons_of_mem _ hx)) h hh

open KoreAML in
theorem headsP_trOrList (ctx : Ctx) (okP : String × List P → Prop) :
    ∀ (ps : List Kore.Pattern) (s : P), headsA [] s = [] → (∀ p ∈ ps, ∀ h ∈ headsP (tr ctx p), okP h) →
      ∀ h ∈ headsP (trOrList ctx s ps), okP h
  | [], s, hs, _, h, hh => by rw [trOrList] at hh; gh_conn hh; rw [hs] at hh; gh_conn hh
  | [p], _, _, hp, h, hh => by rw [trOrList] at hh; exact hp p (List.mem_singleton_self _) h hh
  | p :: q :: ps, s, hs, hp, h, hh => by
    rw [trOrList] at hh; gh_conn hh
    rw [hs] at hh; gh_conn hh
    rcases hh with hh | hh
    · exact hp p (List.mem_cons_self ..) h hh
    · exact headsP_trOrList ctx okP (q :: ps) s hs (fun x hx => hp x (List.mem_cons_of_mem _ hx)) h hh

open KoreAML in
theorem headsP_trLeftAssocRest (ctx : Ctx) (okP : String × List P → Prop)
    (n : String) (ss : List Kore.KSort)
    (hk0 : okP (headP ctx.vars (n, ss)) ∧ ∀ s ∈ ss, sortArgB (trSort ctx.vars s) = true) :
    ∀ (ps : List Kore.Pattern) (acc : P), sortArgB acc = false → (∀ h ∈ headsP acc, okP h) →
      (∀ p ∈ ps, ∀ h ∈ headsP (tr ctx p), okP h) →
      ∀ h ∈ headsP (trLeftAssocRest ctx (KoreAML.appList (sym (.symbol n)) (ss.map (trSort ctx.vars))) acc ps), okP h
  | [], _, _, ha, _, h, hh => by rw [trLeftAssocRest] at hh; exact ha h hh
  | p :: ps, acc, hsa, ha, hp, h, hh => by
    rw [trLeftAssocRest] at hh
    refine headsP_trLeftAssocRest ctx okP n ss hk0 ps _ ?_ ?_ (fun x hx => hp x (List.mem_cons_of_mem _ hx)) h hh
    · simp only [sortArgB, root_appList, sym, GenEqs.root]
    · intro h' hh'
      have e : KoreAML.appList (sym (.symbol n)) (ss.map (trSort ctx.vars)) ⬝ acc ⬝ tr ctx p =
          KoreAML.appList (sym (.symbol n)) (ss.map (trSort ctx.vars) ++ [acc, tr ctx p]) := by
        rw [appList_appendG]; rfl
      rw [headsP_def, e] at hh'
      rcases headsP_chain _ _ _ (sorts_ok ss hk0.2) (by intro y hy; cases hy; exact hsa) h' hh' with
        rfl | ⟨x, hx, hm⟩
      · exact hk0.1
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact ha h' hm
        · exact hp _ (List.mem_cons_self ..) h' hm

open KoreAML in
mutual
/-- **Every head of a translated pattern is the translation of one of its heads**: where every
head of the KORE pattern meets `okP` as the translation writes it (and its sort arguments are sort
constructors), every head of its translation meets `okP`. -/
theorem headsP_tr (ctx : Ctx) (okP : String × List P → Prop) (hst : SubstStable okP) :
    ∀ p : Kore.Pattern, KHeadsOK ctx.vars okP (appHeadsOf p) → ∀ h ∈ headsP (tr ctx p), okP h
  | .var (.evar _), _, _, hh => by rw [tr] at hh; exact absurd hh List.not_mem_nil
  | .var (.svar _), _, _, hh => by rw [tr] at hh; exact absurd hh List.not_mem_nil
  | .app hd ss ps, hk, h, hh => by
    rw [tr] at hh
    split at hh
    · exact absurd hh List.not_mem_nil
    · rw [trArgs_appListG, trSortApp_appListG, ← appList_appendG] at hh
      have hk0 := hk _ (List.mem_cons_self ..)
      rcases headsP_chain _ _ _ (sorts_ok ss hk0.2) (by
          intro y hy
          cases ps with
          | nil => cases hy
          | cons p _ => cases hy; exact sortArgB_tr ctx p) h hh with rfl | ⟨x, hx, hh⟩
      · exact hk0.1
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
        exact headsP_trL ctx okP hst ps (fun x hx => hk x (List.mem_cons_of_mem _ hx)) p hp h hh
  | .string _, _, _, hh => by rw [tr] at hh; exact absurd hh List.not_mem_nil
  | .top _, _, _, hh => by rw [tr] at hh; gh_conn hh
  | .bottom _, _, _, hh => by rw [tr] at hh; gh_conn hh
  | .not _ p, hk, h, hh => by
    rw [tr] at hh; gh_conn hh; exact headsP_tr ctx okP hst p hk h hh
  | .and s ps, hk, h, hh => by
    rw [tr] at hh; exact headsP_trAndList ctx okP ps _ (headsA_trSort _ _ _) (headsP_trL ctx okP hst ps hk) h hh
  | .or s ps, hk, h, hh => by
    rw [tr] at hh; exact headsP_trOrList ctx okP ps _ (headsA_trSort _ _ _) (headsP_trL ctx okP hst ps hk) h hh
  | .implies _ p q, hk, h, hh => by
    have hk' := KHeadsOK.append hk
    rw [tr] at hh; gh_conn hh
    repeat' (first | exact headsP_tr ctx okP hst p hk'.1 h hh | exact headsP_tr ctx okP hst q hk'.2 h hh |
      (rcases hh with hh | hh))
  | .iff _ p q, hk, h, hh => by
    have hk' := KHeadsOK.append hk
    rw [tr] at hh; gh_conn hh
    repeat' (first | exact headsP_tr ctx okP hst p hk'.1 h hh | exact headsP_tr ctx okP hst q hk'.2 h hh |
      (rcases hh with hh | hh))
  | .exist _ _ p, hk, h, hh => by
    rw [tr] at hh; gh_conn hh; exact headsP_tr ctx okP hst p hk h hh
  | .forall _ _ p, hk, h, hh => by
    rw [tr] at hh; gh_conn hh; exact headsP_tr ctx okP hst p hk h hh
  | .mu _ p, hk, h, hh => by
    rw [tr] at hh; gh_conn hh; exact headsP_tr ctx okP hst p hk h hh
  | .nu _ p, hk, h, hh => by
    rw [tr] at hh
    rcases headsP_sNu _ _ _ (headsA_trSort _ _ _) h hh with h1 | ⟨⟨n, ss⟩, h2, rfl⟩
    · exact headsP_tr ctx okP hst p hk h h1
    · exact hst n ss (headsP_tr ctx okP hst p hk _ h2) _ _
  | .ceil _ _ p, hk, h, hh => by
    rw [tr] at hh; gh_conn hh; exact headsP_tr ctx okP hst p hk h hh
  | .floor _ _ p, hk, h, hh => by
    rw [tr] at hh; gh_conn hh; exact headsP_tr ctx okP hst p hk h hh
  | .equals _ _ p q, hk, h, hh => by
    have hk' := KHeadsOK.append hk
    rw [tr] at hh; gh_conn hh
    repeat' (first | exact headsP_tr ctx okP hst p hk'.1 h hh | exact headsP_tr ctx okP hst q hk'.2 h hh |
      (rcases hh with hh | hh))
  | .in _ _ p q, hk, h, hh => by
    have hk' := KHeadsOK.append hk
    rw [tr] at hh; gh_conn hh
    repeat' (first | exact headsP_tr ctx okP hst p hk'.1 h hh | exact headsP_tr ctx okP hst q hk'.2 h hh |
      (rcases hh with hh | hh))
  | .next _ p, hk, h, hh => by
    rw [tr] at hh; gh_conn hh; exact headsP_tr ctx okP hst p hk h hh
  | .rewrites _ p q, hk, h, hh => by
    have hk' := KHeadsOK.append hk
    rw [tr] at hh; gh_conn hh
    repeat' (first | exact headsP_tr ctx okP hst p hk'.1 h hh | exact headsP_tr ctx okP hst q hk'.2 h hh |
      (rcases hh with hh | hh))
  | .dv _ _, _, _, hh => by
    rw [tr, headsP_def, headsA_app, headsA_trSort, List.append_nil] at hh
    exact absurd hh List.not_mem_nil
  | .leftAssoc hd ss ps, hk, h, hh => by
    have hk0 := hk _ (List.mem_cons_self ..)
    have hrest : KHeadsOK ctx.vars okP (appHeadsOfList ps) := fun x hx => hk x (List.mem_cons_of_mem _ hx)
    rw [tr, trSortApp_appListG] at hh
    cases ps with
    | nil =>
      rw [trLeftAssoc] at hh
      rcases headsP_chain _ _ [] (sorts_ok ss hk0.2) (fun _ h => nomatch h) h (by rw [List.append_nil]; exact hh) with rfl | ⟨_, hx, _⟩
      · exact hk0.1
      · cases hx
    | cons p ps =>
      rw [trLeftAssoc] at hh
      have hr := KHeadsOK.append (show KHeadsOK ctx.vars okP (appHeadsOf p ++ appHeadsOfList ps) from hrest)
      exact headsP_trLeftAssocRest ctx okP hd.ident.name ss hk0 ps _ (sortArgB_tr ctx p)
        (headsP_tr ctx okP hst p hr.1) (headsP_trL ctx okP hst ps hr.2) h hh
  | .rightAssoc hd ss ps, hk, h, hh => by
    rw [appHeadsOf] at hk
    have hk0 := hk _ (List.mem_cons_self ..)
    have hrest : KHeadsOK ctx.vars okP (appHeadsOfList ps) := fun x hx => hk x (List.mem_cons_of_mem _ hx)
    rw [tr, trSortApp_appListG] at hh
    exact headsP_trRightAssoc ctx okP hd.ident.name ss hk0 ps (headsP_trL ctx okP hst ps hrest) h hh
  termination_by structural p _ _ _ => p
theorem headsP_trL (ctx : Ctx) (okP : String × List P → Prop) (hst : SubstStable okP) :
    ∀ ps : List Kore.Pattern, KHeadsOK ctx.vars okP (appHeadsOfList ps) →
      ∀ p ∈ ps, ∀ h ∈ headsP (tr ctx p), okP h
  | [], _, _, hp, _, _ => nomatch hp
  | q :: qs, hk, p, hp, h, hh => by
    have hk' := KHeadsOK.append (show KHeadsOK ctx.vars okP (appHeadsOf q ++ appHeadsOfList qs) from hk)
    rcases List.mem_cons.mp hp with he | hp
    · rw [he] at hh; exact headsP_tr ctx okP hst q hk'.1 h hh
    · exact headsP_trL ctx okP hst qs hk'.2 p hp h hh
  termination_by structural ps _ _ _ _ _ => ps
end

/-! ## At Γ's heads -/

/-- The sort arguments of Γ's heads are sorts without parameters (`srt`). -/
theorem gammaHeads_sorts (c : Semantics) : ∀ h ∈ gammaHeads c, ∀ s ∈ h.2, ∃ X, s = KoreAML.srt X := by
  intro h hh s hs
  simp only [gammaHeads, List.mem_append, List.mem_map] at hh
  rcases hh with ⟨k, -, rfl⟩ | ⟨⟨a, b⟩, -, rfl⟩
  · unfold gammaHead at hs
    cases hX : iteSort? (c.symName k.name) with
    | none => rw [hX] at hs; cases hs
    | some X => rw [hX] at hs; exact ⟨X, List.mem_singleton.mp hs⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

theorem trSort_srtG (t : KoreAML.VarTable) (X : String) :
    KoreAML.trSort t (KoreAML.srt X) = KoreAML.sym (.sort ("Sort" ++ X)) := by
  simp [KoreAML.srt, KoreAML.trSort, KoreAML.trSortApp]

/-- A head of Γ is written alike at every variable table. -/
theorem headP_gamma {c : Semantics} {h : String × List Kore.KSort} (hh : h ∈ gammaHeads c)
    (t : KoreAML.VarTable) : headP t h = headP [] h := by
  unfold headP
  congr 1
  refine List.map_congr_left fun s hs => ?_
  obtain ⟨X, rfl⟩ := gammaHeads_sorts c h hh s hs
  rw [trSort_srtG, trSort_srtG]

/-- Γ's heads, as the translation writes them, are kept by substituting for a set variable: their
sort arguments are symbols. -/
theorem gammaHeadsP_stable (c : Semantics) : SubstStable (· ∈ gammaHeadsP c) := by
  intro n ss hm X χ
  have : ss.map (·.substSvar X χ) = ss := by
    obtain ⟨g, hg, he⟩ := List.mem_map.mp hm
    have h2 : ss = g.2.map (KoreAML.trSort []) := (congrArg Prod.snd he).symm
    rw [h2, List.map_map]
    refine List.map_congr_left fun s hs => ?_
    obtain ⟨Y, rfl⟩ := gammaHeads_sorts c g hg s hs
    simp only [Function.comp_apply, trSort_srtG, KoreAML.sym, Pattern.substSvar]
  rw [this]; exact hm

/-- **A translated pattern whose heads are Γ's applies Γ's heads only**: every head of the
translation of a KORE pattern all of whose heads (`appHeadsOf`) are in `gammaHeads c` is one of
`gammaHeads c`, as the translation writes it. -/
theorem headsP_tr_gamma (c : Semantics) (ctx : KoreAML.Ctx) (p : Kore.Pattern)
    (hp : ∀ h ∈ appHeadsOf p, h ∈ gammaHeads c) : ∀ h ∈ headsP (KoreAML.tr ctx p), h ∈ gammaHeadsP c :=
  headsP_tr ctx _ (gammaHeadsP_stable c) p fun h hh => by
    refine ⟨?_, fun s hs => ?_⟩
    · rw [headP_gamma (hp h hh)]; exact List.mem_map_of_mem (hp h hh)
    · obtain ⟨X, rfl⟩ := gammaHeads_sorts c h (hp h hh) s hs
      rw [trSort_srtG]; rfl

end GHWalk

end KCore
