/-
  The kit the helpers over `KCore.KK.emb` read, on kore.k's semantics read from its kompiled text.

  The embeddings of the mirrors `Sig` does not name: `embB` (`Bind`, KKMatchF.lean), `embMs`
  (`Ms`), `embRes` (`Res` as `Option T`), `embPrio` (`Prio` as `Option Int`), `embLook` (`Look`
  as `Option (List Cl)`), each at the symbol number the reader gives its production
  (`embKit_names`), and each a value of its kore.k sort at `K₀ sig`.

  `emb`'s inversion: `emb t` is the constructor term `headOf t` at `argsOf t` (`emb_ctor`), and the
  head names the mirror constructor (`headOf_eq_ap`, …, one per constructor of `T`); `embTs_nil_iff`
  and `embTs_cons_iff` invert `embTs`. At `K₀ sig` no function has a rest (`fnRest_none`), and an
  evaluation has one result (`evalF_iff`, from `Eval.functional` and `KK.coherent`).
-/
import User.Sig

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.KK

/-! ## The other mirrors' embeddings -/

/-- kore.k's `Bind`: `.Bind` and `bind(X, T, B)`. -/
def embB : Bind → GroundTerm
  | [] => .ctor 400 []
  | (x, t) :: b => .ctor 411 [.dv 3 (.int x), emb t, embB b]

/-- kore.k's `Ms`: `.Ms` and `m(B, Ms)`. -/
def embMs : Ms → GroundTerm
  | [] => .ctor 403 []
  | b :: ms => .ctor 428 [embB b, embMs ms]

/-- kore.k's `Res`: `none` and `some(T)`. -/
def embRes : Option T → GroundTerm
  | none => .ctor 433 []
  | some t => .ctor 439 [emb t]

/-- kore.k's `Prio`: `noP` and `at(I)`. -/
def embPrio : Option Int → GroundTerm
  | none => .ctor 431 []
  | some i => .ctor 410 [.dv 3 (.int i)]

/-- kore.k's `Look`: `nofn` and `fnd(Cs)`. -/
def embLook : Option (List Cl) → GroundTerm
  | none => .ctor 432 []
  | some cs => .ctor 422 [embCls cs]

/-- Each symbol number these embeddings use has the KORE name of the production written. -/
theorem embKit_names :
    RefKk.defn.sem.symName 400 = "Lbl'Stop'Bind'Unds'KORE'Unds'Bind" ∧
    RefKk.defn.sem.symName 411 = "Lblbind'LParUndsCommUndsCommUndsRParUnds'KORE'Unds'Bind'Unds'Int'Unds'Term'Unds'Bind" ∧
    RefKk.defn.sem.symName 403 = "Lbl'Stop'Ms'Unds'KORE'Unds'Ms" ∧
    RefKk.defn.sem.symName 428 = "Lblm'LParUndsCommUndsRParUnds'KORE'Unds'Ms'Unds'Bind'Unds'Ms" ∧
    RefKk.defn.sem.symName 433 = "Lblnone'Unds'KORE'Unds'Res" ∧
    RefKk.defn.sem.symName 439 = "Lblsome'LParUndsRParUnds'KORE'Unds'Res'Unds'Term" ∧
    RefKk.defn.sem.symName 431 = "LblnoP'Unds'KORE'Unds'Prio" ∧
    RefKk.defn.sem.symName 410 = "Lblat'LParUndsRParUnds'KORE'Unds'Prio'Unds'Int" ∧
    RefKk.defn.sem.symName 432 = "Lblnofn'Unds'KORE'Unds'Look" ∧
    RefKk.defn.sem.symName 422 = "Lblfnd'LParUndsRParUnds'KORE'Unds'Look'Unds'Clauses" ∧
    RefKk.defn.sem.sortName 36 = "Prio" ∧ RefKk.defn.sem.sortName 37 = "Ms" ∧
    RefKk.defn.sem.sortName 40 = "Look" ∧ RefKk.defn.sem.sortName 41 = "Res" ∧
    RefKk.defn.sem.sortName 46 = "Bind" := by
  decide +kernel

/-! ## Their sorts -/

section Sorts
open _root_.KK _root_.KK.Kit _root_.KK.Facts

theorem embB_sorted_c₀ : ∀ b : Bind, c₀.sortOf (embB b) = some 46
  | [] => sort_ctor sig_400 sorts_nil
  | (x, t) :: b =>
    sort_ctor sig_411 (sorts_cons (sort_int x) (sorts_cons (emb_sorted_c₀ t)
      (sorts_cons (embB_sorted_c₀ b) sorts_nil)))

theorem embMs_sorted_c₀ : ∀ ms : Ms, c₀.sortOf (embMs ms) = some 37
  | [] => sort_ctor sig_403 sorts_nil
  | b :: ms => sort_ctor sig_428 (sorts_cons (embB_sorted_c₀ b) (sorts_cons (embMs_sorted_c₀ ms) sorts_nil))

theorem embRes_sorted_c₀ : ∀ r : Option T, c₀.sortOf (embRes r) = some 41
  | none => sort_ctor sig_433 sorts_nil
  | some t => sort_ctor sig_439 (sorts_cons (emb_sorted_c₀ t) sorts_nil)

theorem embPrio_sorted_c₀ : ∀ p : Option Int, c₀.sortOf (embPrio p) = some 36
  | none => sort_ctor sig_431 sorts_nil
  | some i => sort_ctor sig_410 (sorts_cons (sort_int i) sorts_nil)

theorem embLook_sorted_c₀ : ∀ l : Option (List Cl), c₀.sortOf (embLook l) = some 40
  | none => sort_ctor sig_432 sorts_nil
  | some cs => sort_ctor sig_422 (sorts_cons (embCls_sorted_c₀ cs) sorts_nil)

end Sorts

theorem embB_sorted (b : Bind) : (K₀ sig).sortOf (embB b) = some 46 := embB_sorted_c₀ b
theorem embMs_sorted (ms : Ms) : (K₀ sig).sortOf (embMs ms) = some 37 := embMs_sorted_c₀ ms
theorem embRes_sorted (r : Option T) : (K₀ sig).sortOf (embRes r) = some 41 := embRes_sorted_c₀ r
theorem embPrio_sorted (p : Option Int) : (K₀ sig).sortOf (embPrio p) = some 36 := embPrio_sorted_c₀ p
theorem embLook_sorted (l : Option (List Cl)) : (K₀ sig).sortOf (embLook l) = some 40 :=
  embLook_sorted_c₀ l

/-! ## `emb`'s inversion -/

/-- The symbol `emb t` is headed by. -/
def headOf : T → Sym
  | .ap .. => 408 | .iv .. => 425 | .bv .. => 413 | .tk .. => 443 | .ij .. => 424 | .vr .. => 445
  | .as .. => 409 | .hk .. => 423 | .bot => 412 | .cb .. => 414 | .co .. => 416 | .en .. => 420
  | .kv .. => 426 | .el .. => 419

/-- The arguments of `emb t`'s head. -/
def argsOf : T → List GroundTerm
  | .ap f as => [.dv 3 (.int f), embTs as]
  | .iv i => [.dv 3 (.int i)]
  | .bv b => [.dv 2 (.bool b)]
  | .tk s x => [.dv 3 (.int s), .dv 10 (.tok x)]
  | .ij a b t => [.dv 3 (.int a), .dv 3 (.int b), emb t]
  | .vr i => [.dv 3 (.int i)]
  | .as p i => [emb p, .dv 3 (.int i)]
  | .hk o as => [.dv 3 (.int o), embTs as]
  | .bot => []
  | .cb k c ps => [embK k, .dv 3 (.int c), embTs ps]
  | .co k c es => [embK k, .dv 3 (.int c), embTs es]
  | .en t e => [emb t, emb e]
  | .kv a v => [emb a, emb v]
  | .el x => [emb x]

theorem emb_ctor (t : T) : emb t = .ctor (headOf t) (argsOf t) := by
  cases t <;> rw [emb] <;> rfl

theorem headOf_eq_ap {t : T} : headOf t = 408 ↔ ∃ f as, t = .ap f as := by
  cases t <;> simp [headOf]
theorem headOf_eq_iv {t : T} : headOf t = 425 ↔ ∃ i, t = .iv i := by
  cases t <;> simp [headOf]
theorem headOf_eq_bv {t : T} : headOf t = 413 ↔ ∃ b, t = .bv b := by
  cases t <;> simp [headOf]
theorem headOf_eq_tk {t : T} : headOf t = 443 ↔ ∃ s x, t = .tk s x := by
  cases t <;> simp [headOf]
theorem headOf_eq_ij {t : T} : headOf t = 424 ↔ ∃ a b u, t = .ij a b u := by
  cases t <;> simp [headOf]
theorem headOf_eq_vr {t : T} : headOf t = 445 ↔ ∃ i, t = .vr i := by
  cases t <;> simp [headOf]
theorem headOf_eq_as {t : T} : headOf t = 409 ↔ ∃ p i, t = .as p i := by
  cases t <;> simp [headOf]
theorem headOf_eq_hk {t : T} : headOf t = 423 ↔ ∃ o as, t = .hk o as := by
  cases t <;> simp [headOf]
theorem headOf_eq_bot {t : T} : headOf t = 412 ↔ t = .bot := by
  cases t <;> simp [headOf]
theorem headOf_eq_cb {t : T} : headOf t = 414 ↔ ∃ k c ps, t = .cb k c ps := by
  cases t <;> simp [headOf]
theorem headOf_eq_co {t : T} : headOf t = 416 ↔ ∃ k c es, t = .co k c es := by
  cases t <;> simp [headOf]
theorem headOf_eq_en {t : T} : headOf t = 420 ↔ ∃ u e, t = .en u e := by
  cases t <;> simp [headOf]
theorem headOf_eq_kv {t : T} : headOf t = 426 ↔ ∃ a v, t = .kv a v := by
  cases t <;> simp [headOf]
theorem headOf_eq_el {t : T} : headOf t = 419 ↔ ∃ x, t = .el x := by
  cases t <;> simp [headOf]

theorem embTs_nil_iff {ts : List T} : embTs ts = .ctor 406 [] ↔ ts = [] := by
  cases ts with
  | nil => rw [embTs]; simp
  | cons t ts => rw [embTs]; simp

theorem embTs_cons_iff {ts : List T} {a b : GroundTerm} :
    embTs ts = .ctor 407 [a, b] ↔ ∃ t ts', ts = t :: ts' ∧ emb t = a ∧ embTs ts' = b := by
  cases ts with
  | nil => rw [embTs]; simp
  | cons t ts =>
    rw [embTs]; constructor
    · intro h
      simp only [GroundTerm.ctor.injEq, List.cons.injEq, and_true, true_and] at h
      exact ⟨t, ts, rfl, h⟩
    · rintro ⟨_, _, h, h1, h2⟩; cases h; rw [h1, h2]

/-! ## Evaluation at `K₀ sig` -/

/-- No function of kore.k has a rest at `K₀ sig`. -/
theorem fnRest_none (fn : Fn) (vs : List GroundTerm) : (K₀ sig).fnRest fn vs = none := rfl

/-- An evaluation at `K₀ sig` has one result. -/
theorem evalF_iff {f : Sym} {vs : List GroundTerm} {v r : Option GroundTerm}
    (h : Eval (K₀ sig) f vs v) : Eval (K₀ sig) f vs r ↔ r = v :=
  ⟨fun h' => Eval.functional _root_.KK.coherent h' h, fun e => e ▸ h⟩

/-! ## Checks -/

#check @embB
#check @embMs
#check @embRes
#check @embPrio
#check @embLook
#check @emb_ctor
#check @embTs_nil_iff
#check @embTs_cons_iff
#check @fnRest_none
#check @evalF_iff

open Lean in
#eval show CoreM Unit from do
  for n in [``embKit_names, ``embB_sorted, ``embMs_sorted, ``embRes_sorted, ``embPrio_sorted,
      ``embLook_sorted, ``emb_ctor, ``headOf_eq_ap, ``headOf_eq_iv, ``headOf_eq_bv, ``headOf_eq_tk,
      ``headOf_eq_ij, ``headOf_eq_vr, ``headOf_eq_as, ``headOf_eq_hk, ``headOf_eq_bot, ``headOf_eq_cb,
      ``headOf_eq_co, ``headOf_eq_en, ``headOf_eq_kv, ``headOf_eq_el, ``embTs_nil_iff, ``embTs_cons_iff,
      ``fnRest_none, ``evalF_iff] do
    let axs ← collectAxioms n
    unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "{n}: axioms {axs}"

end KCore.KK
