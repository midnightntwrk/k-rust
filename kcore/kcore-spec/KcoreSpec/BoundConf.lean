/-
  KCore. The Bools that bound a condition's binders, beside `Cond.bound`.

  `Cond.boundConf c` asks of every binder a sort where the values and the elements agree in every
  interpretation whose confined sorts hold values' elements only: an `ex` or `all` variable of a
  confined sort, a match variable held by its pattern under constructors and injections or of a
  confined sort. The Holds lemmas that read a binder by its sort alone (`BinderFacts`) are stated
  over it. `Cond.boundV c val` admits also an `ex` binder of a sort `val` admits whose body fixes
  the bound variable by a term over the other variables (`Cond.fixes`).
  - `Cond.boundV_false`, `Cond.boundV_of_boundConf`: `Cond.boundConf` is `Cond.boundV` with `val`
    admitting no sort, and every `Cond.boundV` accepts what it accepts;
  - `Cond.bound_eq_boundV`: `Cond.bound` is `Cond.boundV` with `val` the test of a sort with a
    value, `Semantics.hasValue`;
  - `Cond.bound_of_boundConf`, `Cond.boundV_hasValue_of_bound`: so `Cond.bound` accepts what
    `Cond.boundConf` accepts, and `Cond.boundV c c.hasValue` what `Cond.bound` accepts;
  - `Cond.fixes_mono`, `Cond.boundV_mono`, `Cond.bound_of_boundV_valued`: a wider `val` (and a
    wider `ok`) accepts more, so `Cond.bound` accepts every condition `Cond.boundV c c.valued`
    accepts (`Semantics.hasValue_of_valued`);
  - `Clause.fixedExs_mono`, `Semantics.clausePlainEx_of_valued`: likewise `Clause.fixedExs`, so
    `Semantics.clausePlainEx` accepts every clause it accepts with `Semantics.valued` in place of
    `Semantics.hasValue`.
-/
import KcoreSpec.ClausePlainEx

set_option autoImplicit false

namespace KCore

/-- The binders of a condition range where values and elements agree by their sorts alone: an
`exMatch` variable is held by its pattern under constructors and injections, or is of a confined
sort; an `ex` or `all` variable is of a confined sort. -/
def Cond.boundConf (c : Semantics) (n : Nat) : Cond → Bool
  | .exMatch ys _ p _ body =>
      (List.range ys.length).all (fun j =>
        (ctorOccs c p).contains (n + j) || (ys[j]?.map c.confined).getD false) &&
      Cond.boundConf c (n + ys.length) body
  | .ex s body | .all s body => c.confined s && Cond.boundConf c (n + 1) body
  | .not p => Cond.boundConf c n p
  | .and p q | .or p q | .implies p q => Cond.boundConf c n p && Cond.boundConf c n q
  | _ => true

/-- `Cond.boundConf` with one more case at an `ex` binder: its sort is confined, or `val` admits it
and the body fixes the bound variable by a term over the other variables (`Cond.fixes`). An `all`
binder and the binders of a match are as in `Cond.boundConf`. `Cond.bound` is it at
`Semantics.hasValue` (`Cond.bound_eq_boundV`). -/
def Cond.boundV (c : Semantics) (val : Srt → Bool) (n : Nat) : Cond → Bool
  | .exMatch ys _ p _ body =>
      (List.range ys.length).all (fun j =>
        (ctorOccs c p).contains (n + j) || (ys[j]?.map c.confined).getD false) &&
      Cond.boundV c val (n + ys.length) body
  | .ex s body =>
      (c.confined s || (val s && Cond.fixes c.confined val (fun j => j != n) n (n + 1) body)) &&
      Cond.boundV c val (n + 1) body
  | .all s body => c.confined s && Cond.boundV c val (n + 1) body
  | .not p => Cond.boundV c val n p
  | .and p q | .or p q | .implies p q => Cond.boundV c val n p && Cond.boundV c val n q
  | _ => true

/-- `Cond.bound` is `Cond.boundV` where `val` is the test of a sort with a value,
`Semantics.hasValue`. -/
theorem Cond.bound_eq_boundV (c : Semantics) : Cond.bound c = Cond.boundV c c.hasValue :=
  funext fun n => funext fun p => go p n
where
  go : ∀ (p : Cond) (n : Nat), Cond.bound c n p = Cond.boundV c c.hasValue n p
  | .top, _ | .bot, _ | .ceil .., _ | .equals .., _ | .mem .., _ => by simp [Cond.bound, Cond.boundV]
  | .not p, n => by rw [Cond.bound, Cond.boundV, go p n]
  | .and p q, n | .or p q, n | .implies p q, n => by rw [Cond.bound, Cond.boundV, go p n, go q n]
  | .exMatch ys s p t body, n => by rw [Cond.bound, Cond.boundV, go body _]
  | .ex s body, n => by rw [Cond.bound, Cond.boundV, go body _]
  | .all s body, n => by rw [Cond.bound, Cond.boundV, go body _]

/-- A condition `Cond.boundConf` accepts, every `Cond.boundV` accepts. -/
theorem Cond.boundV_of_boundConf (c : Semantics) (val : Srt → Bool) :
    ∀ (p : Cond) (n : Nat), Cond.boundConf c n p = true → Cond.boundV c val n p = true
  | .top, _, _ | .bot, _, _ | .ceil .., _, _ | .equals .., _, _ | .mem .., _, _ => by simp [Cond.boundV]
  | .not p, n, h => by
    rw [Cond.boundConf] at h; rw [Cond.boundV]; exact Cond.boundV_of_boundConf c val p n h
  | .and p q, n, h | .or p q, n, h | .implies p q, n, h => by
    rw [Cond.boundConf, Bool.and_eq_true] at h; rw [Cond.boundV, Bool.and_eq_true]
    exact ⟨Cond.boundV_of_boundConf c val p n h.1, Cond.boundV_of_boundConf c val q n h.2⟩
  | .exMatch ys s p t body, n, h => by
    rw [Cond.boundConf, Bool.and_eq_true] at h; rw [Cond.boundV, Bool.and_eq_true]
    exact ⟨h.1, Cond.boundV_of_boundConf c val body _ h.2⟩
  | .ex s body, n, h => by
    rw [Cond.boundConf, Bool.and_eq_true] at h; rw [Cond.boundV, Bool.and_eq_true, Bool.or_eq_true]
    exact ⟨.inl h.1, Cond.boundV_of_boundConf c val body _ h.2⟩
  | .all s body, n, h => by
    rw [Cond.boundConf, Bool.and_eq_true] at h; rw [Cond.boundV, Bool.and_eq_true]
    exact ⟨h.1, Cond.boundV_of_boundConf c val body _ h.2⟩

/-- Where `val` admits no sort, `Cond.boundV` is `Cond.boundConf`. -/
theorem Cond.boundV_false (c : Semantics) :
    ∀ (p : Cond) (n : Nat), Cond.boundV c (fun _ => false) n p = Cond.boundConf c n p
  | .top, _ | .bot, _ | .ceil .., _ | .equals .., _ | .mem .., _ => by simp [Cond.boundV, Cond.boundConf]
  | .not p, n => by rw [Cond.boundV, Cond.boundConf, Cond.boundV_false c p n]
  | .and p q, n | .or p q, n | .implies p q, n => by
    rw [Cond.boundV, Cond.boundConf, Cond.boundV_false c p n, Cond.boundV_false c q n]
  | .exMatch ys s p t body, n => by rw [Cond.boundV, Cond.boundConf, Cond.boundV_false c body _]
  | .ex s body, n => by
    rw [Cond.boundV, Cond.boundConf, Cond.boundV_false c body _]; simp
  | .all s body, n => by rw [Cond.boundV, Cond.boundConf, Cond.boundV_false c body _]

/-- A condition `Cond.boundConf` accepts, `Cond.bound` accepts. -/
theorem Cond.bound_of_boundConf (c : Semantics) (p : Cond) (n : Nat)
    (h : Cond.boundConf c n p = true) : Cond.bound c n p = true := by
  rw [Cond.bound_eq_boundV]; exact Cond.boundV_of_boundConf c c.hasValue p n h

/-- **A condition `Cond.bound` accepts, `Cond.boundV c c.hasValue` accepts**: the Bool the Holds
lemma reads in a model of `Γc` (`CE.holds_den_fixed`, with `hasValue_value`) bounds every
condition `Cond.bound` bounds. -/
theorem Cond.boundV_hasValue_of_bound (c : Semantics) (p : Cond) (n : Nat)
    (h : Cond.bound c n p = true) : Cond.boundV c c.hasValue n p = true := by
  rw [← Cond.bound_eq_boundV]; exact h

/-- `fixesBy` admits more where `ok` admits more. -/
theorem fixesBy_mono {ok ok' : Nat → Bool} (hok : ∀ j, ok j = true → ok' j = true) {i : Nat} {t u : Term}
    (h : fixesBy ok i t u = true) : fixesBy ok' i t u = true := by
  simp only [fixesBy, Bool.and_eq_true, List.all_eq_true] at h ⊢
  exact ⟨h.1, fun j hj => hok j (h.2 j hj)⟩

/-- **`Cond.fixes` admits more where `val` and `ok` admit more.** -/
theorem Cond.fixes_mono {adm val val' : Srt → Bool} (hv : ∀ s, val s = true → val' s = true) :
    ∀ (p : Cond) (ok ok' : Nat → Bool), (∀ j, ok j = true → ok' j = true) → ∀ (i n : Nat),
      Cond.fixes adm val ok i n p = true → Cond.fixes adm val' ok' i n p = true
  | .mem _ t u, ok, ok', hok, i, n, h => by
    rw [Cond.fixes] at h ⊢; exact fixesBy_mono hok h
  | .equals _ t u, ok, ok', hok, i, n, h => by
    rw [Cond.fixes, Bool.or_eq_true] at h ⊢
    exact h.imp (fixesBy_mono hok) (fixesBy_mono hok)
  | .and p q, ok, ok', hok, i, n, h => by
    rw [Cond.fixes, Bool.or_eq_true] at h ⊢
    exact h.imp (Cond.fixes_mono hv p ok ok' hok i n) (Cond.fixes_mono hv q ok ok' hok i n)
  | .or p q, ok, ok', hok, i, n, h => by
    rw [Cond.fixes, Bool.and_eq_true] at h ⊢
    exact ⟨Cond.fixes_mono hv p ok ok' hok i n h.1, Cond.fixes_mono hv q ok ok' hok i n h.2⟩
  | .ex s body, ok, ok', hok, i, n, h => by
    rw [Cond.fixes] at h ⊢
    refine Cond.fixes_mono hv body _ _ (fun j hj => ?_) i (n + 1) h
    by_cases hjn : j = n
    · subst hjn
      simp only [beq_self_eq_true, ite_true, Bool.or_eq_true, Bool.and_eq_true] at hj ⊢
      refine hj.imp id fun h2 => ⟨hv s h2.1, Cond.fixes_mono hv body _ _ (fun k hk => ?_) _ _ h2.2⟩
      simp only [Bool.and_eq_true] at hk ⊢
      exact ⟨hk.1, hok k hk.2⟩
    · have hjn' : (j == n) = false := beq_eq_false_iff_ne.mpr hjn
      simp only [hjn', Bool.false_eq_true, ite_false] at hj ⊢
      exact hok j hj
  | .top, _, _, _, _, _, h | .bot, _, _, _, _, _, h | .ceil .., _, _, _, _, _, h
  | .not _, _, _, _, _, _, h | .implies .., _, _, _, _, _, h | .all .., _, _, _, _, _, h
  | .exMatch .., _, _, _, _, _, h => by simp [Cond.fixes] at h

/-- **`Cond.boundV` accepts more where `val` admits more.** -/
theorem Cond.boundV_mono (c : Semantics) {val val' : Srt → Bool} (hv : ∀ s, val s = true → val' s = true) :
    ∀ (p : Cond) (n : Nat), Cond.boundV c val n p = true → Cond.boundV c val' n p = true
  | .top, _, h | .bot, _, h | .ceil .., _, h | .equals .., _, h | .mem .., _, h => by
    simp [Cond.boundV] at h ⊢
  | .not p, n, h => by rw [Cond.boundV] at h ⊢; exact Cond.boundV_mono c hv p n h
  | .and p q, n, h | .or p q, n, h | .implies p q, n, h => by
    rw [Cond.boundV, Bool.and_eq_true] at h ⊢
    exact ⟨Cond.boundV_mono c hv p n h.1, Cond.boundV_mono c hv q n h.2⟩
  | .exMatch ys s p t body, n, h => by
    rw [Cond.boundV, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, Cond.boundV_mono c hv body _ h.2⟩
  | .ex s body, n, h => by
    rw [Cond.boundV, Bool.and_eq_true, Bool.or_eq_true, Bool.and_eq_true] at h ⊢
    exact ⟨h.1.imp id fun h2 => ⟨hv s h2.1, Cond.fixes_mono hv body _ _ (fun _ hj => hj) n (n + 1) h2.2⟩,
      Cond.boundV_mono c hv body _ h.2⟩
  | .all s body, n, h => by
    rw [Cond.boundV, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, Cond.boundV_mono c hv body _ h.2⟩

/-- **Every condition `Cond.boundV c c.valued` accepts, `Cond.bound` accepts**: `Semantics.hasValue`
accepts every sort `Semantics.valued` accepts. -/
theorem Cond.bound_of_boundV_valued (c : Semantics) (p : Cond) (n : Nat)
    (h : Cond.boundV c c.valued n p = true) : Cond.bound c n p = true := by
  rw [Cond.bound_eq_boundV]
  exact Cond.boundV_mono c (fun _ => Semantics.hasValue_of_valued) p n h

/-- **`Clause.fixedExs` holds more where `val` admits more.** -/
theorem Clause.fixedExs_mono {adm val val' : Srt → Bool} (hv : ∀ s, val s = true → val' s = true)
    (cl : Clause) {i : Nat} (h : i ∈ cl.fixedExs adm val) : i ∈ cl.fixedExs adm val' := by
  unfold Clause.fixedExs at h ⊢
  suffices key : ∀ (l : List Nat) (acc acc' : List Nat), (∀ j ∈ acc, j ∈ acc') →
      ∀ j ∈ l.foldl (fun acc _ => cl.exs.filter fun i => acc.contains i ||
          Cond.fixes adm val (fun j => !cl.exs.contains j || acc.contains j ||
            (j != i && (cl.vars[j]?.map adm).getD false)) i cl.vars.length cl.post) acc,
        j ∈ l.foldl (fun acc _ => cl.exs.filter fun i => acc.contains i ||
          Cond.fixes adm val' (fun j => !cl.exs.contains j || acc.contains j ||
            (j != i && (cl.vars[j]?.map adm).getD false)) i cl.vars.length cl.post) acc' from
    key _ [] [] (fun _ h => h) i h
  intro l
  induction l with
  | nil => exact fun acc acc' hacc => hacc
  | cons _ l ih =>
    intro acc acc' hacc
    refine ih _ _ fun j hj => ?_
    rw [List.mem_filter] at hj ⊢
    refine ⟨hj.1, ?_⟩
    have hj2 := hj.2
    rw [Bool.or_eq_true] at hj2 ⊢
    refine hj2.imp (fun hc => List.contains_iff_mem.mpr (hacc j (List.contains_iff_mem.mp hc))) fun hf => ?_
    refine Cond.fixes_mono hv cl.post _ _ (fun k hk => ?_) j cl.vars.length hf
    simp only [Bool.or_eq_true] at hk ⊢
    exact hk.imp (fun h1 => h1.imp id fun h2 => List.contains_iff_mem.mpr (hacc k (List.contains_iff_mem.mp h2))) id

/-- **Every clause `Semantics.clausePlainEx` accepts with `Semantics.valued` in place of
`Semantics.hasValue`, it accepts.** -/
theorem Semantics.clausePlainEx_of_valued (c : Semantics) (cl : Clause)
    (h : ((!cl.exs.isEmpty || cl.post.isTop) &&
      cl.exs.all (fun i => (cl.vars[i]?.map c.confined).getD false ||
        (cl.fixedExs c.confined c.valued).contains i)) = true) :
    c.clausePlainEx cl = true := by
  simp only [Semantics.clausePlainEx, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    List.contains_iff_mem] at h ⊢
  exact ⟨h.1, fun i hi => (h.2 i hi).imp id (Clause.fixedExs_mono (fun _ => Semantics.hasValue_of_valued) cl)⟩

end KCore
