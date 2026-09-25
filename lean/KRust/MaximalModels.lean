/-
What the maximal-model enumeration of the Z3 sort inference records.

Rust modelled here, with line anchors at ce4084a5:
  crates/k-rust/src/inner/parser/z3_inference.rs
    Grammar::infer_packed_sorts_z3   :157-224   (hard constraints :176-179, seed :180,
                                                 satisfiability :181-195, enumeration :197,
                                                 candidates in a BTreeSet :198-215)
    Grammar::infer_sorts_z3          :367-429   (the unpacked twin: :388-391, :392, :409)
    EncodingBase::sort_value         :532-569
    EncodingBase::order_relation     :571-594
    EncodingBase::decode_sort        :596-620
    Encoding::less_than_eq           :1467-1484
    Encoding::restrict_to_real_sorts :1492-1512
    Encoding::exclude_klabel_parameters :1514-1537
    Encoding::seed_model             :1560-1587
    Encoding::prefer_parameters      :1633-1678
    Encoding::maximal_models         :1680-1799 (outer loop :1695-1797, climb :1716-1772,
                                                 blocking clause :1774-1792)
    Encoding::read_model             :1801-1811
  crates/k-rust/src/definition/partial_order.rs
    PartialOrder::new closure        :119-137
    PartialOrder::less_than_eq       :179-181

The model is written from the Rust above.
Each Z3 answer the Rust reads (the seed, the next unblocked model, each climbing step, the
parameter vector `prefer_parameters` keeps) is a universally quantified argument of the inductive
relations below, so a theorem about `Run` holds for every model sequence Z3 can return.
The statements are partial correctness over complete runs; termination is not modelled.

Hypotheses (each a named argument of the theorems that use it; `lean/README.md` lists the Rust
test behind each):
  * `hP : P.WF`: `less_than_eq(_, _, true)` on model values is reflexive and transitive;
  * `hR : P.RoundTrip`: `sort_value (decode_sort v)` denotes `v` for every value `model.eval`
    returns, so re-encoding a decoded model value gives back the same value;
  * `e : Equivalent P Q`: two encodings define the same `sat`, `le` and `pref`.
No hypothesis restricts how many parameter vectors `prefer_parameters` admits: the Rust applies
every admissible vector (`Problem.candidates`), so its output does not read the one vector a run
records. An earlier version assumed one admissible vector per maximal real projection, and then
that lowering erases the choice; both are false on real input (eight WASM sentences admit
several vectors, and `crates/k-rust/tests/fixtures/sort-inference/parameter-choice.k` has two
that lower to `f{A}` and `f{B}`), so the Rust was changed instead (LT-09).
"Z3 decides" (every check answers Sat with a model of the assertions, or Unsat; `Unknown` is an
error return, :1701-1705, :1766-1770) is the trust base and is not a hypothesis here: a check is
modelled by its answer.
-/

namespace KRust.MaximalModels

/-- The inference problem one call of `maximal_models` solves.

* `A` is the projection of a Z3 model onto the real variables (`real_variables`, :1685-1690);
  `B` is its projection onto the formal parameters (`self.parameters`).
* `le` is `less_than_eq(_, _, true)` read pointwise over the real variables: the climb asserts it
  as `greater` (:1718-1735, :1752) and the blocking clause as `dominated` (:1774-1792).
* `sat a b` is "the hard constraints hold": the formulas asserted at :177-179 (packed) or
  :389-391 (unpacked). No other assertion stays on the solver across iterations except the
  blocking clauses, which the model represents by the list `found`.
* `pref a b` is "`prefer_parameters` may return parameter vector `b` with the real variables
  pinned to `a`" (:1633-1678): `b` satisfies the hard constraints and reaches the maximal
  overload count, then the maximal top-preference count, or both counts are 0 and `b` is the
  climb's own model (:1658-1660, :1667, :1674-1676). How Z3 picks among such `b` is not opened.
  The Rust now defines the admissible vectors in `Encoding::admissible_parameters`
  instead: `b` reaches the maximal overload count, its set of live readings (ambiguity
  alternatives up to bracket erasure) is maximal under inclusion among
  those vectors, and it reaches the maximal top-preference count among the vectors with the
  same live set. `pref` stays opaque here, so no statement changes;
  `tests::admissible_parameters_conform_to_brute_force` checks the Rust against that definition.
* `enc a` is what the Rust asserts for a model value `a` it has read: `read_model` decodes each
  value into a `Sort` (:1801-1811, `decode_sort` :596-620), and the climb, the distinctness
  assertion and the blocking clause re-encode it with `sort_value` (:1721-1726, :1739-1744,
  :1777-1782). -/
structure Problem (A B : Type) where
  le : A → A → Prop
  sat : A → B → Prop
  pref : A → B → Prop
  enc : A → A

variable {A B : Type} (P : Problem A B)

/-- Hypothesis `hP`: the order is a preorder.
`le` is `(l, r) ∈ R ∨ l = r` (`less_than_eq`, :1467-1484) with `R` the pairs of real ground sorts
related by the transitively closed `PartialOrder` (`order_relation` :571-594,
`partial_order.rs:119-137`), read pointwise; reading it as a relation on values needs the Z3
datatype to be free (the `hI` of `SubsortEncoding.lean`).
Rust test: `z3_inference.rs` `tests::subsort_order_is_a_preorder_on_model_values`.
Antisymmetry is not needed here; it is needed only for termination, which the statements assume
by quantifying over complete runs. -/
structure Problem.WF : Prop where
  refl : ∀ a, P.le a a
  trans : ∀ a b c, P.le a b → P.le b c → P.le a c

/-- Hypothesis `hR`: re-encoding a decoded model value gives the same value
(`sort_value (decode_sort v)` is `v`, :532-569, :596-620).
Rust test: `z3_inference.rs` `tests::model_values_round_trip`. -/
def Problem.RoundTrip : Prop := ∀ a, P.enc a = a

/-- Some parameter vector completes `a` to a model of the hard constraints. -/
def Problem.SatA (a : A) : Prop := ∃ b, P.sat a b

/-- `a` is excluded by the blocking clause `¬ and_all(dominated)` of a recorded model `m`
(:1774-1792), which asserts `le x (enc m)`. -/
def Problem.Blocked (found : List A) (a : A) : Prop := ∃ m, m ∈ found ∧ P.le a (P.enc m)

/-- `a` is a maximal real projection of the models of the hard constraints. -/
def Problem.IsMax (a : A) : Prop :=
  P.SatA a ∧ ∀ a', P.SatA a' → P.le a a' → a' = a

/-- The inner climbing loop (:1716-1772): with the blocking clauses in force, assert
`le (enc a) x` (`greater`, :1718-1735) and `x ≠ enc a` on some real variable (`distinct`,
:1736-1751); Sat moves to Z3's model (:1754-1761), Unsat stops (:1765). -/
inductive Climb (found : List A) : A → A → Prop
  | stop (a : A) :
      (¬ ∃ a', P.SatA a' ∧ ¬ P.Blocked found a' ∧ P.le (P.enc a) a' ∧ a' ≠ P.enc a) →
      Climb found a a
  | step (a a' c : A) :
      P.SatA a' → ¬ P.Blocked found a' → P.le (P.enc a) a' → a' ≠ P.enc a → Climb found a' c →
      Climb found a c

/-- The outer loop (:1695-1797). `Run found out`: starting with blocking clauses for the real
projections `found`, the loop records `out` in order (`models.push`, :1793). An iteration starts
from the seed (only before any blocking clause, :1696-1697; `seed_model` :1560-1587 returns a
model of the hard constraints) or from the model of an unblocked Sat check (:1699-1712): both are
an unblocked model `a0`. The loop ends when that check is Unsat (:1700), or after one record when
there are no real variables (:1794-1796), where the blocking clause of the record blocks every
`a` by `WF.refl`.
That the Rust loop is one of these runs (model conformance) is a hypothesis about the Rust; its
test is `z3_inference.rs` `tests::maximal_models_conform_to_brute_force_maximum`, which checks the
consequence `maximal_models_spec` against a brute-force maximum. -/
inductive Run : List A → List (A × B) → Prop
  | done (found : List A) :
      (∀ a, P.SatA a → P.Blocked found a) → Run found []
  | next (found : List A) (a0 a : A) (b : B) (out : List (A × B)) :
      P.SatA a0 → ¬ P.Blocked found a0 → Climb P found a0 a → P.pref a b →
      Run (a :: found) out → Run found ((a, b) :: out)

variable {P}

/-- Under `hR`, `Blocked` is `∃ m ∈ found, le a m` (logical equivalence). -/
theorem blocked_iff (hR : P.RoundTrip) {found : List A} {a : A} :
    P.Blocked found a ↔ ∃ m, m ∈ found ∧ P.le a m := by
  constructor
  · rintro ⟨m, hm, hle⟩
    rw [hR m] at hle
    exact ⟨m, hm, hle⟩
  · rintro ⟨m, hm, hle⟩
    refine ⟨m, hm, ?_⟩
    rw [hR m]
    exact hle

/-- A climb from an unblocked model of the hard constraints ends at a maximal, unblocked real
projection. Proves the conjunction of the two properties of the end point (no equality). -/
theorem climb_max (hP : P.WF) (hR : P.RoundTrip) {found : List A} {a0 a : A}
    (h : Climb P found a0 a) (hs : P.SatA a0) (hu : ¬ P.Blocked found a0) :
    P.IsMax a ∧ ¬ P.Blocked found a := by
  induction h with
  | stop a hstop =>
    refine ⟨⟨hs, ?_⟩, hu⟩
    intro a' hs' hle
    apply Classical.byContradiction
    intro hne
    apply hstop
    refine ⟨a', hs', ?_, (hR a).symm ▸ hle, (hR a).symm ▸ hne⟩
    intro hb
    obtain ⟨m, hm, hle'⟩ := (blocked_iff hR).mp hb
    exact hu ((blocked_iff hR).mpr ⟨m, hm, hP.trans _ _ _ hle hle'⟩)
  | step a a' c hs' hu' _ _ _ ih => exact ih hs' hu'

/-- A maximal element below a recorded model of the hard constraints is that model; so a
blocked maximal element is a member of `found` (membership, no equality of lists). -/
theorem blocked_max_mem (hR : P.RoundTrip) {found : List A} {a : A}
    (hfound : ∀ m, m ∈ found → P.SatA m) (ha : P.IsMax a) (hb : P.Blocked found a) :
    a ∈ found := by
  obtain ⟨m, hm, hle⟩ := (blocked_iff hR).mp hb
  have : m = a := ha.2 m (hfound m hm) hle
  exact this ▸ hm

/-- Invariant of the outer loop, for any blocking list of maximal elements: every record is
maximal, unblocked by the earlier `found` and admissible for `prefer_parameters`; every maximal
element is in `found` or recorded; the recorded real projections have no duplicates.
Proves membership statements and `Nodup`, not an equality of lists. -/
theorem run_spec (hP : P.WF) (hR : P.RoundTrip) {found : List A} {out : List (A × B)}
    (h : Run P found out) (hfound : ∀ m, m ∈ found → P.IsMax m) :
    (∀ p, p ∈ out → P.IsMax p.1 ∧ ¬ P.Blocked found p.1 ∧ P.pref p.1 p.2) ∧
    (∀ a, P.IsMax a → a ∈ found ∨ a ∈ out.map Prod.fst) ∧
    (out.map Prod.fst).Nodup := by
  induction h with
  | done found hall =>
    refine ⟨fun p hp => (nomatch hp), ?_, List.nodup_nil⟩
    intro a ha
    exact Or.inl (blocked_max_mem hR (fun m hm => (hfound m hm).1) ha (hall a ha.1))
  | next found a0 a b out hs0 hu0 hclimb hpref _ ih =>
    have ⟨hmax, hunb⟩ := climb_max hP hR hclimb hs0 hu0
    have hfound' : ∀ m, m ∈ a :: found → P.IsMax m := by
      intro m hm
      cases hm with
      | head => exact hmax
      | tail _ hm => exact hfound m hm
    obtain ⟨ihout, ihcov, ihnd⟩ := ih hfound'
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      cases hp with
      | head => exact ⟨hmax, hunb, hpref⟩
      | tail _ hp =>
        obtain ⟨hpm, hpu, hpp⟩ := ihout p hp
        refine ⟨hpm, fun hb => hpu ?_, hpp⟩
        obtain ⟨m, hm, hle⟩ := hb
        exact ⟨m, List.mem_cons_of_mem _ hm, hle⟩
    · intro x hx
      cases ihcov x hx with
      | inl hin =>
        cases hin with
        | head => exact Or.inr (List.mem_cons_self ..)
        | tail _ hin => exact Or.inl hin
      | inr hin => exact Or.inr (List.mem_cons_of_mem _ hin)
    · refine List.nodup_cons.mpr ⟨?_, ihnd⟩
      intro hin
      obtain ⟨p, hp, hpa⟩ := List.mem_map.mp hin
      obtain ⟨_, hpu, _⟩ := ihout p hp
      exact hpu ((blocked_iff hR).mpr ⟨a, List.mem_cons_self .., hpa ▸ hP.refl _⟩)

/-- **Statement 1 (`maximal_models`, :1680-1799).** Every complete run records each maximal real
projection of the hard constraints exactly once and nothing else, and pairs it with a parameter
vector `prefer_parameters` may return.
Equality proved: set equality of the recorded real projections with the maximal ones (as a
membership iff) plus `Nodup`; the recorded order is not claimed. -/
theorem maximal_models_spec (hP : P.WF) (hR : P.RoundTrip) {out : List (A × B)}
    (h : Run P [] out) :
    (∀ a, a ∈ out.map Prod.fst ↔ P.IsMax a) ∧
    (out.map Prod.fst).Nodup ∧
    (∀ p, p ∈ out → P.pref p.1 p.2) := by
  obtain ⟨hout, hcov, hnd⟩ := run_spec hP hR h (fun _ hm => nomatch hm)
  refine ⟨fun a => ⟨?_, ?_⟩, hnd, fun p hp => (hout p hp).2.2⟩
  · intro hin
    obtain ⟨p, hp, hpa⟩ := List.mem_map.mp hin
    exact hpa ▸ (hout p hp).1
  · intro ha
    cases hcov a ha with
    | inl hin => exact nomatch hin
    | inr hin => exact hin

/-- Hypothesis `e`: two problems that differ only in how the formulas are written.
OT-03 replaces each `less_than_eq` by an equivalent formula (`SubsortEncoding.new_equiv`), so the
hard constraints, the climbing order and the preference formulas are pointwise equivalent, and
so are `sat`, `le` and `pref`.
Rust test: `z3_inference.rs` `tests::order_constraints_are_equivalent_at_every_call_site`, which
checks each `less_than_eq` call of a packed inference (hard constraints, preferences, climb,
blocking clause) against the full disjunction. -/
structure Equivalent (P Q : Problem A B) : Prop where
  le : ∀ a a', P.le a a' ↔ Q.le a a'
  sat : ∀ a b, P.sat a b ↔ Q.sat a b
  pref : ∀ a b, P.pref a b ↔ Q.pref a b

/-- Maximality is the same predicate for equivalent problems (logical equivalence). -/
theorem isMax_congr {P Q : Problem A B} (e : Equivalent P Q) (a : A) :
    P.IsMax a ↔ Q.IsMax a := by
  unfold Problem.IsMax Problem.SatA
  constructor
  · rintro ⟨⟨b, hb⟩, hmax⟩
    refine ⟨⟨b, (e.sat a b).mp hb⟩, fun a' ⟨b', hb'⟩ hle => ?_⟩
    exact hmax a' ⟨b', (e.sat a' b').mpr hb'⟩ ((e.le a a').mpr hle)
  · rintro ⟨⟨b, hb⟩, hmax⟩
    refine ⟨⟨b, (e.sat a b).mpr hb⟩, fun a' ⟨b', hb'⟩ hle => ?_⟩
    exact hmax a' ⟨b', (e.sat a' b').mp hb'⟩ ((e.le a a').mp hle)

/-- **Statement 2 (up to parameter choice).** Two complete runs over equivalent encodings, with
any Z3 answers, record the same real projections, and each one's parameter vector for a real
projection lies in the same set `pref a`.
Equality proved: equality of the recorded sets up to the normalization "replace each recorded
`(a, b)` by `(a, pref a)`". -/
theorem runs_agree_up_to_pref {P Q : Problem A B} (hP : P.WF) (hQ : Q.WF)
    (hRP : P.RoundTrip) (hRQ : Q.RoundTrip) (e : Equivalent P Q) {out out' : List (A × B)}
    (h : Run P [] out) (h' : Run Q [] out') :
    (∀ a, a ∈ out.map Prod.fst ↔ a ∈ out'.map Prod.fst) ∧
    (∀ p, p ∈ out → P.pref p.1 p.2) ∧ (∀ p, p ∈ out' → P.pref p.1 p.2) := by
  obtain ⟨hs, _, hp⟩ := maximal_models_spec hP hRP h
  obtain ⟨hs', _, hp'⟩ := maximal_models_spec hQ hRQ h'
  refine ⟨fun a => ?_, hp, fun p hin => (e.pref p.1 p.2).mpr (hp' p hin)⟩
  rw [hs a, hs' a]
  exact isMax_congr e a

/-- The candidate set of a run: `c` is a candidate when some recorded real projection `a` of
`out` and some parameter vector `b` that `prefer_parameters` admits for it (`P.pref a b`) give
`f a b = some c`.
`f a b` is model application as an opaque function, `none` standing for an application error
(`apply_model_packed` and `apply_model`); the Rust collects the applied terms of every admissible
`(a, b)` in one `BTreeSet` and hands that set, as one ambiguity, to the post-inference passes
(`Grammar::lower_inferred`), so the parse is a function of this set.
Rust, with line anchors at cc55d55c:
  crates/k-rust/src/inner/parser/z3_inference.rs
    Grammar::infer_packed_sorts_z3   :245-304 (every admissible model applied :280-295, the set
                                              as one ambiguity :301-302)
    Grammar::infer_sorts_z3          :447-510 (the unpacked twin: :493-508)
    Encoding::maximal_models         :1889-2009 (each recorded typing with its admissible set)
    Encoding::admissible_parameters  :2031-2117 (the enumeration of `pref a ·`; it fails instead of
                                              returning a subset past 256 vectors)
  crates/k-rust/src/inner/parser.rs
    Grammar::lower_inferred          :1179-1186
That `admissible_parameters` returns exactly `{ b | P.pref a b }` for each recorded `a` is a
hypothesis about the Rust (enumeration conformance); its test is `z3_inference.rs`
`tests::admissible_parameters_conform_to_brute_force`. -/
def Problem.candidates {C : Type} (P : Problem A B) (out : List (A × B)) (f : A → B → Option C)
    (c : C) : Prop :=
  ∃ a, a ∈ out.map Prod.fst ∧ ∃ b, P.pref a b ∧ f a b = some c

/-- **Statement 3 (exact, over the admissible sets).** Two complete runs over equivalent
encodings, with any Z3 answers, have the same candidate set, for any model application `f`.
No uniqueness of the admissible parameter vector is assumed: every admissible vector of every
recorded real projection contributes its candidate, so the vector a run happens to record is not
read.
Equality proved: set equality (as a membership iff) of `P.candidates out f` and
`Q.candidates out' f`. -/
theorem runs_agree_candidates {C : Type} (hP : P.WF) {Q : Problem A B} (hQ : Q.WF)
    (hRP : P.RoundTrip) (hRQ : Q.RoundTrip) (e : Equivalent P Q)
    (f : A → B → Option C) {out out' : List (A × B)}
    (h : Run P [] out) (h' : Run Q [] out') :
    ∀ c, P.candidates out f c ↔ Q.candidates out' f c := by
  obtain ⟨hs, _, _⟩ := runs_agree_up_to_pref hP hQ hRP hRQ e h h'
  intro c
  constructor
  · rintro ⟨a, ha, b, hb, hf⟩
    exact ⟨a, (hs a).mp ha, b, (e.pref a b).mp hb, hf⟩
  · rintro ⟨a, ha, b, hb, hf⟩
    exact ⟨a, (hs a).mpr ha, b, (e.pref a b).mpr hb, hf⟩

end KRust.MaximalModels
