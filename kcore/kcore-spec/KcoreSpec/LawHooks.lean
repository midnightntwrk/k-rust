/-
  KCore. `lawHooks c H`: an interpretation of the parameters that satisfies the laws the text
  writes for its open generators (`OpenLaws`): the free one at an open generator with one law, the
  first-occurrence form at one with both (below). It is H at
  every parameter that is no open generator; at an open generator f (a `raw` parameter) it gives
  the application of f itself, read up to the laws the text writes for f: where f is associative
  (`assoc`) the arguments are flattened (an argument that applies f is replaced by its own
  arguments) and the result is nested to the right; where f is idempotent (`idem`) alone, equal
  adjacent arguments are merged, and an application left with one argument is that argument; where f
  is both, each flattened argument is kept at its first occurrence only (`Band.nf`) and the result
  nested to the right, a single argument being that argument.

  It is the witness that the interpretations satisfying `OpenLaws` are not empty, not the meaning of
  the generator: the text says nothing of an open generator beyond its laws. With one law it is the
  free interpretation of that law; with both it is not (`x | y | x` and `x | y` are one value, which
  the two laws do not state), but it adds no commutativity (`x | y` and `y | x` are two values).
  Merging equal adjacent arguments would not do with both laws: `(x | y) | (x | y)` flattens to
  `x y x y`, which has no equal neighbours, while idempotence makes it `x | y`; the first-occurrence
  form makes it `x y` at every word (`Band.nf_idem`), and its form does not depend on the grouping
  (`Band.nf_left`, `Band.nf_right`).

  The list lemmas its theorems rest on: flattening a right nesting gives the flattened parts
  (`lawFlat_lawNest`), so flattening is idempotent (`lawFlat_lawNest_lawFlat`); a nesting of the
  flattening of a right nesting of atoms is that nesting (`lawNest_lawFlat`); the merge of equal
  adjacent elements is idempotent (`lawMerge_idem`).
-/
import KcoreSpec.Obligations
import KcoreSpec.Band
import KcoreSpec.Collections

set_option autoImplicit false

namespace KCore

/-- The arguments of `t` read through the associative symbol f: the leaves of the binary f-nodes
at its top, left to right. A term that applies no f at its top is its own one leaf. -/
def lawFlat (f : Sym) : GroundTerm → List GroundTerm
  | .ctor g [a, b] => if g == f then lawFlat f a ++ lawFlat f b else [.ctor g [a, b]]
  | t => [t]

/-- The right nesting of a list of terms under the binary symbol f: `f(t₁, f(t₂, … tₙ))`, a single
term itself; the empty list (no argument list of a binary symbol) is `f()`. -/
def lawNest (f : Sym) : List GroundTerm → GroundTerm
  | [] => .ctor f []
  | [t] => t
  | t :: ts => .ctor f [t, lawNest f ts]

/-- Equal adjacent elements merged into one. -/
def lawMerge : List GroundTerm → List GroundTerm
  | [] => []
  | [t] => [t]
  | t :: u :: ts => if Exec.same t u then lawMerge (u :: ts) else t :: lawMerge (u :: ts)

/-- The value of the open generator k at the arguments `vs`: the arguments flattened where `assoc`;
where `assoc` and `idem`, each kept at its first occurrence (`Band.nf`); where `idem` alone, equal
adjacent ones merged; nested to the right where `assoc`; an application merged to one argument is
that argument; otherwise the application itself. -/
def lawApp (k : ParamSig) (vs : List GroundTerm) : GroundTerm :=
  let f := k.sig.name
  let xs := if k.assoc then vs.flatMap (lawFlat f) else vs
  let ys := if k.assoc && k.idem then Band.nf xs else if k.idem then lawMerge xs else xs
  if k.assoc then lawNest f ys
  else if k.idem then (match ys with
    | [y] => y
    | _ => .ctor f ys)
  else .ctor f vs

/-- **`lawHooks c H`**: H everywhere except at the open generators of c (its `raw` parameters),
where it is `lawApp`: the right-nested application of the flattened arguments where `assoc`, each
at its first occurrence where also `idem`, equal adjacent arguments merged where `idem` alone. -/
def lawHooks (c : Semantics) (H : HookParams) : HookParams :=
  ⟨fun f vs => match c.params.find? (fun k => k.raw && k.sig.name == f) with
    | some k => some (lawApp k vs)
    | none => H.app f vs⟩

/-! ## The list lemmas -/

/-- A term is never flattened to nothing. -/
theorem lawFlat_ne_nil (f : Sym) : ∀ t, lawFlat f t ≠ []
  | .ctor g [a, b] => by
    unfold lawFlat
    split
    · intro h; exact lawFlat_ne_nil f a (List.append_eq_nil_iff.mp h).1
    · exact List.cons_ne_nil _ _
  | .ctor _ [] | .ctor _ [_] | .ctor _ (_ :: _ :: _ :: _) | .inj _ _ _ | .dv _ _ | .map _ _ | .set _ _
  | .list _ _ => by simp [lawFlat]

/-- Each leaf of a flattening is its own one leaf. -/
theorem lawFlat_leaf (f : Sym) : ∀ t, ∀ x ∈ lawFlat f t, lawFlat f x = [x]
  | .ctor g [a, b], x, hx => by
    unfold lawFlat at hx
    split at hx
    · rcases List.mem_append.mp hx with h | h
      · exact lawFlat_leaf f a x h
      · exact lawFlat_leaf f b x h
    · rename_i hg
      rw [List.mem_singleton] at hx; subst hx
      simp [lawFlat, hg]
  | .ctor _ [], x, hx | .ctor _ [_], x, hx | .ctor _ (_ :: _ :: _ :: _), x, hx | .inj _ _ _, x, hx
  | .dv _ _, x, hx | .map _ _, x, hx | .set _ _, x, hx | .list _ _, x, hx => by
    simp only [lawFlat, List.mem_singleton] at hx; subst hx; simp [lawFlat]

/-- **Flattening a nesting** gives the flattened parts, at a nonempty list. -/
theorem lawFlat_lawNest (f : Sym) : ∀ ts : List GroundTerm, ts ≠ [] →
    lawFlat f (lawNest f ts) = ts.flatMap (lawFlat f)
  | [], h => absurd rfl h
  | [t], _ => by simp [lawNest]
  | t :: u :: ts, _ => by
    rw [show lawNest f (t :: u :: ts) = .ctor f [t, lawNest f (u :: ts)] from rfl]
    simp only [lawFlat, beq_self_eq_true, ↓reduceIte]
    rw [lawFlat_lawNest f (u :: ts) (List.cons_ne_nil _ _)]
    simp [List.flatMap_cons]

/-- Flattening the nesting of a flattening gives the flattening back. -/
theorem lawFlat_lawNest_lawFlat (f : Sym) (t : GroundTerm) :
    lawFlat f (lawNest f (lawFlat f t)) = lawFlat f t := by
  rw [lawFlat_lawNest f _ (lawFlat_ne_nil f t)]
  have : ∀ xs : List GroundTerm, (∀ x ∈ xs, lawFlat f x = [x]) → xs.flatMap (lawFlat f) = xs := by
    intro xs h
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      rw [List.flatMap_cons, h x (List.mem_cons_self ..), ih fun y hy => h y (List.mem_cons_of_mem _ hy)]
      rfl
  exact this _ (lawFlat_leaf f t)

/-- **The nesting of a flattening**: the right nesting of a nonempty list of leaves (terms that are
their own one leaf) flattens to that list, so nesting its flattening gives it back. -/
theorem lawNest_lawFlat (f : Sym) (ts : List GroundTerm) (hne : ts ≠ [])
    (hl : ∀ t ∈ ts, lawFlat f t = [t]) : lawNest f (lawFlat f (lawNest f ts)) = lawNest f ts := by
  rw [lawFlat_lawNest f ts hne]
  congr 1
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rw [List.flatMap_cons, hl t (List.mem_cons_self ..)]
    cases ts with
    | nil => rfl
    | cons u us =>
      rw [ih (List.cons_ne_nil _ _) fun x hx => hl x (List.mem_cons_of_mem _ hx)]
      rfl

/-- The merge keeps the first element. -/
theorem lawMerge_head : ∀ (t : GroundTerm) (ts : List GroundTerm), ∃ rest, lawMerge (t :: ts) = t :: rest
  | t, [] => ⟨[], rfl⟩
  | t, u :: ts => by
    obtain ⟨rest, hr⟩ := lawMerge_head u ts
    unfold lawMerge
    split
    · rename_i h
      rw [Exec.same_iff] at h; subst h
      exact ⟨rest, hr⟩
    · exact ⟨_, rfl⟩

/-- After the merge no two adjacent elements are equal. -/
def lawNoAdj : List GroundTerm → Prop
  | t :: u :: ts => Exec.same t u = false ∧ lawNoAdj (u :: ts)
  | _ => True

theorem lawMerge_noAdj : ∀ ts : List GroundTerm, lawNoAdj (lawMerge ts)
  | [] => trivial
  | [_] => trivial
  | t :: u :: ts => by
    have ih := lawMerge_noAdj (u :: ts)
    unfold lawMerge
    split
    · exact ih
    · rename_i h
      obtain ⟨rest, hr⟩ := lawMerge_head u ts
      rw [hr] at ih ⊢
      exact ⟨by simpa using h, ih⟩

/-- A list with no two equal adjacent elements is its own merge. -/
theorem lawMerge_of_noAdj : ∀ ts : List GroundTerm, lawNoAdj ts → lawMerge ts = ts
  | [], _ => rfl
  | [_], _ => rfl
  | t :: u :: ts, ⟨h, hr⟩ => by
    unfold lawMerge
    rw [h]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [lawMerge_of_noAdj (u :: ts) hr]

/-- **The merge is idempotent.** -/
theorem lawMerge_idem (ts : List GroundTerm) : lawMerge (lawMerge ts) = lawMerge ts :=
  lawMerge_of_noAdj _ (lawMerge_noAdj ts)

/-! ## The interpretation -/

/-- `lawHooks` is H off the open generators. -/
theorem lawHooks_app_of_find_none {c : Semantics} {H : HookParams} {f : Sym} {vs : List GroundTerm}
    (h : c.params.find? (fun k => k.raw && k.sig.name == f) = none) : (lawHooks c H).app f vs = H.app f vs := by
  simp [lawHooks, h]

/-- At an open generator, `lawHooks` gives the free application of its laws. -/
theorem lawHooks_app_of_find {c : Semantics} {H : HookParams} {f : Sym} {vs : List GroundTerm} {k : ParamSig}
    (h : c.params.find? (fun k => k.raw && k.sig.name == f) = some k) :
    (lawHooks c H).app f vs = some (lawApp k vs) := by
  simp [lawHooks, h]

end KCore
