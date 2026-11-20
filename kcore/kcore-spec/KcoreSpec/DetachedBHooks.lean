/-
  `detachedB` reads no interpretation of the parameter symbols: each of its conjuncts (`sortsB`,
  `listsB`, `valuesB`, `graphsB`, the library collections' axioms) reads the sorts, the symbols,
  the signatures, the collections and the item lists of the theory (the signature's, the
  constructors', the functions', the rules', the step's closure, `boolClosed`), and none of those
  reads `Semantics.hooks`, the one field `Semantics.withHooks` replaces. So `detachedB` at
  `c.withHooks H` is `detachedB c` (`detachedB_withHooks`, the kernel's definitional equality at a
  variable `c`), and the decision made on a text's parsed semantics gives the registry family's
  conservativity at `c.withHooks H` for every H (`registry_withHooks_of_decided`).
-/
import KcoreSpec.DataCmd
import KcoreSpec.Obligations
import KcoreSpec.FnObligations
import KcoreSpec.ConsConservative

set_option autoImplicit false

namespace KCore

/- `detachedB` does not read the interpretation of the parameter symbols. -/
kernel_rfl detachedB_withHooks : ∀ (c : Semantics) (H : HookParams) (ss : List Srt) (ks : List Sym),
  detachedB (c.withHooks H) ss ks = detachedB c ss ks

/-- **The registry family is conservative for every H, from the decision at `c`**: where
`detachedB c ss ks` holds, at the names of `ss` and `ks` under `c.withHooks H` the names are
detached, the family is conservative (`registry_conservative`) and no step at values rests on it
(`exact_own`). -/
theorem registry_withHooks_of_decided (c : Semantics) (H : HookParams) (ss : List Srt) (ks : List Sym)
    (hok : c.coreOK = true) (hpre : c.clausesPreTop = true) (hf : FnHyp (c.withHooks H))
    (hd : detachedB c ss ks = true) :
    Detached (c.withHooks H) (DetachedB.names (c.withHooks H) ss ks) ∧
    RegistryConservative (c.withHooks H) (DetachedB.names (c.withHooks H) ss ks) ∧
    ExactOwn (c.withHooks H) (DetachedB.names (c.withHooks H) ss ks) :=
  have h := (Semantics.coreOK_withHooks c H).trans hok
  have hp := (Semantics.clausesPreTop_withHooks c H).trans hpre
  have hd' := (detachedB_withHooks c H ss ks).trans hd
  ⟨detached_of_decided _ ss ks h hd', registry_conservative _ hp ss ks h hf hd', exact_own _ hp ss ks h hf hd'⟩

end KCore
