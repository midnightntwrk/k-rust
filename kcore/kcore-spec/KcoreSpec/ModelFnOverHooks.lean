/-
  KCore. `listsOffB` does not read the interpretation of the hooks.

  The items `listsOffB` checks (the signature, the constructors, the functions' equations, the
  rules, the step's closure, the collections and Bool's closure) and `f`'s own items are built from
  the semantics' data and its translation of terms, which reads no hook's interpretation; so
  `listsOffB (c.withHooks H) f n` is `listsOffB c f n`, by unfolding, checked by the kernel.
-/
import KcoreSpec.ModelFnOverNames
import KcoreSpec.DataCmd

set_option autoImplicit false

namespace KCore

namespace Faithful

namespace Model

-- `listsOffB` under every interpretation of the hooks is `listsOffB` of the semantics.
kernel_rfl listsOffB_withHooks : ∀ (c : Semantics) (H : HookParams) (f : Sym) (n : String),
  listsOffB (c.withHooks H) f n = listsOffB c f n

/-- `ListsOff` under every interpretation of the hooks, from `listsOffB` of the semantics. -/
theorem listsOff_withHooks {c : Semantics} (H : HookParams) {f : Sym} {n : String}
    (h : listsOffB c f n = true) : ListsOff (c.withHooks H) f n :=
  listsOff_of_decided (by rw [listsOffB_withHooks]; exact h)

end Model

end Faithful

end KCore
