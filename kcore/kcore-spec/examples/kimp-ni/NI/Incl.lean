/- Kernel fact (examples/run.sh): the checker's core has kimp's signature, through the renaming
   `toSec` (Names.lean). Both import the same builtin library; the renaming keeps every name; and
   kimp's constructors, user sorts and subsorts, renamed, are the checker's. So a value of kimp's
   program sorts, renamed, is a value of the checker's, of the renamed sort. -/
import NI.Spec
namespace NI
open KCore
/-- The renaming keeps names. -/
noncomputable def namesKept : Bool :=
  symMap.all (fun (f, g) => Kimp.c.symName f == ImpSec.c.symName g) &&
    sortMap.all (fun (a, b) => Kimp.c.sortName a == ImpSec.c.sortName b)
/-- kimp's constructors, user sorts and subsorts (those after its configuration's cells', whose
trees differ), renamed, are among the checker's. -/
def sigIncl (c : Semantics) (p : Presentation) (d : Semantics) (q : Presentation) : Bool :=
  (userCtors c p).all (fun k => (userCtors d q).contains ⟨rn symMap k.name, k.args.map (rn sortMap), rn sortMap k.result⟩) &&
    (userSortsOf c p).all (fun s => (userSortsOf d q).contains (rn sortMap s)) &&
    (userSubsortsOf c p).all (fun (a, b) => (userSubsortsOf d q).contains (rn sortMap a, rn sortMap b))
theorem kimp_lib : Kimp.c.lib = ImpSec.c.lib := rfl
theorem kimp_names : namesKept = true := by decide +kernel
theorem kimp_incl : sigIncl Kimp.c Kimp.defn.pres ImpSec.c ImpSec.defn.pres = true := by decide +kernel
end NI
