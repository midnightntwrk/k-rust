# shellcheck shell=bash
# The noninterference area: `noninterference` (ImpNI: kimp with the security checker
# demos/k/imp-sec.k, library impsec).

kore_noninterference() {
  case $1 in
    imp-sec) f=$DEMOS/k/imp-sec.k m=IMP-SEC s=IMP-SEC-SYNTAX inc=$KIMP ;;
    *) return 1 ;;
  esac
}

name_noninterference() {
  case $1 in
    impsec) echo KImpSec ;;
    *) return 1 ;;
  esac
}

gen_noninterference() {
  case $1 in
    impsec) GEN_ARGS=(--kore "$(kore_dir imp-sec)/definition.kore" --runtime "$(kore_dir imp-sec)/runtime.json"
            --out "$o" --name KImpSec --prelude ../../lean/prelude
            --open-obligations "$o/open-obligations.txt" --extra-fns "lev,sec,conf") ;;
    *) return 1 ;;
  esac
  return 0
}

# ImpNI: `Tr.lean`, kimp to the checker, translating programs (`--roots`)
relate_noninterference() {
  case $1 in
    ImpNI) nb=KImpSec kd=$(kore_dir imp-sec) extra=(--roots "SortStmt,SortExpr") ;;
    *) return 1 ;;
  esac
}

# libs_noninterference NS: the noninterference scaffold of demo NS (ImpNI: kimp, with the checker
# demos/k/imp-sec.k in the hand module NS/Hand.lean; needs libs_relate NS for the translation of
# programs), `NS/NI.lean`, and its report `NS/noninterference.toml`.
libs_noninterference() {
  case $1 in
    ImpNI) "$G" noninterference --kore "$(kore_dir kimp)/definition.kore" --name KImp --ns ImpNI \
        --store-cell env --program-sort SortStmt --params "(G : KImpSec.SortMap)" \
        --secure "secure G" --low-eq "lowEq G" \
        --out "$DEMOS/ImpNI/ImpNI/NI.lean" --report "$DEMOS/ImpNI/noninterference.toml" ;;
    *) echo "libs_noninterference: unknown demo $1" >&2; return 2 ;;
  esac
}
