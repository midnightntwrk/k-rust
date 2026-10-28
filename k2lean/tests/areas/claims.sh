# shellcheck shell=bash
# The claims area: `claims` over kimp's specifications (krust kprove verdicts, kc_auto, replays,
# induction skeletons), claims under kimpinv's invariant (`--assume-invariant`), and a claim
# transferred along ImpRel's bisimulation (ImpRelClaims, by hand and `--transfer`). Registry: claims.py.

# ---------------------------------------------------------------- gate phases (tests/gate.sh)

needs_claims() {
  if runs record claims; then
    [ -d "$SPECS" ] || need "kimp's claims at $SPECS (set GATE_IMP_CHECKOUT)"
  fi
  return 0
}

kimp_claims() {
  phase "kimp claims"
  local OUT=$GEN/kimp-claims OWN=$T/demos/claims/specs d
  spec() { # FILE MODULE DIR
    "$KRUST" kcompile "$1" --main-module "$2" --definition-module IMP-VERIFICATION --for-proving \
      --output-directory "$KO/$3" --builtin-directory "$BUILTIN" -I "$KIMP" -I "$(dirname "$1")" -w none \
      > "$L/kcompile-$3.log" 2>&1 || bad "kcompile $3" "$L/kcompile-$3.log"
  }
  spec "$SPECS/imp-simple-spec.k" IMP-SIMPLE-SPEC imp-simple-spec
  spec "$SPECS/imp-sum-spec.k" IMP-SUM-SPEC imp-sum-spec
  spec "$OWN/imp-ifs-uint64-spec.k" IMP-IFS-UINT64-SPEC imp-ifs-uint64-spec
  spec "$OWN/imp-two-sum-aux-spec.k" IMP-TWO-SUM-AUX-SPEC imp-two-sum-aux-spec
  spec "$OWN/imp-div0-spec.k" IMP-DIV0-SPEC imp-div0-spec
  # claims that hold only under kimpinv's invariant, by its part `envOk` (demos/k/kimp-inv): over kimp they are
  # false (refuted in demos/claims/hand/Hand.lean), over kimpinv with --assume-invariant they hold
  "$KRUST" kcompile "$OWN/imp-inv-spec.k" --main-module IMP-INV-SPEC --definition-module IMP-INV-VERIFICATION --for-proving \
    --output-directory "$KO/imp-inv-spec" --builtin-directory "$BUILTIN" -I "$KIMP" -I "$D/k/kimp-inv" -w none \
    > "$L/kcompile-imp-inv-spec.log" 2>&1 || bad "kcompile imp-inv-spec" "$L/kcompile-imp-inv-spec.log"
  {
    for d in imp-simple-spec:IMP-SIMPLE-SPEC imp-ifs-uint64-spec:IMP-IFS-UINT64-SPEC imp-two-sum-aux-spec:IMP-TWO-SUM-AUX-SPEC imp-div0-spec:IMP-DIV0-SPEC imp-inv-spec:IMP-INV-SPEC; do
      "$KRUST" kprove --compiled-definition "$KO/${d%%:*}" --main-module "${d##*:}" 2>&1 < /dev/null | grep '^claim' || true
    done
    "$KRUST" kprove --compiled-definition "$KO/imp-sum-spec" --main-module IMP-SUM-SPEC \
      --claim IMP-SUM-SPEC.sum-spec 2>&1 < /dev/null | grep '^claim' || true
    "$KRUST" kprove --compiled-definition "$KO/imp-sum-spec" --main-module IMP-SUM-SPEC \
      --claim IMP-SUM-SPEC.two-sum-spec --depth 300 2>&1 < /dev/null | grep -E '^claim|^  [a-z]' || true
  } > "$MEAS/kprove.txt"
  # kimp-claims over kimp, with the transfer modules of ImpRelClaims and ImpUnrollClaims
  claims_gen() { # OUT SEMANTICS-PATH LOG [ARG…]
    local out=$1 sem=$2 log=$3; shift 3
    "$G" claims --kore "$KO/kimp/definition.kore" \
      --spec "$KO/imp-simple-spec/definition.kore" --spec "$KO/imp-sum-spec/definition.kore" \
      --spec "$KO/imp-ifs-uint64-spec/definition.kore" --spec "$KO/imp-two-sum-aux-spec/definition.kore" --spec "$KO/imp-div0-spec/definition.kore" \
      --spec "$KO/imp-inv-spec/definition.kore" \
      --induction "$T/demos/claims/kimp-expr-eval.toml" --induction "$T/demos/claims/kimp-expr-div.toml" \
      --induction "$T/demos/claims/kimp-expr-vars.toml" \
      --out "$out" --name KImpClaims --semantics KImp --semantics-path "$sem" --kclaims-path ../../lean/claims \
      --open "$T/demos/claims/kimp-open.txt" "$@" \
      --hand Hand --hand Replay.Addition2 --hand Replay.Branching --hand Replay.SumLoop > "$L/$log" 2>&1
  }
  if claims_gen "$OUT" ../kimp claims-gen.log \
      --transfer ImpRel --transfer-target KrsImp --transfer-out "$D/ImpRelClaims/ImpRelClaims/Transfers.lean" \
      --transfer ImpUnroll --transfer-kind stutter --transfer-target KUnroll --transfer-det KUnroll.Determinism \
      --transfer-out "$D/ImpUnrollClaims/ImpUnrollClaims/Transfers.lean"; then
    ok "claims gen"
    cp "$T/demos/claims/hand/Hand.lean" "$OUT/KImpClaims/Hand.lean"
    cp "$OUT/claims.toml" "$MEAS/claims.toml"
    mkdir -p "$OUT/KImpClaims/Replay" "$MEAS/replay"
    "$KRUST" kore-rpc "$KO/imp-simple-spec/definition.kore" --module IMP-SIMPLE-SPEC --server-port 0 \
      > "$L/rpc.log" 2>&1 < /dev/null &
    RPC=$!
    trap 'kill $RPC 2>/dev/null || true' EXIT
    for _ in $(seq 100); do grep -q listening "$L/rpc.log" && break; sleep 0.1; done
    PORT=$(sed -n 's/.*listening on 127.0.0.1:\([0-9]*\).*/\1/p' "$L/rpc.log")
    replay() { # LABEL MODULE-FILE [--cut RULE]
      local label=$1 file=$2; shift 2
      (ulimit -v 4000000; "$G" claims replay --kore "$KO/kimp/definition.kore" \
        --spec "$KO/imp-simple-spec/definition.kore" --claim "IMP-SIMPLE-SPEC.$label" --port "$PORT" \
        --out "$OUT/KImpClaims/Replay/$file.lean" --skeleton "$MEAS/replay/$label.toml" "$@") > "$L/replay-$label.log" 2>&1 \
        && ok "replay $label" || bad "replay $label" "$L/replay-$label.log"
    }
    replay addition-2 Addition2
    replay branching Branching
    replay sum-loop SumLoop --cut IMP.while
    kill $RPC 2>/dev/null; wait $RPC 2>/dev/null; trap - EXIT
    if lbuild "$OUT" build-claims; then
      ok "build claims" "$L/build-claims.log"
      if lbuild "$OUT" build-claims-guard KImpClaimsTest; then ok "guard claims" "$L/build-claims-guard.log"
      else bad "guard claims" "$L/build-claims-guard.log"; fi
      grep -o 'KImpClaims[^ ]*\.holds depends on axioms: .*' "$L/build-claims-guard.log" > "$MEAS/axioms.txt" || true
      grep -o 'KImpClaims.Hand[^ ]* depends on axioms: .*' "$L/build-claims.log" >> "$MEAS/axioms.txt" || true
      grep -E 'kc_auto' "$L/build-claims.log" > "$MEAS/kc-auto-stats.txt" || true
    else bad "build claims" "$L/build-claims.log"; fi
  else bad "claims gen" "$L/claims-gen.log"; fi
}

kimpinv_claims() {
  # claims under a preserved invariant (`--assume-invariant`): the kind 1 invariant of kimpinv
  # (`envOk` and `storeNoIds`, invariants area), whose library is built there only as far as
  # Invariants.lean; the claims need the rest (Rules, Adequacy, Determinism). The invariant's
  # unfolding set is read from the library's invariant-unfold.txt (the default of --invariant-unfold)
  phase "kimpinv claims"
  local OUTI=$GEN/kimpinv-claims
  if lbuild "$GEN/kimpinv" build-kimpinv-full KImpInv; then
    ok "build kimpinv" "$L/build-kimpinv-full.log"
    if "$G" claims --kore "$KO/kimp-inv/definition.kore" --spec "$KO/imp-inv-spec/definition.kore" \
        --out "$OUTI" --name KImpInvClaims --semantics KImpInv --semantics-path ../kimpinv --kclaims-path ../../lean/claims \
        --assume-invariant Invariant > "$L/claims-inv-gen.log" 2>&1; then
      ok "claims-inv gen"
      cp "$OUTI/claims.toml" "$MEAS/claims-inv.toml"
      if lbuild "$OUTI" build-claims-inv; then
        ok "build claims-inv" "$L/build-claims-inv.log"
        if lbuild "$OUTI" build-claims-inv-guard KImpInvClaimsTest; then ok "guard claims-inv" "$L/build-claims-inv-guard.log"
        else bad "guard claims-inv" "$L/build-claims-inv-guard.log"; fi
        grep -o 'KImpInvClaims[^ ]*\.holds depends on axioms: .*' "$L/build-claims-inv-guard.log" >> "$MEAS/axioms.txt" || true
        grep -E 'kc_auto' "$L/build-claims-inv.log" >> "$MEAS/kc-auto-stats.txt" || true
      else bad "build claims-inv" "$L/build-claims-inv.log"; fi
    else bad "claims-inv gen" "$L/claims-inv-gen.log"; fi
  else bad "build kimpinv" "$L/build-kimpinv-full.log"; fi
}

impplus_claims() {
  # IMP++ (the soundness area's library impplus): a `Step` that is not a function (ranked: `join`
  # matches two threads; strict operators heat either argument), explored by every successor
  # (`KClaims.ExecSucc`). The spec is example material (demos/claims/specs/impplus-spec.k)
  phase "impplus claims"
  local OUTP=$GEN/impplus-claims
  if ! "$KRUST" kcompile "$T/demos/claims/specs/impplus-spec.k" --main-module IMPPLUS-SPEC --definition-module IMP \
      --for-proving --output-directory "$KO/impplus-spec" --builtin-directory "$BUILTIN" -I "$IMPPP" -w none \
      > "$L/kcompile-impplus-spec.log" 2>&1; then
    bad "kcompile impplus-spec" "$L/kcompile-impplus-spec.log"; return
  fi
  if "$G" claims --kore "$KO/impplus/definition.kore" --spec "$KO/impplus-spec/definition.kore" \
      --out "$OUTP" --name KImpPlusClaims --semantics KImpPlus --semantics-path ../impplus \
      --kclaims-path ../../lean/claims > "$L/claims-impplus-gen.log" 2>&1; then
    ok "claims-impplus gen"
    cp "$OUTP/claims.toml" "$MEAS/claims-impplus.toml"
    if lbuild "$OUTP" build-claims-impplus; then
      ok "build claims-impplus" "$L/build-claims-impplus.log"
      if lbuild "$OUTP" build-claims-impplus-guard KImpPlusClaimsTest; then
        ok "guard claims-impplus" "$L/build-claims-impplus-guard.log"
      else bad "guard claims-impplus" "$L/build-claims-impplus-guard.log"; fi
      grep -o 'KImpPlusClaims[^ ]*\.holds depends on axioms: .*' "$L/build-claims-impplus-guard.log" \
        > "$MEAS/axioms-impplus.txt" || true
      grep -E 'kc_auto' "$L/build-claims-impplus.log" > "$MEAS/kc-auto-impplus.txt" || true
    else bad "build claims-impplus" "$L/build-claims-impplus.log"; fi
  else bad "claims-impplus gen" "$L/claims-impplus-gen.log"; fi
}

gate_claims() {
  if runs record impplus-claims; then
    kc impplus && impplus_claims
  fi
  if runs record claims; then
    kc kimp && kc kimp-inv
    kimp_claims
    kimpinv_claims
  fi
  # kimp's claims transferred to the KRS IMP port along ImpRel's bisimulation (demos/ImpRelClaims:
  # one by hand, Transfer.lean, and every proved one by `claims --transfer`, Transfers.lean), built
  # like a demo
  if runs demo ImpRelClaims; then
    phase "demo ImpRelClaims"
    dbuild ImpRelClaims
  fi
  # kimp's claims carried to its unrolling variant along ImpUnroll's stuttering bisimulation, each
  # with its own modality since KUnroll's step is deterministic (demos/ImpUnrollClaims, `claims
  # --transfer … --transfer-kind stutter --transfer-det KUnroll.Determinism`)
  if runs demo ImpUnrollClaims; then
    phase "demo ImpUnrollClaims"
    dbuild ImpUnrollClaims
  fi
}
