# shellcheck shell=bash
# The claims area: `claims` over kimp's specifications (krust kprove verdicts, kc_auto, replays,
# induction skeletons), claims under kimpinv's invariant (`--assume-invariant`), and a claim
# transferred along ImpRel's bisimulation (ImpRelClaims, by hand and `--transfer`). Registry: claims.py.

# ---------------------------------------------------------------- gate phases (tests/gate.sh)

# The area's own definitions: kstrict (demos/claims/specs/strict.k), `+` strict in both arguments,
# so either heats first (a `Step` that is not a function), and cooling rules that match the item
# after the hole; kprio, the fixture `prio` (its compiled KORE, as the fixture libraries of the
# invariants area), tables of equations of several priorities and a decoder of bit patterns over a
# table of registers, with an independently written table.
kore_claims() {
  case $1 in
    kstrict) f=$DEMOS/claims/specs/strict.k m=STRICT s=STRICT-SYNTAX inc=$DEMOS/claims/specs ;;
    *) return 1 ;;
  esac
}

name_claims() {
  case $1 in
    kstrict) echo KStrict ;;
    kprio) echo KPrio ;;
    *) return 1 ;;
  esac
}

gen_claims() {
  case $1 in
    kstrict) GEN_ARGS=(--kore "$(kore_dir kstrict)/definition.kore" --runtime "$(kore_dir kstrict)/runtime.json"
            --out "$o" --name KStrict --prelude ../../lean --open-obligations "$o/open-obligations.txt") ;;
    kprio) GEN_ARGS=(--kore "$FIXTURES/prio/definition.kore" --runtime "$FIXTURES/prio/runtime.json"
            --out "$o" --name KPrio --prelude ../../lean --open-obligations "$o/open-obligations.txt") ;;
    *) return 1 ;;
  esac
}

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
      --out "$out" --name KImpClaims --semantics KImp --semantics-path "$sem" --kclaims-path ../../lean \
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
      # the refutations of the open list's false claims, as the guard checked them (`#k2l_refuted`);
      # Lake wraps a long message, so a line is joined up to the end of its axiom list
      awk '/KImpClaims\.Hand[^ ]* refutes / { s = $0; while (s !~ /\]/ && (getline l) > 0) s = s " " l
             sub(/.*KImpClaims\.Hand/, "KImpClaims.Hand", s); gsub(/ +/, " ", s); print s }' \
        "$L/build-claims-guard.log" > "$MEAS/refuted.txt"
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
        --out "$OUTI" --name KImpInvClaims --semantics KImpInv --semantics-path ../kimpinv --kclaims-path ../../lean \
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
      --kclaims-path ../../lean > "$L/claims-impplus-gen.log" 2>&1; then
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

sumspec_claims() {
  # the K tutorial's own IMP++ proof, lesson_7/tests/proofs/sum-spec.k, read as it is (through
  # demos/claims/specs/tutorial-sum-spec.k, which requires the definition first): the loop over
  # framed <env> and <store> by its circularity, a map equality by bindings at the loop's head and
  # `(N + 1) * N / 2` at its exit; the program by the loop's claim. Heavy: 62 rules a step, 98
  # configurations (the loop 80, the program 18), about 12 minutes
  phase "sumspec claims"
  local OUTP=$GEN/sumspec-claims
  if ! "$KRUST" kcompile "$T/demos/claims/specs/tutorial-sum-spec.k" --main-module SUM-SPEC --definition-module IMP \
      --for-proving --output-directory "$KO/sumspec" --builtin-directory "$BUILTIN" -I "$IMPPP" -w none \
      > "$L/kcompile-sumspec.log" 2>&1; then
    bad "kcompile sumspec" "$L/kcompile-sumspec.log"; return
  fi
  if "$G" claims --kore "$KO/impplus/definition.kore" --spec "$KO/sumspec/definition.kore" \
      --out "$OUTP" --name KSumSpec --semantics KImpPlus --semantics-path ../impplus \
      --kclaims-path ../../lean > "$L/claims-sumspec-gen.log" 2>&1; then
    ok "claims-sumspec gen"
    cp "$OUTP/claims.toml" "$MEAS/claims-sumspec.toml"
    if lbuild "$OUTP" build-claims-sumspec; then
      ok "build claims-sumspec" "$L/build-claims-sumspec.log"
      if lbuild "$OUTP" build-claims-sumspec-guard KSumSpecTest; then
        ok "guard claims-sumspec" "$L/build-claims-sumspec-guard.log"
      else bad "guard claims-sumspec" "$L/build-claims-sumspec-guard.log"; fi
      grep -o 'KSumSpec[^ ]*\.holds depends on axioms: .*' "$L/build-claims-sumspec-guard.log" \
        > "$MEAS/axioms-sumspec.txt" || true
      # (each claim's summary line; a step's message that it left a configuration to a split also
      # names kc_auto)
      grep -E 'kc_auto [^ ]+: [0-9]+ configurations' "$L/build-claims-sumspec.log" > "$MEAS/kc-auto-sumspec.txt" || true
    else bad "build claims-sumspec" "$L/build-claims-sumspec.log"; fi
  else bad "claims-sumspec gen" "$L/claims-sumspec-gen.log"; fi
}

strict_claims() {
  # kstrict's claims (demos/claims/specs/strict-spec.k): with a symbolic rest of `<k>`, the cooling
  # rules' matchers do not reduce, and `kc_auto` steps by the cases of `Step` (`tryRel`)
  phase "strict claims"
  local OUTP=$GEN/strict-claims
  if ! "$KRUST" kcompile "$T/demos/claims/specs/strict-spec.k" --main-module STRICT-SPEC --definition-module STRICT \
      --for-proving --output-directory "$KO/strict-spec" --builtin-directory "$BUILTIN" -I "$T/demos/claims/specs" -w none \
      > "$L/kcompile-strict-spec.log" 2>&1; then
    bad "kcompile strict-spec" "$L/kcompile-strict-spec.log"; return
  fi
  if "$G" claims --kore "$(kore_dir kstrict)/definition.kore" --spec "$KO/strict-spec/definition.kore" \
      --out "$OUTP" --name KStrictClaims --semantics KStrict --semantics-path ../kstrict \
      --kclaims-path ../../lean > "$L/claims-strict-gen.log" 2>&1; then
    ok "claims-strict gen"
    cp "$OUTP/claims.toml" "$MEAS/claims-strict.toml"
    if lbuild "$OUTP" build-claims-strict; then
      ok "build claims-strict" "$L/build-claims-strict.log"
      if lbuild "$OUTP" build-claims-strict-guard KStrictClaimsTest; then
        ok "guard claims-strict" "$L/build-claims-strict-guard.log"
      else bad "guard claims-strict" "$L/build-claims-strict-guard.log"; fi
      grep -o 'KStrictClaims[^ ]*\.holds depends on axioms: .*' "$L/build-claims-strict-guard.log" \
        > "$MEAS/axioms-strict.txt" || true
      grep -E 'kc_auto' "$L/build-claims-strict.log" > "$MEAS/kc-auto-strict.txt" || true
    else bad "build claims-strict" "$L/build-claims-strict.log"; fi
  else bad "claims-strict gen" "$L/claims-strict-gen.log"; fi
}

prio_claims() {
  # kprio's claims (demos/claims/specs/prio-spec.k): the decoder against the independent table at one
  # opcode (a target's witnesses named by partial functions' values), over its family of opcodes (the
  # decoder by its equation whose `requires` holds, the two tables at symbolic fields by cases), and
  # the family with source and destination swapped, false and refuted by hand (prio-open.txt,
  # demos/claims/hand/PrioHand.lean); and four of kprio's equations by the row route alone
  # (demos/claims/hand/PrioRows.lean)
  phase "prio claims"
  local OUTP=$GEN/prio-claims
  if ! "$KRUST" kcompile "$T/demos/claims/specs/prio-spec.k" --main-module PRIO-SPEC --definition-module PRIO \
      --for-proving --output-directory "$KO/prio-spec" --builtin-directory "$BUILTIN" -I "$FIXTURES/prio" -w none \
      > "$L/kcompile-prio-spec.log" 2>&1; then
    bad "kcompile prio-spec" "$L/kcompile-prio-spec.log"; return
  fi
  if "$G" claims --kore "$FIXTURES/prio/definition.kore" --spec "$KO/prio-spec/definition.kore" \
      --out "$OUTP" --name KPrioClaims --semantics KPrio --semantics-path ../kprio \
      --kclaims-path ../../lean --open "$T/demos/claims/prio-open.txt" --hand Hand \
      > "$L/claims-prio-gen.log" 2>&1; then
    ok "claims-prio gen"
    cp "$T/demos/claims/hand/PrioHand.lean" "$OUTP/KPrioClaims/Hand.lean"
    cp "$T/demos/claims/hand/PrioRows.lean" "$OUTP/KPrioClaims/Rows.lean"
    cp "$OUTP/claims.toml" "$MEAS/claims-prio.toml"
    if lbuild "$OUTP" build-claims-prio; then
      ok "build claims-prio" "$L/build-claims-prio.log"
      # the row route alone on kprio's equations, which the other proofs would also close
      if lbuild "$OUTP" build-prio-rows KPrioClaims.Rows; then
        ok "prio rows" "$L/build-prio-rows.log"
      else bad "prio rows" "$L/build-prio-rows.log"; fi
      if lbuild "$OUTP" build-claims-prio-guard KPrioClaimsTest; then
        ok "guard claims-prio" "$L/build-claims-prio-guard.log"
      else bad "guard claims-prio" "$L/build-claims-prio-guard.log"; fi
      grep -o 'KPrioClaims[^ ]*\.holds depends on axioms: .*' "$L/build-claims-prio-guard.log" \
        > "$MEAS/axioms-prio.txt" || true
      grep -E 'kc_auto' "$L/build-claims-prio.log" > "$MEAS/kc-auto-prio.txt" || true
    else bad "build claims-prio" "$L/build-claims-prio.log"; fi
  else bad "claims-prio gen" "$L/claims-prio-gen.log"; fi
}

gate_claims() {
  runs lib kstrict && kc kstrict && lib kstrict KStrict
  runs lib kprio && lib kprio KPrio
  if runs record prio-claims; then
    prio_claims
  fi
  if runs record strict-claims; then
    kc kstrict && strict_claims
    # importing KClaims leaves common names usable (lean/claims/KClaimsTest/Keywords.lean)
    if lbuild "$T/lean" build-kclaims-test KClaimsTest; then ok "KClaims importers" "$L/build-kclaims-test.log"
    else bad "KClaims importers" "$L/build-kclaims-test.log"; fi
  fi
  if runs record impplus-claims; then
    kc impplus && impplus_claims
  fi
  if runs record sumspec-claims; then
    kc impplus && sumspec_claims
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
