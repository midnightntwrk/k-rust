# shellcheck shell=bash
# The invariants area: kind 1 invariant libraries (kimpinv, kimpkeys, kimpkeys-hand, kimpfold,
# kimptop, kimpboth, nested, and SIMPLE's simpleinv, simplestore, simplet), KRS IMP's sidecar invariant, the
# negative check, the kind 2 demos (ImpWrites, KrsImpTyping, SimpleEnv) and template. Registry:
# invariants.py.

kore_invariants() {
  case $1 in
    kimp-inv) f=$DEMOS/k/kimp-inv/imp-inv.k m=IMP-INV s=IMP-SYNTAX inc=$KIMP ;;
    kimp-keys) f=$DEMOS/k/kimp-keys/imp-keys.k m=IMP-KEYS s=IMP-SYNTAX inc=$KIMP ;;
    kimp-both) f=$DEMOS/k/kimp-inv/imp-both.k m=IMP-BOTH s=IMP-SYNTAX inc=$KIMP ;;
    simple-inv) f=$DEMOS/k/simple-inv/simple-inv.k m=SIMPLE-INV s=SIMPLE-UNTYPED-SYNTAX inc=$SD ;;
    *) return 1 ;;
  esac
}

name_invariants() {
  case $1 in
    kimpinv|kimpfold|kimptop|kimpboth) echo KImpInv ;; kimpkeys|kimpkeys-hand) echo KImpKeys ;; nested) echo KNested ;;
    simpleinv|simplestore|simplet) echo KSimpleInv ;;
    *) return 1 ;;
  esac
}

gen_invariants() {
  case $1 in
    kimpinv) GEN_ARGS=(--kore "$(kore_dir kimp-inv)/definition.kore" --runtime "$(kore_dir kimp-inv)/runtime.json"
            --out "$o" --name KImpInv --prelude ../../lean/prelude --open-obligations "$o/open-obligations.txt"
            --invariant envOk@env --invariant storeNoIds@env) ;;
    # kimp with the K function `envKeysOk` (demos/k/kimp-keys, the walkthrough of
    # docs/invariants.md, §3); kimpkeys-hand is the same library with one case listed in its
    # open-invariant-cases.txt, so that the case is taken from its hand module
    kimpkeys|kimpkeys-hand) GEN_ARGS=(--kore "$(kore_dir kimp-keys)/definition.kore" --runtime "$(kore_dir kimp-keys)/runtime.json"
            --out "$o" --name KImpKeys --prelude ../../lean/prelude --open-obligations "$o/open-obligations.txt"
            --invariant envKeysOk@env) ;;
    # the same definition with the invariant as a fold with a parameter (`allIs(L, B)`), and as a
    # function of the whole configuration (the top-cell form, `topEnvOk`)
    kimpfold) GEN_ARGS=(--kore "$(kore_dir kimp-inv)/definition.kore" --runtime "$(kore_dir kimp-inv)/runtime.json"
            --out "$o" --name KImpInv --prelude ../../lean/prelude --open-obligations "$o/open-obligations.txt"
            --invariant envAll@env) ;;
    kimptop) GEN_ARGS=(--kore "$(kore_dir kimp-inv)/definition.kore" --runtime "$(kore_dir kimp-inv)/runtime.json"
            --out "$o" --name KImpInv --prelude ../../lean/prelude --open-obligations "$o/open-obligations.txt"
            --invariant topEnvOk) ;;
    # the top-cell form whose right-hand side conjoins two partial calls (demos/k/kimp-inv/imp-both.k)
    kimpboth) GEN_ARGS=(--kore "$(kore_dir kimp-both)/definition.kore" --runtime "$(kore_dir kimp-both)/runtime.json"
            --out "$o" --name KImpInv --prelude ../../lean/prelude --open-obligations "$o/open-obligations.txt"
            --invariant topBoth) ;;
    # a cell inside two nested cell maps (tests/fixtures/nested, whose compiled KORE is committed)
    nested) GEN_ARGS=(--kore "$FIXTURES/nested/definition.kore" --runtime "$FIXTURES/nested/runtime.json"
            --out "$o" --name KNested --prelude ../../lean/prelude --open-obligations "$o/open-obligations.txt"
            --invariant even@v) ;;
    # SIMPLE with the K function `holdsOk` (demos/k/simple-inv): a cell predicate of `<holds>`, which
    # is inside the `<thread>` cell map, so it is lifted to "every thread"
    simpleinv) GEN_ARGS=(--kore "$(kore_dir simple-inv)/definition.kore" --runtime "$(kore_dir simple-inv)/runtime.json"
            --out "$o" --name KSimpleInv --prelude ../../lean/prelude --linear-terms
            --open-obligations "$o/open-obligations.txt" --invariant holdsOk@holds) ;;
    # the same definition with "every store value is a Val or undefined", as a function of the `<store>` cell's
    # content and as a function of SIMPLE's top cell `<T>`
    simplestore|simplet) GEN_ARGS=(--kore "$(kore_dir simple-inv)/definition.kore" --runtime "$(kore_dir simple-inv)/runtime.json"
            --out "$o" --name KSimpleInv --prelude ../../lean/prelude --linear-terms
            --open-obligations "$o/open-obligations.txt"
            --invariant "$([ "$1" = simplet ] && echo tStoreOk@T || echo storeOk@store)") ;;
    *) return 1 ;;
  esac
  return 0
}

# libs_gen_ill_typed DIR: KRS IMP with an ill-typed `assign` (krs-imp-ill-typed.py beside libs.sh), with
# the sidecar, into DIR (namespace KrsImp, so its Terms.lean equals krsimp's): the generated proof of the
# declared cell type must fail at `KRS-IMP.assign` (the gate's negative check).
libs_gen_ill_typed() {
  python3 -I "$LIBS_DIR/krs-imp-ill-typed.py" "$KRS/definition.kore" "$1/definition.kore" &&
  "$G" gen --kore "$1/definition.kore" --out "$1" --name KrsImp --prelude ../../lean/prelude \
    --open-obligations "$1/open-obligations.txt" --sidecar "$KRS/k2lean-sidecar.json"
}

# ---------------------------------------------------------------- gate phases (tests/gate.sh)

needs_invariants() {
  if runs lib simpleinv || runs lib simplestore || runs lib simplet; then
    [ -d "$SD" ] || need "SIMPLE's sources at $SD (set GATE_K_CHECKOUT)"
  fi
  return 0
}

# kind 1 invariants: `{ns}/Invariants.lean`. A rule case that `k2l_preserve` does not close becomes
# an open case (`open-from-log` into open-invariant-cases.txt) and the library is regenerated, so
# the case is then taken from the hand module, as for equations.
invcases() { # DIR NAME: build NAME.Invariants, at most three attempts; the last log is build-DIR-inv.log
  local d=$1 n=$2 o=$GEN/$1 k
  for k in 1 2 3; do
    if lbuild "$o" "build-$d-inv-$k" "$n.Invariants"; then
      cp "$L/build-$d-inv-$k.log" "$L/build-$d-inv.log"; ok "invariant $d" "$L/build-$d-inv.log"; return 0
    fi
    cp "$L/build-$d-inv-$k.log" "$L/build-$d-inv.log"
    [ "$k" = 3 ] && break
    "$G" open-from-log "$o/$n/Invariants.lean" "$L/build-$d-inv-$k.log" "$o/open-invariant-cases.txt" >> "$L/gen-$d.log" 2>&1
    genlib "$d" >> "$L/gen-$d.log" 2>&1 || { bad "gen $d" "$L/gen-$d.log"; return 1; }
  done
  bad "invariant $d" "$L/build-$d-inv.log"; return 1
}
inv_reset() { # DIR: GATE_RETRY_OPEN also retries the open invariant cases
  [ "${GATE_RETRY_OPEN:-0}" = 1 ] && : > "$GEN/$1/open-invariant-cases.txt"
  return 0
}
inv_lib() { # DIR NAME [keep]: a library built only as far as its invariant needs (its Equations, for
  # the K equations it unfolds, then Invariants.lean; not Adequacy or Determinism); `keep` keeps the
  # tracked open invariant cases under GATE_RETRY_OPEN
  local d=$1 n=$2
  phase "lib $d"
  lib_open "$d"
  [ "${3:-}" = keep ] || inv_reset "$d"
  if genlib "$d"; then
    eqns "$d" "$n" && invcases "$d" "$n"
  else bad "gen $d" "$L/gen-$d.log"; fi
}

negative_ill_typed() {
  phase "negative"
  # KRS IMP with an ill-typed `assign` (tests/krs-imp-ill-typed.py): the sidecar's `Preserved` proof
  # must fail, and name the rule (as the open case and in the build error); measured/negative.toml
  # records what happened
  local NEG=$T/negative/krsimp-ill-typed neg_built=false k last
  mkdir -p "$NEG"
  rm -rf "$NEG/KrsImp"
  [ -d "$NEG/.lake" ] || { [ -d "$GEN/krsimp/.lake" ] && cp -a "$GEN/krsimp/.lake" "$NEG/.lake"; }  # same Terms.lean
  cp "$GEN/krsimp/open-obligations.txt" "$NEG/open-obligations.txt"
  : > "$NEG/open-invariant-cases.txt"
  if libs_gen_ill_typed "$NEG" > "$L/gen-ill-typed.log" 2>&1; then
    ok "gen ill-typed" "$L/gen-ill-typed.log"
    for k in 1 2; do
      if lbuild "$NEG" "build-ill-typed-$k" KrsImp.Invariants; then neg_built=true; break; fi
      [ "$k" = 2 ] && break
      "$G" open-from-log "$NEG/KrsImp/Invariants.lean" "$L/build-ill-typed-$k.log" "$NEG/open-invariant-cases.txt" >> "$L/gen-ill-typed.log" 2>&1
      libs_gen_ill_typed "$NEG" >> "$L/gen-ill-typed.log" 2>&1 || bad "gen ill-typed" "$L/gen-ill-typed.log"
    done
    last=$(ls "$L"/build-ill-typed-*.log | sort | tail -1)
    python3 -I - "$NEG/open-invariant-cases.txt" "$last" "$neg_built" > "$MEAS/negative.toml" <<'PY'
import re, sys
cases, log, built = sys.argv[1], sys.argv[2], sys.argv[3] == "true"
opened = []
for l in open(cases):
    l = l.strip()
    if l and not l.startswith("#"):
        opened.append(l.split(" | ")[0])
errors = [l for l in open(log) if re.match(r"\s*error: ", l)]
named = sorted({n for l in errors for n in re.findall(r"«[^»]*»", l)})
q = lambda s: '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'
print("[krsimp-ill-typed]")
print(f"builds = {'true' if built else 'false'}")
print(f"open = [{', '.join(q(x) for x in sorted(opened))}]")
print(f"error_names = [{', '.join(q(x) for x in named)}]")
print(f"first_error = {q(errors[0].strip()) if errors else q('')}")
PY
    ok "negative ill-typed" "$MEAS/negative.toml"
  else bad "gen ill-typed" "$L/gen-ill-typed.log"; fi
}

kind2_template() {
  # the kind 2 template: the skeleton `k2lean new-invariant` writes for kimp, rewritten on every run
  # (the command never overwrites a file, so the skeleton's files are deleted first; .lake/ and the
  # manifest are kept), built like a demo (demo.Kind2Template)
  phase "kind2 template"
  local K2T=$W/kind2/KImpTpl
  mkdir -p "$K2T"
  find "$K2T" -name .lake -prune -o -name '*.lean' -type f -exec rm -f {} +
  rm -f "$K2T/lean-toolchain"
  if "$G" new-invariant --lib "$GEN/kimp" --out "$K2T" --name KImpTpl > "$L/kind2-new.log" 2>&1; then
    ok "new-invariant kimp" "$L/kind2-new.log"
    if lbuild "$K2T" build-Kind2Template; then ok "build Kind2Template" "$L/build-Kind2Template.log"
    else bad "build Kind2Template" "$L/build-Kind2Template.log"; fi
  else bad "new-invariant kimp" "$L/kind2-new.log"; fi
}

gate_invariants() {
  if runs inv krsimp; then
    phase "invariant krsimp"
    [ -f "$GEN/krsimp/KrsImp/Invariants.lean" ] && { inv_reset krsimp; invcases krsimp KrsImp; }
  fi
  # kimp with the K functions `envOk` and `storeNoIds` (demos/k/kimp-inv/imp-inv.k)
  runs lib kimpinv && kc kimp-inv && inv_lib kimpinv KImpInv
  # kimp with the K function `envKeysOk` (demos/k/kimp-keys): the walkthrough of docs/invariants.md,
  # §3, every case by `k2l_preserve`; then kimpkeys-hand, the same library (so its build starts from
  # kimpkeys') whose tracked open-invariant-cases.txt lists one case, proved in its tracked hand
  # module KImpKeys/InvariantsHand.lean: the kind 1 hand path, and an edit of the hand module is
  # checked by this build, not by the sources check
  runs lib kimpkeys && kc kimp-keys && inv_lib kimpkeys KImpKeys
  if runs lib kimpkeys-hand; then
    seed_lake kimpkeys-hand kimpkeys
    kc kimp-keys && inv_lib kimpkeys-hand KImpKeys keep
  fi
  # the other shapes of kind 1 invariant over kimpinv's definition: a fold with a parameter
  # (kimpfold) and the top-cell form (kimptop); their Terms … Equations are kimpinv's, so each
  # starts from its build
  local d
  for d in kimpfold kimptop; do
    runs lib "$d" || continue
    seed_lake "$d" kimpinv
    kc kimp-inv && inv_lib "$d" KImpInv
  done
  # the top-cell form with two partial calls conjoined (demos/k/kimp-inv/imp-both.k), over
  # kimpinv's definition and one more function, so it starts from kimpinv's build too
  if runs lib kimpboth; then
    seed_lake kimpboth kimpinv
    kc kimp-both && inv_lib kimpboth KImpInv
  fi
  # a cell inside two nested cell maps (tests/fixtures/nested)
  runs lib nested && inv_lib nested KNested
  runs negative krsimp-ill-typed && negative_ill_typed
  # SIMPLE with the K function `holdsOk` (demos/k/simple-inv), as for kimpinv; "every store value
  # is a Val or undefined" as a cell function (simplestore) and as a function of SIMPLE's top cell
  # `<T>` (simplet), over the same definition: they start from simpleinv's build
  runs lib simpleinv && kc simple-inv && inv_lib simpleinv KSimpleInv
  for d in simplestore simplet; do
    runs lib "$d" || continue
    seed_lake "$d" simpleinv
    kc simple-inv && inv_lib "$d" KSimpleInv
  done
  phase "diff invariants"
  diffs kimpinv kimpkeys kimpfold kimptop kimpboth nested simpleinv simplestore simplet
  # kind 2 invariants, built like demos: a walk over <k> (ImpWrites), KRS IMP's declared cell type
  # (KrsImpTyping), a Lean invariant over KSimple's configuration (SimpleEnv, needs SIMPLE)
  phase "demos invariants"
  for d in ImpWrites KrsImpTyping SimpleEnv; do runs demo "$d" && dbuild "$d"; done
  runs demo Kind2Template && kind2_template
}
