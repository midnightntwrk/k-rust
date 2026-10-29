# shellcheck shell=bash
# The invariants area: kind 1 invariant libraries (kimpinv, kimpkeys, kimpkeys-hand, kimpfold,
# kimptop, kimpboth, nested, range, walk, kfold, anyfold, drfinv, and SIMPLE's simpleinv, simplestore, simplet, simpleenvs), KRS IMP's sidecar invariant, the
# negative check, the kind 2 demos (ImpWrites, KrsImpTyping, InvBudget) and template. Registry:
# invariants.py.

kore_invariants() {
  case $1 in
    kimp-inv) f=$DEMOS/k/kimp-inv/imp-inv.k m=IMP-INV s=IMP-SYNTAX inc=$KIMP ;;
    kimp-keys) f=$DEMOS/k/kimp-keys/imp-keys.k m=IMP-KEYS s=IMP-SYNTAX inc=$KIMP ;;
    kimp-both) f=$DEMOS/k/kimp-inv/imp-both.k m=IMP-BOTH s=IMP-SYNTAX inc=$KIMP ;;
    simple-inv) f=$DEMOS/k/simple-inv/simple-inv.k m=SIMPLE-INV s=SIMPLE-UNTYPED-SYNTAX inc=$SD ;;
    simple-envs) f=$DEMOS/k/simple-inv/simple-envs.k m=SIMPLE-ENVS s=SIMPLE-UNTYPED-SYNTAX inc=$SD ;;
    *) return 1 ;;
  esac
}

name_invariants() {
  case $1 in
    kimpinv|kimpfold|kimptop|kimpboth) echo KImpInv ;; kimpkeys|kimpkeys-hand) echo KImpKeys ;; nested) echo KNested ;; range) echo KRange ;; walk) echo KWalk ;; kfold) echo KKFold ;; anyfold) echo KAnyFold ;; drfinv) echo Drf ;;
    simpleinv|simplestore|simplet|simpleenvs) echo KSimpleInv ;;
    *) return 1 ;;
  esac
}

gen_invariants() {
  case $1 in
    kimpinv) GEN_ARGS=(--kore "$(kore_dir kimp-inv)/definition.kore" --runtime "$(kore_dir kimp-inv)/runtime.json"
            --out "$o" --name KImpInv --prelude ../../lean --open-obligations "$o/open-obligations.txt"
            --invariant envOk@env --invariant storeNoIds@env) ;;
    # kimp with the K function `envKeysOk` (demos/k/kimp-keys, the walkthrough of
    # docs/invariants.md, §3); kimpkeys-hand is the same library with one case listed in its
    # open-invariant-cases.txt, so that the case is taken from its hand module
    kimpkeys|kimpkeys-hand) GEN_ARGS=(--kore "$(kore_dir kimp-keys)/definition.kore" --runtime "$(kore_dir kimp-keys)/runtime.json"
            --out "$o" --name KImpKeys --prelude ../../lean --open-obligations "$o/open-obligations.txt"
            --invariant envKeysOk@env) ;;
    # the same definition with the invariant as a fold with a parameter (`allIs(L, B)`), and as a
    # function of the whole configuration (the top-cell form, `topEnvOk`)
    kimpfold) GEN_ARGS=(--kore "$(kore_dir kimp-inv)/definition.kore" --runtime "$(kore_dir kimp-inv)/runtime.json"
            --out "$o" --name KImpInv --prelude ../../lean --open-obligations "$o/open-obligations.txt"
            --invariant envAll@env) ;;
    kimptop) GEN_ARGS=(--kore "$(kore_dir kimp-inv)/definition.kore" --runtime "$(kore_dir kimp-inv)/runtime.json"
            --out "$o" --name KImpInv --prelude ../../lean --open-obligations "$o/open-obligations.txt"
            --invariant topEnvOk) ;;
    # the top-cell form whose right-hand side conjoins two partial calls (demos/k/kimp-inv/imp-both.k)
    kimpboth) GEN_ARGS=(--kore "$(kore_dir kimp-both)/definition.kore" --runtime "$(kore_dir kimp-both)/runtime.json"
            --out "$o" --name KImpInv --prelude ../../lean --open-obligations "$o/open-obligations.txt"
            --invariant topBoth) ;;
    # a cell inside two nested cell maps (tests/fixtures/nested, whose compiled KORE is committed)
    nested) GEN_ARGS=(--kore "$FIXTURES/nested/definition.kore" --runtime "$FIXTURES/nested/runtime.json"
            --out "$o" --name KNested --prelude ../../lean --open-obligations "$o/open-obligations.txt"
            --invariant even@v) ;;
    # a fold over `<k>` whose test of one item is a partial function (tests/fixtures/kfold)
    kfold) GEN_ARGS=(--kore "$FIXTURES/kfold/definition.kore" --runtime "$FIXTURES/kfold/runtime.json"
            --out "$o" --name KKFold --prelude ../../lean --open-obligations "$o/open-obligations.txt"
            --invariant ok) ;;
    # `orBool` list folds, read under `notBool` and as they are (tests/fixtures/anyfold)
    anyfold) GEN_ARGS=(--kore "$FIXTURES/anyfold/definition.kore" --runtime "$FIXTURES/anyfold/runtime.json"
            --out "$o" --name KAnyFold --prelude ../../lean --open-obligations "$o/open-obligations.txt"
            --invariant ok) ;;
    # a map extended by a map built by recursion on an `Int` range (tests/fixtures/range)
    range) GEN_ARGS=(--kore "$FIXTURES/range/definition.kore" --runtime "$FIXTURES/range/runtime.json"
            --out "$o" --name KRange --prelude ../../lean --open-obligations "$o/open-obligations.txt"
            --invariant storeNat@store) ;;
    # claims disjoint across a cell map's elements and the program (tests/fixtures/drf's `drfOk`:
    # at most one write to <acc> pending), the K function's preservation with no hand case
    drfinv) GEN_ARGS=(--kore "$FIXTURES/drf/definition.kore" --runtime "$FIXTURES/drf/runtime.json"
            --out "$o" --name Drf --prelude ../../lean --open-obligations "$o/open-obligations.txt"
            --invariant drfOk@T) ;;
    # walks over a cell map and over maps by free-key patterns (tests/fixtures/walk)
    walk) GEN_ARGS=(--kore "$FIXTURES/walk/definition.kore" --runtime "$FIXTURES/walk/runtime.json"
            --out "$o" --name KWalk --prelude ../../lean --open-obligations "$o/open-obligations.txt"
            --invariant envsOk) ;;
    # SIMPLE with the K function `holdsOk` (demos/k/simple-inv): a cell predicate of `<holds>`, which
    # is inside the `<thread>` cell map, so it is lifted to "every thread"
    simpleinv) GEN_ARGS=(--kore "$(kore_dir simple-inv)/definition.kore" --runtime "$(kore_dir simple-inv)/runtime.json"
            --out "$o" --name KSimpleInv --prelude ../../lean
            --open-obligations "$o/open-obligations.txt" --invariant holdsOk@holds) ;;
    # the same definition with "every store value is a Val or undefined", as a function of the `<store>` cell's
    # content and as a function of SIMPLE's top cell `<T>`
    simplestore|simplet) GEN_ARGS=(--kore "$(kore_dir simple-inv)/definition.kore" --runtime "$(kore_dir simple-inv)/runtime.json"
            --out "$o" --name KSimpleInv --prelude ../../lean
            --open-obligations "$o/open-obligations.txt"
            --invariant "$([ "$1" = simplet ] && echo tStoreOk@T || echo storeOk@store)") ;;
    # SIMPLE with `envsOk` (demos/k/simple-inv/simple-envs.k): every environment, of every thread and
    # of every stack frame, maps into the store, through walks, folds over `K` and lists, and their
    # monotonicity in the store
    simpleenvs) GEN_ARGS=(--kore "$(kore_dir simple-envs)/definition.kore" --runtime "$(kore_dir simple-envs)/runtime.json"
            --out "$o" --name KSimpleInv --prelude ../../lean
            --open-obligations "$o/open-obligations.txt" --invariant envsOk@T) ;;
    *) return 1 ;;
  esac
  return 0
}

# libs_gen_ill_typed DIR: KRS IMP with an ill-typed `assign` (krs-imp-ill-typed.py beside libs.sh), with
# the sidecar, into DIR (namespace KrsImp, so its Terms.lean equals krsimp's): the generated proof of the
# declared cell type must fail at `KRS-IMP.assign` (the gate's negative check).
libs_gen_ill_typed() {
  python3 -I "$LIBS_DIR/krs-imp-ill-typed.py" "$KRS/definition.kore" "$1/definition.kore" &&
  "$G" gen --kore "$1/definition.kore" --out "$1" --name KrsImp --prelude ../../lean \
    --open-obligations "$1/open-obligations.txt" --sidecar "$KRS/k2lean-sidecar.json"
}

# ---------------------------------------------------------------- gate phases (tests/gate.sh)

needs_invariants() {
  if runs lib simpleinv || runs lib simplestore || runs lib simplet || runs lib simpleenvs; then
    [ -d "$SD" ] || need "SIMPLE's sources at $SD (set GATE_K_CHECKOUT)"
  fi
  return 0
}

# The modules of a Lean project that a failed build left unchecked: Lake names only the modules
# whose build failed (a broken hand case), not those it then did not build because they import
# one, directly or not (the `Invariants.lean` of a kind 1 library, the `Run.lean` of a demo).
unbuilt() { # DIR LOG MODULE...: of the import closure of MODULEs (all of DIR's when none), printed
  python3 -I - "$@" <<'EOF'
import re, sys
from pathlib import Path
root, log, want = Path(sys.argv[1]), Path(sys.argv[2]), sys.argv[3:]
text = log.read_text(errors="replace") if log.exists() else ""
failed = set(re.findall(r"^✖ \[\d+/\d+\] Building (\S+)", text, re.M))
imports = {}
for f in root.rglob("*.lean"):
    rel = f.relative_to(root)
    if rel.parts[0].startswith(".") or rel.name == "lakefile.lean":
        continue
    mod = ".".join(rel.with_suffix("").parts)
    imports[mod] = re.findall(r"^import\s+(\S+)", f.read_text(errors="replace"), re.M)
todo, need = list(want or imports), set()
while todo:
    m = todo.pop()
    if m in imports and m not in need:
        need.add(m)
        todo += imports[m]
broken = set(failed)
grew = True
while grew:
    grew = False
    for m in need - broken:
        if any(i in broken for i in imports[m]):
            broken.add(m)
            grew = True
left = sorted(broken - failed)
if failed:
    print(f"gate:   failed: {', '.join(sorted(failed))}; not built because they import it: {', '.join(left) or 'none'}")
EOF
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
  bad "invariant $d" "$L/build-$d-inv.log"; unbuilt "$o" "$L/build-$d-inv.log" "$n.Invariants"; return 1
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
  rm -rf "$NEG/KrsImp" "$NEG/lake-manifest.json"   # the manifest resolves the lakefile gen rewrites
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
  # (the command never overwrites a file, so the skeleton's files are deleted first; .lake/ is kept,
  # and the manifest, which records how the last lakefile's requires resolved, is deleted with them),
  # built like a demo (demo.Kind2Template)
  phase "kind2 template"
  local K2T=$W/kind2/KImpTpl
  mkdir -p "$K2T"
  find "$K2T" -name .lake -prune -o -name '*.lean' -type f -exec rm -f {} +
  rm -f "$K2T/lean-toolchain" "$K2T/lake-manifest.json"
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
  # a map extended by an `Int`-range map (tests/fixtures/range)
  runs lib range && inv_lib range KRange
  # a fold over `<k>` read item by item (tests/fixtures/kfold)
  runs lib kfold && inv_lib kfold KKFold
  # `orBool` list folds (tests/fixtures/anyfold)
  runs lib anyfold && inv_lib anyfold KAnyFold
  # walks by free-key patterns over a cell map and over maps (tests/fixtures/walk)
  runs lib walk && inv_lib walk KWalk
  # claims disjoint across a cell map's elements, read by `noDup` (tests/fixtures/drf's `drfOk`)
  runs lib drfinv && inv_lib drfinv Drf
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
  # SIMPLE's environments in the store (envsOk@T), from its own definition
  runs lib simpleenvs && kc simple-envs && inv_lib simpleenvs KSimpleInv
  phase "diff invariants"
  diffs kimpinv kimpkeys kimpfold kimptop kimpboth nested range walk kfold anyfold simpleinv simplestore simplet simpleenvs
  # kind 2 invariants, built like demos: a walk over <k> (ImpWrites), KRS IMP's declared cell type
  # (KrsImpTyping), and k2l_preserve's per-rule heartbeat budget over the range library (InvBudget)
  phase "demos invariants"
  for d in ImpWrites KrsImpTyping InvBudget; do
    runs demo "$d" || continue
    dbuild "$d"
    grep -q '^✖' "$L/build-$d.log" && unbuilt "$D/$d" "$L/build-$d.log"
  done
  runs demo Kind2Template && kind2_template
}
