#!/usr/bin/env bash
# Native oracle regeneration for the tour-minimal bundle parity gate.
#
#   regenerate-oracle.sh [OUT] [ORACLE_TOML]
#
# OUT          scratch directory (default SCRATCH/krs-parity-oracle); holds the git
#              exports, the Cargo target directories, and the two emit-k outputs.
# ORACLE_TOML  where to write the provenance record (default OUT/oracle.toml).
#
# The native oracle is the stdout of the collector built by `krs emit-k`
# (inventory mode, native krs-macros) for tests/tour-minimal at HEAD, and for
# the E1 edit (edit-e1.patch) applied to a git export of HEAD.
# The fixture in the checkout is never modified: each
# export is mounted read-only over the checkout path in a private bwrap
# namespace, because krs-cli finds the framework through its compile-time
# CARGO_MANIFEST_DIR.
#
# Environment: KRS_GATE_SCRATCH (the scratch root SCRATCH, default /var/tmp),
# CLI_TARGET (default SCRATCH/krs-parity-cli-target; krs and krs-gate are built
# from this checkout on every run), KRUST_GATE_Z3 and KRS_Z3_LIB, LOAD_MAX (default 40).
# krs and krs-gate link Z3 as the KRS gates build them (krs/tests/support/tools.py, z3_route):
# by default the release Krs.lock [solver] linked names, downloaded and linked statically;
# under KRUST_GATE_Z3=system the library in KRS_Z3_LIB, which must then be set.
set -euo pipefail

HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(git -C "$HERE" rev-parse --show-toplevel)
SCRATCH=${KRS_GATE_SCRATCH:-/var/tmp}
OUT=${1:-$SCRATCH/krs-parity-oracle}
ORACLE_TOML=${2:-$OUT/oracle.toml}
LOAD_MAX=${LOAD_MAX:-40}
# z3_check is the KRS gates' Z3 check (krs/tests/support/tools.py): `z3_check library` prints the
# library directory a KRUST_GATE_Z3=system build links, and fails unless KRS_Z3_LIB holds the
# Krs.lock [solver] linked release (z3_library_dir); `z3_check linked BINARY...` fails unless each
# binary links that release under the route's library paths (require_linked_z3).
z3_check() {
  python3 - "$HERE/../../../../tests" "$@" <<'PY'
import sys
from pathlib import Path
sys.path.insert(0, sys.argv[1])
from support import GateError
from support.tools import require_linked_z3, z3_environment, z3_library_dir
try:
    if sys.argv[2] == "library":
        print(z3_library_dir())
    else:
        for binary in sys.argv[3:]:
            require_linked_z3(Path(binary), z3_environment())
except GateError as error:
    sys.exit(f"error: {error}")
PY
}
case ${KRUST_GATE_Z3:-gh-release} in
  gh-release) Z3= ;;
  system)
    : "${KRS_Z3_LIB:?KRUST_GATE_Z3=system needs KRS_Z3_LIB, the library directory of Krs.lock [solver] linked}"
    Z3=$(z3_check library) ;;
  *) echo "KRUST_GATE_Z3 must be gh-release or system, not $KRUST_GATE_Z3" >&2; exit 2 ;;
esac
CLI_TARGET=${CLI_TARGET:-$SCRATCH/krs-parity-cli-target}
KRS_BIN=$CLI_TARGET/debug/krs
GATE_BIN=$CLI_TARGET/debug/krs-gate
PATCH=$HERE/edit-e1.patch

wait_for_load() {
  local load
  while load=$(cut -d' ' -f1 /proc/loadavg) && awk -v l="$load" -v m="$LOAD_MAX" 'BEGIN { exit !(l > m) }'; do
    echo "load $load > $LOAD_MAX, waiting 60 s" >&2
    sleep 60
  done
}

# The oracle inputs must be committed: the export is HEAD, not the working tree.
if ! git -C "$REPO" diff --quiet HEAD -- crates tests/tour-minimal Cargo.lock; then
  echo "crates/, tests/tour-minimal, or Cargo.lock differ from HEAD; commit them first" >&2
  exit 2
fi
REV=$(git -C "$REPO" rev-parse HEAD)

# One package per invocation, so krs-gate's features never unify into the krs binary.
for package in krs-cli:krs:z3-inference,kink krs-gate:krs-gate:z3-inference; do
  IFS=: read -r name binary features <<<"$package"
  route=()
  [[ -n $Z3 ]] && route=(--no-default-features --features "$features")
  wait_for_load
  (cd "$REPO" && env ${Z3:+"LIBRARY_PATH=$Z3${LIBRARY_PATH:+:$LIBRARY_PATH}"} ${Z3:+"LD_LIBRARY_PATH=$Z3${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"} \
    nice -n 19 ionice -c3 cargo +stable build --locked --offline -j 4 -p "$name" --bin "$binary" "${route[@]}" --target-dir "$CLI_TARGET")
done
z3_check linked "$KRS_BIN" "$GATE_BIN"

export_at() { # DIR: fresh git archive of HEAD
  rm -rf "$1"
  mkdir -p "$1"
  git -C "$REPO" archive "$REV" | tar -x -C "$1"
  cargo +stable generate-lockfile --manifest-path "$1/tests/tour-minimal/Cargo.toml" --offline
}

in_export() { # EXPORT CMD...: run CMD with EXPORT mounted read-only over the checkout path
  local export=$1; shift
  local args=(--die-with-parent --tmpfs / --dev /dev --proc /proc)
  local entry
  for entry in /*; do
    case $entry in
      /dev | /proc) ;;
      *) if [[ -L $entry ]]; then args+=(--symlink "$(readlink "$entry")" "$entry"); else args+=(--bind "$entry" "$entry"); fi ;;
    esac
  done
  args+=(--ro-bind "$export" "$REPO" --chdir "$REPO")
  # An external compiler-cache server would read the unmounted host checkout.
  env -u RUSTC_WRAPPER nice -n 19 ionice -c3 bwrap "${args[@]}" -- "$@"
}

emit() { # NAME EXPORT
  local name=$1 export=$2
  rm -rf "${OUT:?}/$name"
  wait_for_load
  local started=$SECONDS
  in_export "$export" env ${Z3:+"LD_LIBRARY_PATH=$Z3"} CARGO_TARGET_DIR="$OUT/target-$name" CARGO_BUILD_JOBS=4 \
    "$KRS_BIN" emit-k --manifest-path "$REPO/tests/tour-minimal/Cargo.toml" \
    --package krs-tour-minimal --definition main --ir --output "$OUT/$name" \
    >"$OUT/$name.stdout" 2>"$OUT/$name.stderr"
  local collector
  collector=$(find "$OUT/target-$name" -type f -path '*/debug/krs-generated-collector-*' -perm -u+x -print -quit)
  [[ -x $collector ]] || { echo "no native collector built under $OUT/target-$name" >&2; exit 2; }
  in_export "$export" env ${Z3:+"LD_LIBRARY_PATH=$Z3"} "$collector" >"$OUT/$name/collector-stdout.json"
  echo $((SECONDS - started)) >"$OUT/$name.seconds"
}

mkdir -p "$OUT"
export_at "$OUT/src-base"
export_at "$OUT/src-e1"
(cd "$OUT/src-e1" && patch -p1 --quiet <"$PATCH")
emit native "$OUT/src-base"
emit native-e1 "$OUT/src-e1"

env ${Z3:+"LD_LIBRARY_PATH=$Z3${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"} python3 - "$OUT" "$REPO" "$REV" "$ORACLE_TOML" "$KRS_BIN" "$PATCH" "$GATE_BIN" <<'PY'
import hashlib, json, subprocess, sys
from pathlib import Path

out, repo, rev, oracle_toml, krs_bin, patch, gate_bin = sys.argv[1:]
out = Path(out)

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def tree(spec):
    return subprocess.check_output(["git", "-C", repo, "rev-parse", f"{rev}:{spec}"], text=True).strip()

def record(name, lesson):
    pretty = out / name / "descriptor-bundle.json"
    bundle = out / name / "collector-stdout.json"
    summary = json.loads(subprocess.check_output([
        gate_bin, "collector-bundle", str(bundle), str(pretty),
    ]))
    if not bundle.read_bytes().endswith(b"\n"):
        sys.exit(f"{name}: collector stdout lacks its trailing newline")
    return {
        "bundle": str(bundle),
        "bundle_bytes": bundle.stat().st_size,
        "bundle_sha256": sha(bundle),
        "protocol_version": summary["protocol_version"],
        "descriptors": summary["descriptors"],
        "descriptor_kinds": summary["descriptor_kinds"],
        "lesson_source": str(lesson),
        "lesson_source_sha256": sha(lesson),
        "emit_seconds": int((out / f"{name}.seconds").read_text()),
    }

base = record("native", out / "src-base/tests/tour-minimal/src/lib.rs")
e1 = record("native-e1", out / "src-e1/tests/tour-minimal/src/lib.rs")
if base["bundle_sha256"] == e1["bundle_sha256"]:
    sys.exit("the E1 oracle equals the unmodified oracle: E1 does not alter the bundle")

def q(value):
    return json.dumps(value)

lines = [
    "# tour-minimal native oracle provenance (browser/worker/test/parity/regenerate-oracle.sh).",
    "# The gate refuses to compare when any [validity] value differs from the checkout.",
    "schema = 1",
    f"krs_revision = {q(rev)}",
    f"krs_bin_sha256 = {q(sha(krs_bin))}",
    "recipe = \"krs emit-k --manifest-path tests/tour-minimal/Cargo.toml --package krs-tour-minimal --definition main --ir (git export of krs_revision mounted over the checkout path)\"",
    "",
    "[validity]",
    f"crates_tree = {q(tree('crates'))}",
    f"tour_minimal_tree = {q(tree('tests/tour-minimal'))}",
    f"cargo_lock_blob = {q(tree('Cargo.lock'))}",
    f"krs_lib_rs_sha256 = {q(sha(out / 'src-base/crates/krs/src/lib.rs'))}",
    f"lesson_source_sha256 = {q(base['lesson_source_sha256'])}",
    f"protocol_version = {base['protocol_version']}",
]
for table, rec in (("oracle", base), ("oracle_e1", e1)):
    lines += ["", f"[{table}]"]
    for key in ("bundle", "bundle_bytes", "bundle_sha256", "protocol_version", "descriptors", "lesson_source", "lesson_source_sha256", "emit_seconds"):
        lines.append(f"{key} = {q(rec[key])}")
    if table == "oracle_e1":
        lines.append(f"edit_patch_sha256 = {q(sha(patch))}")
    lines.append(f"[{table}.descriptor_kinds]")
    lines += [f"{k} = {v}" for k, v in rec["descriptor_kinds"].items()]
Path(oracle_toml).write_text("\n".join(lines) + "\n")
(out / "native-collector-stdout.sha256").write_text(f"{base['bundle_sha256']}  collector-stdout.json\n")
(out / "native-e1-collector-stdout.sha256").write_text(f"{e1['bundle_sha256']}  collector-stdout.json\n")
print(Path(oracle_toml).read_text())
PY
