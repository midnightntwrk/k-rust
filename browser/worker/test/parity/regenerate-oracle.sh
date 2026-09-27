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
# CLI_TARGET (default SCRATCH/krs-parity-cli-target), KRS_BIN (a krs binary
# built from this checkout; built when absent), KRS_Z3_LIB, LOAD_MAX (default 40).
set -euo pipefail

HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(git -C "$HERE" rev-parse --show-toplevel)
SCRATCH=${KRS_GATE_SCRATCH:-/var/tmp}
OUT=${1:-$SCRATCH/krs-parity-oracle}
ORACLE_TOML=${2:-$OUT/oracle.toml}
LOAD_MAX=${LOAD_MAX:-40}
Z3=${KRS_Z3_LIB:-$(ls -d /nix/store/*-z3-4.12.5-lib/lib | head -1)}
CLI_TARGET=${CLI_TARGET:-$SCRATCH/krs-parity-cli-target}
KRS_BIN=${KRS_BIN:-$CLI_TARGET/debug/krs}
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

if [[ ! -x $KRS_BIN ]]; then
  wait_for_load
  (cd "$REPO" && LIBRARY_PATH=$Z3${LIBRARY_PATH:+:$LIBRARY_PATH} LD_LIBRARY_PATH=$Z3${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH} \
    nice -n 19 ionice -c3 cargo +stable build --locked --offline -j 4 -p krs-cli --bin krs --target-dir "$CLI_TARGET")
fi

export_at() { # DIR: fresh git archive of HEAD
  rm -rf "$1"
  mkdir -p "$1"
  git -C "$REPO" archive "$REV" | tar -x -C "$1"
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
  in_export "$export" env LD_LIBRARY_PATH="$Z3" CARGO_TARGET_DIR="$OUT/target-$name" CARGO_BUILD_JOBS=4 \
    "$KRS_BIN" emit-k --manifest-path "$REPO/tests/tour-minimal/Cargo.toml" \
    --package krs-tour-minimal --definition main --output "$OUT/$name" \
    >"$OUT/$name.stdout" 2>"$OUT/$name.stderr"
  local collector
  collector=$(find "$OUT/target-$name" -type f -path '*/debug/krs-generated-collector-*' -perm -u+x -print -quit)
  [[ -x $collector ]] || { echo "no native collector built under $OUT/target-$name" >&2; exit 2; }
  in_export "$export" env LD_LIBRARY_PATH="$Z3" "$collector" >"$OUT/$name/collector-stdout.json"
  echo $((SECONDS - started)) >"$OUT/$name.seconds"
}

mkdir -p "$OUT"
export_at "$OUT/src-base"
export_at "$OUT/src-e1"
(cd "$OUT/src-e1" && patch -p1 --quiet <"$PATCH")
emit native "$OUT/src-base"
emit native-e1 "$OUT/src-e1"

python3 - "$OUT" "$REPO" "$REV" "$ORACLE_TOML" "$KRS_BIN" "$PATCH" <<'PY'
import hashlib, json, subprocess, sys
from collections import Counter
from pathlib import Path

out, repo, rev, oracle_toml, krs_bin, patch = sys.argv[1:]
out = Path(out)

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def tree(spec):
    return subprocess.check_output(["git", "-C", repo, "rev-parse", f"{rev}:{spec}"], text=True).strip()

def record(name, lesson):
    pretty = out / name / "descriptor-bundle.json"
    data = json.loads(pretty.read_bytes())
    bundle = out / name / "collector-stdout.json"
    if json.loads(bundle.read_bytes()) != data:
        sys.exit(f"{name}: collector stdout differs from the pretty emit-k artifact")
    if not bundle.read_bytes().endswith(b"\n"):
        sys.exit(f"{name}: collector stdout lacks its trailing newline")
    kinds = Counter(d["descriptor_kind"] for d in data["descriptors"])
    return {
        "bundle": str(bundle),
        "bundle_bytes": bundle.stat().st_size,
        "bundle_sha256": sha(bundle),
        "protocol_version": data["protocol_version"],
        "descriptors": len(data["descriptors"]),
        "descriptor_kinds": dict(sorted(kinds.items())),
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
    "recipe = \"krs emit-k --manifest-path tests/tour-minimal/Cargo.toml --package krs-tour-minimal --definition main (git export of krs_revision mounted over the checkout path)\"",
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
