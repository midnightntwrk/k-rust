#!/usr/bin/env bash
# Builds the KRS browser dependency pack with the native twin of the wasip1-hosted rustc fork.
#
# Usage: browser/pack/build.sh FORK_ROOT OUTPUT_DIR
#
#   FORK_ROOT   a fork build root laid out as the fork-build recipe builds it, e.g. /var/tmp/krs-browser-fork/R-k:
#                 build/x86_64-unknown-linux-gnu/stage1/     native twin (bin/rustc, lib/rustlib/{x86_64-unknown-linux-gnu,wasm32-wasip1})
#                 out/rustc/rustc.wasm                       wasip1-hosted rustc of the same fork commit
#                 out/wasip1/stage/rustc/sysroot-wasip1.bundle   its RIWB1 sysroot bundle
#   OUTPUT_DIR  must not exist or be empty; receives
#                 pack/            the pack (see browser/pack/manifest-format.toml), including pack/pack-manifest.toml
#                 build/           build scratch and logs (not part of the pack): src/ (git archive, mounted at /krs),
#                                  target/ (mounted at /pack-target), build.jsonl, cargo.stderr, inventory-tree.txt,
#                                  path-scan.txt, build-stats.toml
#
# Environment:
#   KRS_REPO     KRS checkout to export (default: the checkout containing this script)
#   KRS_REV      revision to export with `git archive` (default HEAD); the export must contain browser/pack
#   FORK_SOURCE  optional fork source checkout; when set, its HEAD must equal the twin's commit-hash and
#                the commits FORK_PATCH_BASE..HEAD are recorded as the fork patch set
#   FORK_PATCH_BASE  default krs/base
#   FORK_REPOSITORY  default https://github.com/AngelOnFira/rust (recorded only)
#   CARGO_HOME_HOST  the Cargo home bound at /cargo (default $HOME/.cargo); used offline
#   PACK_TARGET  namespace path of the target directory (default /pack-target); only for the
#                target-path leak diagnostic, since proc-macro crate hashes may depend on it
#   JOBS (default 4), LOAD_MAX (default 40), LOCK (default /var/tmp/krs-browser-fork/heavy-build.lock)
#
# The build is Cargo driving the twin (RUSTC) inside a bubblewrap mount namespace in which
#   /krs          = the git archive export, read-only (the stable virtual root of framework sources; never remapped)
#   /pack-target  = OUTPUT_DIR/build/target (fixed path: proc-macro and build-script hashes depend on it)
#   /cargo        = CARGO_HOME_HOST (fixed path for the registry sources)
#   /fork/stage1  = the twin's stage1 directory, read-only
# and every other top-level host directory at its own path.
# Target units are compiled with the flags in RUSTFLAGS below; host units (build scripts and
# proc macros) are not, which is Cargo's behaviour with --target.
# The heavy step runs under `flock $LOCK`, `nice -n 19 ionice -c3`, and waits while the
# 1-minute load average exceeds LOAD_MAX.
set -euo pipefail

usage() { sed -n 2,40p "$0" >&2; exit 2; }
[[ $# -eq 2 ]] || usage

HERE=$(cd "$(dirname "$0")" && pwd)
FORK_ROOT=$(realpath "$1")
OUTPUT=$(realpath -m "$2")
KRS_REPO=${KRS_REPO:-$(git -C "$HERE" rev-parse --show-toplevel)}
KRS_REV=$(git -C "$KRS_REPO" rev-parse --verify "${KRS_REV:-HEAD}^{commit}")
FORK_PATCH_BASE=${FORK_PATCH_BASE:-krs/base}
FORK_REPOSITORY=${FORK_REPOSITORY:-https://github.com/AngelOnFira/rust}
CARGO_HOME_HOST=$(realpath "${CARGO_HOME_HOST:-$HOME/.cargo}")
JOBS=${JOBS:-4}
LOAD_MAX=${LOAD_MAX:-40}
LOCK=${LOCK:-/var/tmp/krs-browser-fork/heavy-build.lock}
PACK_TARGET=${PACK_TARGET:-/pack-target}
[[ $PACK_TARGET =~ ^/[a-z0-9-]+$ && ! $PACK_TARGET =~ ^/(krs|cargo|fork|dev|proc|target|registry)$ && ! -e $PACK_TARGET ]] \
  || { echo "build.sh: PACK_TARGET must be a new top-level path such as /pack-target" >&2; exit 2; }
export KRS_PACK_NS_TARGET=$PACK_TARGET

STAGE1=$FORK_ROOT/build/x86_64-unknown-linux-gnu/stage1
TWIN=$STAGE1/bin/rustc
RUSTC_WASM=$FORK_ROOT/out/rustc/rustc.wasm
BUNDLE=$FORK_ROOT/out/wasip1/stage/rustc/sysroot-wasip1.bundle
CARGO=$(rustup which --toolchain stable cargo)
TARGET=wasm32-wasip1

die() { echo "build.sh: $*" >&2; exit 1; }

# ------------------------------------------------------------------ preconditions

for f in "$TWIN" "$RUSTC_WASM" "$BUNDLE"; do [[ -f $f ]] || die "missing $f"; done
# The stage1 sysroot keeps only the targets of the last x.py invocation; both std libraries are
# needed (host units link against x86_64 std, target units against wasm32-wasip1 std).
for t in x86_64-unknown-linux-gnu "$TARGET"; do
  compgen -G "$STAGE1/lib/rustlib/$t/lib/libstd-*.rlib" >/dev/null \
    || die "twin sysroot lacks $t std; run the fork's 'x.py build library --stage 1 --target x86_64-unknown-linux-gnu,$TARGET'"
done
if [[ -e $OUTPUT ]] && [[ -n $(ls -A "$OUTPUT") ]]; then die "$OUTPUT is not empty (a pack build must start clean)"; fi
mkdir -p "$OUTPUT/build/src" "$OUTPUT/build/target" "$OUTPUT/pack"
BUILD=$OUTPUT/build

registry_dirs=("$CARGO_HOME_HOST"/registry/src/index.crates.io-*)
[[ ${#registry_dirs[@]} -eq 1 && -d ${registry_dirs[0]} ]] || die "expected one crates.io source directory in $CARGO_HOME_HOST/registry/src"
REGISTRY_INDEX=$(basename "${registry_dirs[0]}")

# Compiler identities. rustc.wasm -vV runs under Node's WASI with no preopens.
"$TWIN" -vV >"$BUILD/twin-vV.txt"
node --disable-warning=ExperimentalWarning --input-type=module -e '
import { readFile } from "node:fs/promises";
import { WASI } from "node:wasi";
const wasi = new WASI({ version: "preview1", args: ["rustc", "-vV"], env: {}, returnOnExit: true });
const module = await WebAssembly.compile(await readFile(process.argv[1]));
const instance = await WebAssembly.instantiate(module, wasi.getImportObject());
process.exitCode = wasi.start(instance);
' "$RUSTC_WASM" >"$BUILD/rustc-wasm-vV.txt"
twin_commit=$(sed -n 's/^commit-hash: //p' "$BUILD/twin-vV.txt")
wasm_commit=$(sed -n 's/^commit-hash: //p' "$BUILD/rustc-wasm-vV.txt")
[[ -n $twin_commit && $twin_commit == "$wasm_commit" ]] \
  || die "twin ($twin_commit) and rustc.wasm ($wasm_commit) are not from one fork commit (rlibs would fail with E0514)"
[[ $(head -1 "$BUILD/twin-vV.txt") == "$(head -1 "$BUILD/rustc-wasm-vV.txt")" ]] || die "twin and rustc.wasm version lines differ"
grep -qx "host: $TARGET" "$BUILD/rustc-wasm-vV.txt" || die "rustc.wasm is not hosted on $TARGET"

fork_commits=()
if [[ -n ${FORK_SOURCE:-} ]]; then
  [[ $(git -C "$FORK_SOURCE" rev-parse HEAD) == "$twin_commit" ]] || die "FORK_SOURCE HEAD is not $twin_commit"
  mapfile -t fork_commits < <(git -C "$FORK_SOURCE" log --reverse --format='%H %s' "$FORK_PATCH_BASE..HEAD")
fi

# ------------------------------------------------------------------ KRS source at /krs

git -C "$KRS_REPO" archive "$KRS_REV" | tar -x -C "$BUILD/src"
[[ -f $BUILD/src/browser/pack/Cargo.toml ]] || die "revision $KRS_REV has no browser/pack/Cargo.toml"

RUSTFLAGS=(
  "--remap-path-prefix=/cargo/registry/src/$REGISTRY_INDEX=/registry"
  "--remap-path-prefix=$PACK_TARGET=/target"
  -Cdebuginfo=0 -Ccodegen-units=1 -Cpanic=abort -Cstrip=none
)
CARGO_ARGS=(build --locked --offline --release --target "$TARGET" -j "$JOBS" -v --message-format=json-render-diagnostics)
encoded=$(printf '%s\x1f' "${RUSTFLAGS[@]}"); encoded=${encoded%$'\x1f'}

ns_args=(--die-with-parent --tmpfs / --dev /dev --proc /proc)
for entry in /*; do
  case $entry in
    /dev | /proc | /krs | "$PACK_TARGET" | /cargo | /fork) ;;
    *) if [[ -L $entry ]]; then ns_args+=(--symlink "$(readlink "$entry")" "$entry"); else ns_args+=(--bind "$entry" "$entry"); fi ;;
  esac
done
ns_args+=(--ro-bind "$BUILD/src" /krs --bind "$BUILD/target" "$PACK_TARGET" --bind "$CARGO_HOME_HOST" /cargo
  --ro-bind "$STAGE1" /fork/stage1 --chdir /krs/browser/pack)
# NS: the command prefix that runs its arguments inside the namespace with a fixed environment.
NS=(bwrap "${ns_args[@]}" -- env -i HOME="$HOME" PATH=/usr/bin:/bin LANG=C.UTF-8
  CARGO_HOME=/cargo CARGO_TARGET_DIR="$PACK_TARGET" RUSTC=/fork/stage1/bin/rustc
  CARGO_INCREMENTAL=0 CARGO_BUILD_JOBS="$JOBS" SOURCE_DATE_EPOCH=0
  CARGO_ENCODED_RUSTFLAGS="$encoded")

# ------------------------------------------------------------------ feature check (no inventory)

set +e
"${NS[@]}" "$CARGO" tree --locked --offline --target "$TARGET" -e normal,features -i inventory \
  >"$BUILD/inventory-tree.txt" 2>&1
rc=$?
set -e
if ((rc == 0)) && [[ -s $BUILD/inventory-tree.txt ]]; then die "feature unification enables inventory for $TARGET (build/inventory-tree.txt)"; fi
grep -q 'did not match any packages' "$BUILD/inventory-tree.txt" || ((rc == 0)) || die "cargo tree failed (build/inventory-tree.txt)"
grep -q '^name = "inventory"$' "$BUILD/src/browser/pack/Cargo.lock" && die "browser/pack/Cargo.lock contains inventory"

# ------------------------------------------------------------------ heavy step

exec 9>"$LOCK"
echo "build.sh: waiting for $LOCK" >&2
flock 9
while :; do
  load=$(cut -d' ' -f1 /proc/loadavg)
  awk -v l="$load" -v m="$LOAD_MAX" 'BEGIN{exit !(l<=m)}' && break
  echo "build.sh: load $load > $LOAD_MAX, waiting" >&2
  sleep 60
done
load_at_start=$(cat /proc/loadavg)
t0=$(date +%s%N)
set +e
heavy=(nice -n 19 ionice -c3 "${NS[@]}" "$CARGO" "${CARGO_ARGS[@]}")
if systemd-run --user --scope --quiet true 2>/dev/null; then
  # A transient scope gives the build its own cgroup, whose memory.peak is the build's peak memory.
  systemd-run --user --scope --quiet --unit="krs-browser-pack-$$-$(date +%s)" -- bash -c '
    cg=$(cut -d: -f3 /proc/self/cgroup); "$@"; rc=$?
    cat "/sys/fs/cgroup$cg/memory.peak" >"'"$BUILD/memory-peak"'" 2>/dev/null; exit $rc' _ \
    "${heavy[@]}" >"$BUILD/build.jsonl" 2>"$BUILD/cargo.stderr"
else
  "${heavy[@]}" >"$BUILD/build.jsonl" 2>"$BUILD/cargo.stderr"
fi
rc=$?
set -e
t1=$(date +%s%N)
flock -u 9
exec 9>&-
((rc == 0)) || { tail -30 "$BUILD/cargo.stderr" >&2; die "cargo build failed ($rc); see $BUILD/cargo.stderr"; }
{
  echo "wall_s = $(awk -v n=$((t1 - t0)) 'BEGIN{printf "%.1f", n/1e9}')"
  echo "memory_peak_bytes = $(cat "$BUILD/memory-peak" 2>/dev/null || echo 0)"
  echo "load_at_start = \"$load_at_start\""
  echo "jobs = $JOBS"
  echo "build_jsonl_sha256 = \"$(sha256sum "$BUILD/build.jsonl" | cut -d' ' -f1)\""
} >"$BUILD/build-stats.toml"

# ------------------------------------------------------------------ pack and manifest

producer=(
  --set "krs_revision=$KRS_REV"
  --set "krs_crates_tree=$(git -C "$KRS_REPO" rev-parse "$KRS_REV:crates")"
  --set "krs_pack_tree=$(git -C "$KRS_REPO" rev-parse "$KRS_REV:browser/pack")"
  --set "cargo_version=$("$CARGO" -V)"
  --set "fork_repository=$FORK_REPOSITORY"
  --set "registry_index=$REGISTRY_INDEX"
)
for c in "${fork_commits[@]}"; do producer+=(--fork-commit "$c"); done
python3 "$HERE/manifest.py" assemble --build "$BUILD" --pack "$OUTPUT/pack" \
  --stage1 "$STAGE1" --rustc-wasm "$RUSTC_WASM" --bundle "$BUNDLE" --cargo-home "$CARGO_HOME_HOST" \
  --rustflag-sep $'\x1f' "--rustflags=$encoded" --cargo-args "${CARGO_ARGS[*]}" "${producer[@]}"
python3 "$HERE/manifest.py" verify "$OUTPUT/pack"
python3 "$HERE/manifest.py" scan "$OUTPUT/pack" --host-path "$HOME/" --host-path /var/tmp/ --host-path /nix/store/ \
  --host-path "$KRS_REPO" --host-path "$FORK_ROOT" --host-path "$OUTPUT" --host-path "$CARGO_HOME_HOST" \
  >"$BUILD/path-scan.txt" \
  || die "path scan found undeclared paths (build/path-scan.txt)"
echo "build.sh: pack at $OUTPUT/pack, pack_id $(python3 "$HERE/manifest.py" id "$OUTPUT/pack")" >&2
