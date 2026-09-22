#!/usr/bin/env bash
# IR-18 native diagnostic baseline (ticket procedure step 1) and native-twin controls.
#
#   native-diagnostics.sh [OUT]      (default /var/tmp/krs-ir18-native)
#
# Writes OUT/cases/<ID>/ for every case in cases.ts:
#   D001, D002+D004, D007   cargo +stable check --message-format=json of the BL-006 bins (cargo.jsonl, exit)
#   D003, D008              krs check of the BL-006 packages (stderr, exit) with the collector's stdout
#                           teed to native-bundle.json by the cargo shim (lower-shim/cargo)
#   D005, D006              the BL-006 anchor-probe (bl006-probe.json), and the lesson-level faults the
#                           browser injects: the native tour-minimal collector binary run over an export
#                           whose src/lib.rs is the E1 text (stale) or absent (missing) (stderr, exit)
#   X1, X2                  cargo +stable check of tour-minimal variants (cargo.jsonl, exit)
#   twin-*                  native-twin controls for the rustc cases: the worker's expansion of the case
#                           (expand-case.ts, same expander module as the staged assets) compiled by the
#                           x86_64 twin of rustc.wasm (same fork commit) against the pack, mapped with
#                           the worker's lookup (twin.stderr, twin-mapped.json)
#
# Environment: REPO (default: this checkout), BL006 (the retained BL-006 spike directory), KRS_BIN,
# ORACLE_DIR (regenerate-oracle.sh output at this revision: collector binary and exports), ASSETS
# (staged worker assets: expander module, pack), TWIN, KRS_Z3_LIB, LOAD_MAX (default 40).
set -euo pipefail

HERE=$(cd "$(dirname "$0")" && pwd)
WORKER=$(cd "$HERE/../.." && pwd)
REPO=${REPO:-$(git -C "$HERE" rev-parse --show-toplevel)}
OUT=${1:-/var/tmp/krs-ir18-native}
BL006=${BL006:-/home/sebastiengllmt/git/workspaces/starstream-fv/krs/draft/browser-lessons/spikes/BL-006}
KRS_BIN=${KRS_BIN:-/var/tmp/krs-ir17-cli-target/debug/krs}
ORACLE_DIR=${ORACLE_DIR:-/var/tmp/krs-ir17-oracle}
ASSETS=${ASSETS:-/var/tmp/krs-ir18-assets}
TWIN=${TWIN:-/var/tmp/krs-browser-fork/R-k/build/x86_64-unknown-linux-gnu/stage1/bin/rustc}
LOAD_MAX=${LOAD_MAX:-40}
Z3=${KRS_Z3_LIB:-$(find /nix/store -maxdepth 1 -name '*-z3-4.12.5-lib' -type d | head -1)/lib}
REAL_CARGO=$(command -v cargo)
FIXTURES=$WORKER/test/fixtures
CASES=$OUT/cases

wait_for_load() {
  local load
  while load=$(cut -d' ' -f1 /proc/loadavg) && awk -v l="$load" -v m="$LOAD_MAX" 'BEGIN { exit !(l > m) }'; do
    echo "load $load > $LOAD_MAX, waiting 60 s" >&2
    sleep 60
  done
}
low() { nice -n 19 ionice -c3 "$@"; }
record_exit() { echo "$2" >"$1/exit"; }

# The oracle directory must describe this checkout (regenerate-oracle.sh at this revision).
grep -q "crates_tree = \"$(git -C "$REPO" rev-parse HEAD:crates)\"" "$ORACLE_DIR/oracle.toml" \
  || { echo "$ORACLE_DIR/oracle.toml is not for this crates/ tree; run regenerate-oracle.sh first" >&2; exit 2; }
COLLECTOR=$(find "$ORACLE_DIR/target-native/x86_64-unknown-linux-gnu/debug" -maxdepth 1 -type f -name 'krs-generated-collector-*' | head -1)
[[ -x $COLLECTOR ]] || { echo "no native collector binary under $ORACLE_DIR" >&2; exit 2; }

rm -rf "$OUT"
mkdir -p "$CASES" "$OUT/lower-shim"
{
  echo "repo_head = $(git -C "$REPO" rev-parse HEAD)"
  echo "crates_tree = $(git -C "$REPO" rev-parse HEAD:crates)"
  echo "krs_bin_sha256 = $(sha256sum "$KRS_BIN" | cut -d' ' -f1)"
  echo "rustc = $(rustc +stable -V)"
  echo "twin = $("$TWIN" -V)"
  echo "collector = $COLLECTOR"
} >"$OUT/provenance.txt"

# ---------------------------------------------------------------- BL-006 workspace

# Copy the retained fixtures; point the path dependencies at this checkout's crates.
mkdir -p "$OUT/workspace"
cp -r "$BL006/Cargo.toml" "$BL006/anchor-probe" "$BL006/overlap" "$BL006/rust-expansion" "$BL006/wrong-result" "$OUT/workspace/"
sed -i "s|\"../../../../crates/|\"$REPO/crates/|" "$OUT/workspace/Cargo.toml"
for pair in rust-expansion/src/bin/malformed_macro.rs:malformed_macro.rs rust-expansion/src/bin/unresolved_constructor.rs:unresolved_constructor.rs \
  rust-expansion/src/bin/external_proc_macro.rs:external_proc_macro.rs wrong-result/src/lib.rs:wrong_result.rs overlap/src/lib.rs:overlap.rs; do
  cmp "$OUT/workspace/${pair%%:*}" "$FIXTURES/bl006/${pair##*:}"
done
(cd "$OUT/workspace" && sha256sum rust-expansion/src/bin/*.rs wrong-result/src/lib.rs overlap/src/lib.rs anchor-probe/src/main.rs) >"$OUT/fixtures.sha256"

cargo_check_bin() { # ID BIN
  local dir=$CASES/$1
  mkdir -p "$dir"
  wait_for_load
  set +e
  (cd "$OUT/workspace" && low cargo +stable check --offline -j 4 --bin "$2" --message-format=json \
    --target-dir "$OUT/target-check" >"$dir/cargo.jsonl" 2>"$dir/cargo.stderr")
  record_exit "$dir" $?
  set -e
}
cargo_check_bin D001 malformed_macro
cargo_check_bin D002-D004 unresolved_constructor
cargo_check_bin D007 external_proc_macro

# ---------------------------------------------------------------- krs check (lowering)

# The cargo shim: krs-cli runs the generated collector with `cargo run`; the shim tees its stdout
# (native bundle) or, with KRS_IR18_BUNDLE, replaces it by a browser bundle (native lowering of the
# browser bundle). Every other cargo invocation is the real cargo.
cat >"$OUT/lower-shim/cargo" <<EOF
#!/usr/bin/env bash
for argument in "\$@"; do [[ \$argument == run ]] && run=1; done
if [[ -n \${run:-} && -n \${KRS_IR18_BUNDLE:-} ]]; then cat "\$KRS_IR18_BUNDLE"; exit 0; fi
if [[ -n \${run:-} && -n \${KRS_IR18_TEE:-} ]]; then
  "$REAL_CARGO" "\$@" >"\$KRS_IR18_TEE"; status=\$?; cat "\$KRS_IR18_TEE"; exit \$status
fi
exec "$REAL_CARGO" "\$@"
EOF
chmod +x "$OUT/lower-shim/cargo"

krs_check() { # ID PACKAGE-DIR PACKAGE
  local dir=$CASES/$1
  mkdir -p "$dir"
  wait_for_load
  set +e
  low env PATH="$OUT/lower-shim:$PATH" KRS_IR18_TEE="$dir/native-bundle.json" LD_LIBRARY_PATH="$Z3" \
    CARGO_TARGET_DIR="$OUT/target-krs" CARGO_BUILD_JOBS=4 \
    "$KRS_BIN" check --manifest-path "$OUT/workspace/$2/Cargo.toml" --package "$3" --definition main \
    >"$dir/stdout" 2>"$dir/stderr"
  record_exit "$dir" $?
  set -e
}
krs_check D003 wrong-result bl006-wrong-result
krs_check D008 overlap bl006-overlap

# ---------------------------------------------------------------- collection faults

mkdir -p "$CASES/D005" "$CASES/D006"
wait_for_load
(cd "$OUT/workspace" && low cargo +stable build --offline -j 4 -p bl006-anchor-probe --target-dir "$OUT/target-check" -q)
for probe in stale:D005 missing:D006; do
  set +e
  "$OUT/target-check/debug/bl006-anchor-probe" "${probe%%:*}" >"$CASES/${probe##*:}/bl006-probe.json" 2>"$CASES/${probe##*:}/bl006-probe.stderr"
  echo $? >"$CASES/${probe##*:}/bl006-probe.exit"
  set -e
done

in_export() { # EXPORT CMD...: CMD with EXPORT mounted read-only over the checkout path
  local export=$1; shift
  local args=(--die-with-parent --tmpfs / --dev /dev --proc /proc)
  local entry
  for entry in /*; do
    case $entry in
      /dev | /proc) ;;
      *) if [[ -L $entry ]]; then args+=(--symlink "$(readlink "$entry")" "$entry"); else args+=(--bind "$entry" "$entry"); fi ;;
    esac
  done
  args+=(--ro-bind "$export" "$REPO" --chdir /)
  bwrap "${args[@]}" -- "$@"
}
cp -a "$ORACLE_DIR/src-base" "$OUT/src-missing"
rm "$OUT/src-missing/tests/tour-minimal/src/lib.rs"
cmp "$ORACLE_DIR/src-e1/tests/tour-minimal/src/lib.rs" "$FIXTURES/tour-minimal-e1.rs"
mkdir -p "$CASES/collector-control"
for run in collector-control:src-base D005:src-e1 D006:missing; do
  id=${run%%:*} export=${run##*:}
  [[ $export == missing ]] && export=$OUT/src-missing || export=$ORACLE_DIR/$export
  set +e
  in_export "$export" "$COLLECTOR" >"$CASES/$id/collector.stdout" 2>"$CASES/$id/collector.stderr"
  echo $? >"$CASES/$id/collector.exit"
  set -e
done
cmp "$CASES/collector-control/collector.stdout" "$ORACLE_DIR/native/descriptor-bundle.json"

# ---------------------------------------------------------------- tour-minimal rustc variants

tour_variant() { # ID FIXTURE
  local dir=$CASES/$1 pkg=$OUT/variants/$1
  mkdir -p "$dir" "$pkg/src"
  sed "s|path = \"../../crates/krs\"|path = \"$REPO/crates/krs\"|" "$REPO/tests/tour-minimal/Cargo.toml" >"$pkg/Cargo.toml"
  cp "$REPO/tests/tour-minimal/Cargo.lock" "$pkg/"
  cp "$FIXTURES/$2" "$pkg/src/lib.rs"
  wait_for_load
  set +e
  (cd "$pkg" && low cargo +stable check --offline -j 4 --message-format=json --target-dir "$OUT/target-variants" \
    >"$dir/cargo.jsonl" 2>"$dir/cargo.stderr")
  record_exit "$dir" $?
  set -e
}
tour_variant X1 rustc-unresolved-variant.rs
tour_variant X2 rustc-rule-head-missing-constructor.rs

# ---------------------------------------------------------------- native-twin controls

EXPANDER=$ASSETS/modules/krs_expand_wasm.wasm
PACK=$ASSETS/pack
KRS_RLIB=$(find "$PACK/deps" -name 'libkrs-*.rlib' | head -1)
(cd "$WORKER" && bun test/parity/cases.ts write-lessons "$ASSETS" "$OUT/lessons")
twin_control() { # ID LESSON FIXTURE [FAULT]
  local id=$1 lesson=$OUT/lessons/$2.json fixture=$FIXTURES/$3 fault=${4:-}
  local dir=$CASES/$id/twin
  mkdir -p "$dir"
  (cd "$WORKER" && bun test/parity/expand-case.ts expand --expander "$EXPANDER" --lesson "$lesson" --source "$fixture" \
    --out "$dir" ${fault:+--fault "$fault"}) >"$dir/expand.json"
  [[ -f $dir/expanded.rs ]] || return 0
  local crate name version dir_ flags
  crate=$(jq -r .package.crate_name "$lesson")
  name=$(jq -r .package.cargo_name "$lesson")
  version=$(jq -r .package.cargo_version "$lesson")
  dir_=$(jq -r .package.manifest_dir "$lesson")
  mapfile -t flags < <(jq -r '.rustc_lint_flags[]' "$lesson")
  set +e
  low env CARGO_PKG_NAME="$name" CARGO_PKG_VERSION="$version" CARGO_MANIFEST_DIR="$dir_" CARGO_CRATE_NAME="$crate" \
    "$TWIN" "$dir/expanded.rs" --crate-name "$crate" --crate-type rlib --edition 2024 --target wasm32-wasip1 \
    -C panic=abort -Zproc-macro-metadata-only -L "dependency=$PACK/deps" -L "dependency=$PACK/proc-macro-meta" \
    --extern "k=$KRS_RLIB" --error-format=json "${flags[@]}" -A non_camel_case_types -A non_snake_case \
    --emit=metadata -o "$dir/out.rmeta" 2>"$dir/twin.stderr"
  echo $? >"$dir/exit"
  set -e
  (cd "$WORKER" && bun test/parity/expand-case.ts map --expander "$EXPANDER" --dir "$dir" --source "$fixture" \
    --stderr "$dir/twin.stderr") >"$dir/twin-mapped.json"
}
twin_control D002-D004 bl006-rust-expansion bl006/unresolved_constructor.rs
twin_control D009 tour-minimal tour-minimal.rs registration-table-missing-factory
twin_control X1 tour-minimal rustc-unresolved-variant.rs
twin_control X2 tour-minimal rustc-rule-head-missing-constructor.rs

(cd "$CASES" && find . -type f -not -name '*.rmeta' | sort | xargs sha256sum) >"$OUT/cases.sha256"
echo "native baseline in $OUT"
