#!/usr/bin/env bash
# The WASM execution gate: compile the pinned WASM semantics with krust, run `krust krun` on the
# programs of upstream's tests/simple and `krust kprove` on the specs of upstream's tests/proofs,
# and compare each result with scripts/wasm-execution-gate.toml.
set -euo pipefail

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
source "$workspace/scripts/reference-memory-guard.sh"
reference_enter_whole_job "$@"
source "$workspace/scripts/reference-pins.sh"
k_checkout=${K_CHECKOUT:-"$workspace/k"}
wasm_checkout=${WASM_SEMANTICS_CHECKOUT:-"$workspace/wasm-semantics"}
manifest="$workspace/scripts/wasm-execution-gate.toml"
success_configuration="$workspace/scripts/wasm-execution-gate.success.kore"
program_timeout=${WASM_EXECUTION_GATE_PROGRAM_TIMEOUT_SECONDS:-30}
proof_timeout=${WASM_EXECUTION_GATE_PROOF_TIMEOUT_SECONDS:-60}
work=
update=false

usage() {
  cat <<'EOF'
usage: scripts/wasm-execution-gate.sh [--work DIR] [--update] [CASE...]

Compile the pinned WASM semantics (test.md, WASM-TEST) with krust, run `krust krun` on each
program of wasm-semantics/tests/simple and `krust kprove` on each spec of
wasm-semantics/tests/proofs, and compare the results with scripts/wasm-execution-gate.toml.
A CASE is a manifest name (`simple/arithmetic`, `proofs/loops`); without one, every case runs.
Exit status 3 when a result differs, 2 on a usage or setup error.

A program's result is its exit status, its standard error, and its standard output: either
`success`, the final configuration of a passing upstream test as krust renders it
(scripts/wasm-execution-gate.success.kore), or the SHA-256 of another output. A proof's result
is its exit status, its standard error, and its verdict: the lines of standard output indented
by at most two spaces (each claim's status and state counts, and where a failed claim stopped).

krust is $KRUST_BIN when set, otherwise the gate binary built as the reference gates build it
(KRUST_GATE_Z3, KRUST_GATE_TARGET_DIR, KRUST_GATE_INVARIANT_CHECKS). The checkouts are
$WASM_SEMANTICS_CHECKOUT and $K_CHECKOUT (default: the workspace's wasm-semantics and k), at
the pins of scripts/reference-differential.toml. Each program runs under a
$WASM_EXECUTION_GATE_PROGRAM_TIMEOUT_SECONDS limit (default 30), each proof under
$WASM_EXECUTION_GATE_PROOF_TIMEOUT_SECONDS (default 60).

  --work DIR   keep the compiled definition and every output in DIR (default: a temporary
               directory, removed on exit unless a result differs)
  --update     rewrite the selected cases' expected results in the manifest from this run
EOF
}

die() {
  echo "error: $*" >&2
  exit 2
}

cases=()
while (($#)); do
  case "$1" in
    --work) work=${2:?}; shift 2 ;;
    --update) update=true; shift ;;
    -h | --help) usage; exit 0 ;;
    -*) usage >&2; die "unknown argument $1" ;;
    *) cases+=("$1"); shift ;;
  esac
done

[[ "$program_timeout" =~ ^[1-9][0-9]*$ ]] || die "WASM_EXECUTION_GATE_PROGRAM_TIMEOUT_SECONDS must be positive"
[[ "$proof_timeout" =~ ^[1-9][0-9]*$ ]] || die "WASM_EXECUTION_GATE_PROOF_TIMEOUT_SECONDS must be positive"
semantics="$wasm_checkout/pykwasm/src/pykwasm/kdist/wasm-semantics"
builtin="$k_checkout/k-distribution/include/kframework/builtin"
[[ -f "$semantics/test.md" ]] || die "no WASM semantics at $wasm_checkout (set WASM_SEMANTICS_CHECKOUT)"
[[ -d "$builtin" ]] || die "no K builtin directory at $k_checkout (set K_CHECKOUT)"
reference_require_git_pin WASM "$wasm_checkout" "$WASM_REFERENCE_REVISION"
reference_require_git_pin K "$k_checkout" "$K_REFERENCE_REVISION"

# One line per selected case: kind, name, and for a proof its two modules.
entries=$(python3 - "$manifest" "${cases[@]}" <<'EOF'
import sys, tomllib
with open(sys.argv[1], "rb") as manifest:
    loaded = tomllib.load(manifest)
known = {case["name"]: ("program", case) for case in loaded["program"]}
known |= {case["name"]: ("proof", case) for case in loaded["proof"]}
selected = sys.argv[2:] or list(known)
unknown = [name for name in selected if name not in known]
if unknown:
    sys.exit(f"error: unknown case {' '.join(unknown)}; cases: {' '.join(known)}")
for name in selected:
    kind, case = known[name]
    print("\t".join([kind, name, case.get("module", ""), case.get("definition_module", "")]))
EOF
) || exit 2

if [[ -z "$work" ]]; then
  work=$(mktemp -d "${TMPDIR:-/tmp}/k-rust-wasm-execution.XXXXXX")
  remove_work=true
else
  mkdir -p "$work"
  work=$(cd "$work" && pwd)
  remove_work=false
fi

if [[ -n "${KRUST_BIN:-}" ]]; then
  krust=$KRUST_BIN
else
  reference_announce_krust_gate_build
  cargo build --quiet --release "${krust_gate_cargo_args[@]}" --manifest-path "$workspace/Cargo.toml" \
    -p k-rust --bin krust
  krust=$krust_gate_binary
fi
[[ -x "$krust" ]] || die "no krust executable at $krust"

# Runs one case: TIMEOUT NAME ARGUMENT..., with standard input closed so that a definition that
# reads $STDIN gets end of file instead of the caller's terminal or pipe.
run_case() {
  local limit=$1 name=$2 output="$work/${2//\//-}"
  local started finished status=0
  shift 2
  started=$(date +%s%N)
  timeout -s INT -k 10 "$limit" "$krust" "$@" </dev/null >"$output.stdout" 2>"$output.stderr" || status=$?
  finished=$(date +%s%N)
  echo "$status" >"$output.exit"
  echo $(((finished - started) / 1000000)) >"$output.milliseconds"
}

# The programs are sentences of the test language, whose grammar is WASM-TEST-SYNTAX. Each
# proof compiles its own spec module in process.
if grep -q '^program' <<<"$entries"; then
  echo "[wasm] compiling test.md (WASM-TEST) with $krust"
  "$krust" kcompile "$semantics/test.md" --main-module WASM-TEST --syntax-module WASM-TEST-SYNTAX \
    --backend rust --output-directory "$work/definition" --builtin-directory "$builtin" \
    </dev/null >"$work/kcompile.log" 2>&1 \
    || die "compiling WASM failed; see $work/kcompile.log"
fi

while IFS=$'\t' read -r kind name module definition_module; do
  case "$kind" in
    program)
      run_case "$program_timeout" "$name" krun --definition "$work/definition" --sort Stmts \
        "$wasm_checkout/tests/$name.wast"
      ;;
    proof)
      run_case "$proof_timeout" "$name" kprove "$wasm_checkout/tests/$name-spec.k" \
        --main-module "$module" --definition-module "$definition_module" -I "$semantics" \
        --builtin-directory "$builtin"
      ;;
  esac
done <<<"$entries"

status=0
python3 - "$manifest" "$success_configuration" "$work" "$update" "${cases[@]}" <<'EOF' || status=$?
import difflib, hashlib, re, sys, tomllib
from pathlib import Path

manifest_path, success_path, work = Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3])
update, selected = sys.argv[4] == "true", sys.argv[5:]
text = manifest_path.read_text()
loaded = tomllib.loads(text)
success = success_path.read_bytes()
cases = [("program", case) for case in loaded["program"]] + [("proof", case) for case in loaded["proof"]]
selected = set(selected or [case["name"] for _, case in cases])


def measure(kind, name):
    def output(suffix):
        return (work / (name.replace("/", "-") + suffix)).read_bytes()

    stdout = output(".stdout")
    result = {"exit": int(output(".exit")), "stderr": output(".stderr").decode()}
    if kind == "program":
        result["stdout"] = "success" if stdout == success else (
            f"sha256:{hashlib.sha256(stdout).hexdigest()} ({len(stdout)} bytes)")
    else:
        lines = stdout.decode().splitlines()
        result["verdict"] = "".join(line + "\n" for line in lines if re.match(r"^ {0,2}\S", line))
    seconds = int(output(".milliseconds")) / 1000
    return result, stdout, seconds


def toml_string(value):
    if "\n" in value:
        return '"""\n' + value.replace("\\", "\\\\").replace('"""', '\\"""') + '"""'
    return '"' + value.replace("\\", "\\\\").replace('"', '\\"') + '"'


if update:
    header = []
    for line in text.splitlines(keepends=True):
        if not line.startswith("#"):
            break
        header.append(line)
    out = header
    for kind, case in cases:
        if case["name"] in selected:
            case = {**case, **measure(kind, case["name"])[0]}
        out.append(f"\n[[{kind}]]\n")
        for key, value in case.items():
            out.append(f"{key} = {value if isinstance(value, int) else toml_string(value)}\n")
    manifest_path.write_text("".join(out))
    print(f"updated {len(selected)} cases in {manifest_path}")
    sys.exit(0)

differences = 0
for kind, case in cases:
    name = case["name"]
    if name not in selected:
        continue
    measured, stdout, seconds = measure(kind, name)
    differing = [key for key in measured if measured[key] != case.get(key)]
    if not differing:
        if kind == "program":
            shown = measured["stdout"]
        else:
            statuses = re.findall(r"^claim .*?: (\w+)", measured["verdict"], re.MULTILINE)
            shown = ", ".join(f"{statuses.count(s)} {s}" for s in sorted(set(statuses)))
        print(f"{name}: ok, exit {measured['exit']}, {shown} ({seconds:.1f} s)")
        continue
    differences += 1
    print(f"{name}: DIFFERS ({seconds:.1f} s)")
    if measured["exit"] == 124:
        print("  timed out")
    for key in differing:
        expected, actual = str(case.get(key)), str(measured[key])
        if "\n" in expected + actual or len(expected + actual) > 100:
            print(f"  {key}:")
            for line in difflib.unified_diff(expected.splitlines(), actual.splitlines(),
                                             "expected", "measured", lineterm="", n=1):
                print(f"    {line}")
        else:
            print(f"  {key}: expected {expected}, measured {actual}")
    if (kind == "program" and case.get("stdout") == "success" and measured["stdout"] != "success"
            and stdout):
        diff = list(difflib.unified_diff(success.decode().splitlines(), stdout.decode().splitlines(),
                                         "success", "measured", lineterm="", n=1))
        for line in diff[:40]:
            print(f"    {line}")
        if len(diff) > 40:
            print(f"    ... {len(diff) - 40} more diff lines")
print(f"{len(selected) - differences} of {len(selected)} cases as recorded")
sys.exit(3 if differences else 0)
EOF

if ((status == 0)) && [[ "$remove_work" == true ]]; then
  find "$work" -depth -delete
elif ((status != 0)); then
  echo "outputs kept in $work"
fi
exit "$status"
