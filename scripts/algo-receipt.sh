#!/usr/bin/env bash
set -euo pipefail

# Record algorithm cost receipts for the workloads of scripts/algo-workloads.toml: counters,
# timings, a trace aggregate, wall time and peak RSS, the output check, and the algo-graph join.

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
manifest="$workspace/scripts/algo-workloads.toml"
pins_manifest="$workspace/scripts/reference-differential.toml"
original_args=("$@")

KRUST_BIN=${KRUST_BIN:-"$workspace/target/profiling/krust"}
KRUST_FEATURES=${KRUST_FEATURES:-cli,measure}
ALGO_RECEIPT_WORK=${ALGO_RECEIPT_WORK:-"$workspace/target/algo-receipts/work"}
ALGO_RECEIPT_HEAVY_MIN_AVAILABLE_GIB=${ALGO_RECEIPT_HEAVY_MIN_AVAILABLE_GIB:-24}
ALGO_RECEIPT_HEAVY_WAIT_SECONDS=${ALGO_RECEIPT_HEAVY_WAIT_SECONDS:-600}
ALGO_RECEIPT_STDOUT_KEEP_BYTES=${ALGO_RECEIPT_STDOUT_KEEP_BYTES:-1048576}

usage() {
  cat <<'EOF'
Usage: scripts/algo-receipt.sh --workload NAME [--param VALUE] [--repeat N] [--output DIR] [OPTIONS]
       scripts/algo-receipt.sh --list

Record algorithm cost receipts for one workload of scripts/algo-workloads.toml.

Each receipt runs the workload's prepare steps (unmeasured; their outputs are kept below
ALGO_RECEIPT_WORK and reused while the krust binary is unchanged), then the measured command
twice:
  measured  with --timings and KRUST_COUNTERS, through scripts/conformance/measure.py, for the
            wall time, peak RSS, exit status, stdout that the output check reads, timings.json
            and counters.json;
  traced    with --trace-aggregate and KRUST_COUNTERS, for trace-aggregate.json, the per
            algorithm and per phase span aggregate that algo-graph join reads.
Span instrumentation costs time per span (about 60 percent on a krun whose backend spans open
once per call), so the wall time and peak RSS come from the measured run; the traced run's wall
time is recorded next to it. The counters of both runs must be equal, since krust is
deterministic on these inputs; the receipt records the comparison.

A receipt directory holds metadata.json, command.txt, timings.json, counters.json,
trace-aggregate.json, the measured and traced runs' stdout, stderr and meta.toml, graph.toml
(algo-graph graph -o), and join.toml and overlay.mmd (algo-graph join). A stdout larger than
ALGO_RECEIPT_STDOUT_KEEP_BYTES (default 1 MiB) is replaced by its first 64 KiB
(NAME.stdout.head) after the check; metadata.json records its size and SHA-256.
Receipts go to DIR/<param value or base>/rep-<k>, k = 1..N. With --atlas FILE, each recorded
receipt is also indexed in FILE (see below).

A ladder workload records every ladder value in order unless --param names one. A measured run
slower than the ladder's stop_seconds is killed and ends the ladder; that value and the later
ones are reported as not reached.

Options:
  --workload NAME   Workload name from scripts/algo-workloads.toml (see --list)
  --param VALUE     One ladder value (ladder workloads only)
  --repeat N        Receipts per workload and value (default: 1)
  --output DIR      Workload directory (default: target/algo-receipts/COMMIT/NAME)
  --atlas FILE      Add the recorded receipts to this atlas.toml (created when absent; its
                    commit must be the checkout's)
  --allow-dirty     Record from a checkout with tracked modifications (metadata says so)
  --allow-unpinned  Permit reference checkouts other than the manifest pins
  --list            Print the workloads and exit
  --dry-run         Print the resolved commands without running them
  -h, --help        Show this help

Environment:
  KRUST_BIN         krust built with the profiling profile and the measure feature
                    (default: target/profiling/krust):
                      with-z3-static-4.16.0 cargo build --profile profiling -p k-rust \
                        --no-default-features --features cli,measure --bin krust --locked
  KRUST_FEATURES    The features KRUST_BIN was built with, recorded in the metadata
                    (default: cli,measure)
  ALGO_GRAPH        algo-graph binary (default: cargo run --release -p algo-graph)
  ALGO_RECEIPT_WORK Work root for prepared definitions and run scratch
                    (default: target/algo-receipts/work)
  K_CHECKOUT, IMP_SEMANTICS_CHECKOUT, WASM_SEMANTICS_CHECKOUT, EVM_SEMANTICS_CHECKOUT,
  MIR_SEMANTICS_CHECKOUT
                    Reference checkouts (defaults: the workspace symlinks, as
                    scripts/reference-manifest.py)

Heavy workloads run the whole job under scripts/reference-memory-guard.sh (a 16 GiB user
scope, or the workload's memory_gib; or the RLIMIT_AS fallback 8 GiB above it), and first wait
until /proc/meminfo reports ALGO_RECEIPT_HEAVY_MIN_AVAILABLE_GIB (default 24, and at least
memory_gib + 8) GiB available; after
ALGO_RECEIPT_HEAVY_WAIT_SECONDS (default 600) they exit 4 without recording.

atlas.toml: schema = 1, commit = the full krust revision, and one [[receipt]] per receipt with
workload, command, param_name and param (ladder workloads only), repeat, join (the join.toml
path relative to the atlas), wall_seconds and peak_rss_kib of the measured run. Recording a
receipt again replaces its entry.

Requires: python3 (3.11 or later), jq, git.
EOF
}

fail() {
  echo "error: $*" >&2
  exit 2
}

# The manifest helper: resolves a workload, evaluates output checks, and updates atlas.toml.
helper() {
  python3 - "$@" <<'PY'
import ast, json, os, re, subprocess, sys, tomllib
from pathlib import Path
from string import Template

workspace = Path(os.environ["ALGO_RECEIPT_WORKSPACE"])
roots = {
    "workspace": str(workspace),
    "k": os.environ.get("K_CHECKOUT", str(workspace / "k")),
    "imp": os.environ.get("IMP_SEMANTICS_CHECKOUT", str(workspace / "imp-semantics")),
    "wasm": os.environ.get("WASM_SEMANTICS_CHECKOUT", str(workspace / "wasm-semantics")),
    "evm": os.environ.get("EVM_SEMANTICS_CHECKOUT", str(workspace / "evm-semantics")),
    "mir": os.environ.get("MIR_SEMANTICS_CHECKOUT", str(workspace / "mir-semantics")),
}
roots["builtin"] = roots["k"] + "/k-distribution/include/kframework/builtin"
pin_checkouts = {
    "k": roots["k"],
    "imp": roots["imp"],
    "wasm": roots["wasm"],
    "mir": roots["mir"],
    "kevm": roots["evm"],
    "kevm-plugin": roots["evm"] + "/kevm-pyk/src/kevm_pyk/kproj/plugin",
}


def load(path):
    with open(path, "rb") as source:
        return tomllib.load(source)


def expand(value, variables, strict=True):
    if isinstance(value, str):
        template = Template(value)
        return template.substitute(variables) if strict else template.safe_substitute(variables)
    if isinstance(value, list):
        return [expand(item, variables, strict) for item in value]
    if isinstance(value, dict):
        return {key: expand(item, variables, strict) for key, item in value.items()}
    return value


def evaluate(expression, name, value):
    """An integer expression over the ladder parameter: literals, the parameter, + - * // %."""
    tree = ast.parse(expression, mode="eval")

    def walk(node):
        if isinstance(node, ast.Expression):
            return walk(node.body)
        if isinstance(node, ast.Constant) and isinstance(node.value, int):
            return node.value
        if isinstance(node, ast.Name) and node.id == name:
            return value
        if isinstance(node, ast.BinOp):
            left, right = walk(node.left), walk(node.right)
            operations = {ast.Add: int.__add__, ast.Sub: int.__sub__, ast.Mult: int.__mul__,
                          ast.FloorDiv: int.__floordiv__, ast.Mod: int.__mod__}
            if type(node.op) in operations:
                return operations[type(node.op)](left, right)
        raise ValueError(f"unsupported expect expression: {expression}")

    return walk(tree)


def expected_integer(path):
    """The integer that a K `--pattern "<k> V:K </k>"` output binds: `V:K #Equals <int> ~> .K`."""
    text = Path(path).read_text()
    found = re.search(r"V:K\s*#Equals\s*(-?[0-9]+)\s*~>\s*\.K", text)
    if not found or text.count("#Equals") != 1:
        raise ValueError(f"{path} does not bind V to one integer")
    return int(found.group(1))


def workload(manifest, name):
    for entry in manifest["workload"]:
        if entry["name"] == name:
            return entry
    names = ", ".join(entry["name"] for entry in manifest["workload"])
    raise SystemExit(f"error: unknown workload {name}; workloads: {names}")


def resolve(name, param, prepared, run, input_path, shape=False):
    manifest = load(sys.argv[2])
    entry = workload(manifest, name)
    ladder = entry.get("ladder")
    if shape and ladder is not None:
        param = str(ladder["values"][0])
    if ladder is None and param != "":
        raise SystemExit(f"error: {name} has no ladder; --param does not apply")
    if ladder is not None and param == "":
        raise SystemExit(f"error: {name} is a ladder workload; name a --param value")
    variables = dict(roots, prepared=prepared, run=run, input=input_path)
    param_value = None
    if ladder is not None:
        param_value = int(param)
        if param_value not in ladder["values"]:
            raise SystemExit(f"error: {param} is not a value of {name}'s ladder {ladder['values']}")
        variables[ladder["param"]] = str(param_value)
    steps = {step["name"]: step for step in manifest.get("prepare", [])}
    prepare = []
    for step_name in entry.get("prepare", []):
        step = steps.get(step_name)
        if step is None:
            raise SystemExit(f"error: {name} names an unknown prepare step {step_name}")
        prepare.append(expand(step, variables))
    check = expand(entry.get("check", {}), variables, strict=False)
    expect = None
    if "expect" in check:
        expect = evaluate(check["expect"], ladder["param"], param_value) if ladder else int(check["expect"])
    elif "expect_out" in check:
        expect = expected_integer(check["expect_out"])
    if expect is not None:
        variables["expect"] = str(expect)
    check = expand(check, variables)
    check["expect"] = expect
    pins_manifest = load(sys.argv[3])
    pins = []
    for pin in entry.get("pins", []):
        checkout = pin_checkouts[pin]
        actual = subprocess.run(["git", "-C", checkout, "rev-parse", "HEAD"],
                                capture_output=True, text=True)
        pins.append({"name": pin, "checkout": checkout,
                     "pinned": pins_manifest["reference"][pin]["revision"],
                     "actual": actual.stdout.strip() if actual.returncode == 0 else None})
    result = {
        "name": entry["name"],
        "command": entry["command"],
        "weight": entry["weight"],
        "memory_gib": entry.get("memory_gib"),
        "args": expand(entry["args"], variables),
        "prepare": prepare,
        "check": check,
        "pins": pins,
        "input": expand(ladder["input"], variables) if ladder else None,
        "param_name": ladder["param"] if ladder else None,
        "param": param_value,
        "ladder_values": ladder["values"] if ladder else [],
        "stop_seconds": ladder.get("stop_seconds") if ladder else None,
    }
    if result["command"] not in ("kcompile", "kprove", "krun"):
        raise SystemExit(f"error: {name} has unknown command {result['command']}")
    if result["weight"] not in ("light", "heavy"):
        raise SystemExit(f"error: {name} has unknown weight {result['weight']}")
    if result["memory_gib"] is not None and result["weight"] != "heavy":
        raise SystemExit(f"error: {name} sets memory_gib but is not heavy")
    print(json.dumps(result))


def check_output(check_path, stdout_path, exit_code):
    check = json.loads(Path(check_path).read_text())
    stdout = Path(stdout_path).read_text(errors="replace")
    squeezed = re.sub(r"\s+", "", stdout)
    results = []

    def record(kind, detail, passed):
        results.append({"kind": kind, "detail": detail, "passed": passed})

    expected_exit = check.get("exit", 0)
    record("exit", str(expected_exit), int(exit_code) == expected_exit)
    for text in check.get("stdout", []):
        record("stdout contains", text, text in stdout)
    for text in check.get("stdout_squeezed", []):
        record("stdout contains, whitespace removed", text, re.sub(r"\s+", "", text) in squeezed)
    for text in check.get("stdout_absent", []):
        record("stdout lacks", text, text not in stdout)
    for path in check.get("files", []):
        record("file is non-empty", path, os.path.isfile(path) and os.path.getsize(path) > 0)
    passed = all(result["passed"] for result in results)
    print(json.dumps({"passed": passed, "expect": check.get("expect"), "checks": results}))


def update_atlas(atlas_path, commit, entries_path):
    atlas = Path(atlas_path)
    receipts = []
    if atlas.exists():
        existing = load(atlas)
        if existing.get("commit") != commit:
            raise SystemExit(f"error: {atlas} indexes commit {existing.get('commit')}, not {commit}")
        receipts = existing.get("receipt", [])
    new = [json.loads(line) for line in Path(entries_path).read_text().splitlines() if line]
    key = lambda receipt: (receipt["workload"], receipt.get("param"), receipt["repeat"])
    replaced = {key(receipt) for receipt in new}
    receipts = [receipt for receipt in receipts if key(receipt) not in replaced] + new
    receipts.sort(key=lambda receipt: (receipt["workload"], receipt.get("param", -1), receipt["repeat"]))

    def value(item):
        if isinstance(item, str):
            return json.dumps(item)
        return repr(item)

    lines = ["schema = 1", f"commit = {json.dumps(commit)}"]
    order = ["workload", "command", "param_name", "param", "repeat", "join", "wall_seconds", "peak_rss_kib"]
    for receipt in receipts:
        lines += ["", "[[receipt]]"]
        lines += [f"{field} = {value(receipt[field])}" for field in order if receipt.get(field) is not None]
    atlas.parent.mkdir(parents=True, exist_ok=True)
    atlas.write_text("\n".join(lines) + "\n")


def list_workloads():
    manifest = load(sys.argv[2])
    for entry in manifest["workload"]:
        ladder = entry.get("ladder")
        values = f"  {ladder['param']} = {', '.join(map(str, ladder['values']))}" if ladder else ""
        print(f"{entry['name']:<30} {entry['command']:<9} {entry['weight']:<6}{values}")


action = sys.argv[1]
if action == "resolve":
    resolve(*sys.argv[4:9])
elif action == "shape":
    resolve(sys.argv[4], "", "${prepared}", "${run}", "${input}", shape=True)
elif action == "check":
    check_output(*sys.argv[2:5])
elif action == "atlas":
    update_atlas(*sys.argv[2:5])
elif action == "list":
    list_workloads()
else:
    raise SystemExit(f"error: unknown helper action {action}")
PY
}

shell_command() {
  local output=
  printf -v output '%q ' "$@"
  printf '%s' "${output% }"
}

measure_field() {
  sed -n "s/^$2 = //p" "$1.meta.toml"
}

# Print one labelled command to command.txt, with its working directory.
log_command() {
  local label=$1
  shift
  printf '%s (cwd %s): %s\n' "$label" "$PWD" "$*" >>"$receipt/command.txt"
}

workload=
param=
repeat=1
output=
atlas=
allow_dirty=0
allow_unpinned=0
list=0
dry_run=0

while (($#)); do
  case "$1" in
    --workload) workload=${2:?}; shift 2 ;;
    --param) param=${2:?}; shift 2 ;;
    --repeat) repeat=${2:?}; shift 2 ;;
    --output) output=${2:?}; shift 2 ;;
    --atlas) atlas=${2:?}; shift 2 ;;
    --allow-dirty) allow_dirty=1; shift ;;
    --allow-unpinned) allow_unpinned=1; shift ;;
    --list) list=1; shift ;;
    --dry-run) dry_run=1; shift ;;
    -h|--help) usage; exit ;;
    *) fail "unknown option: $1" ;;
  esac
done

export ALGO_RECEIPT_WORKSPACE=$workspace
command -v python3 >/dev/null 2>&1 || fail "python3 is required"
if [[ "$list" == 1 ]]; then
  helper list "$manifest"
  exit
fi
[[ -n "$workload" ]] || fail "--workload is required (see --list)"
[[ "$repeat" =~ ^[1-9][0-9]*$ ]] || fail "--repeat must be a positive integer"
command -v jq >/dev/null 2>&1 || fail "jq is required"

# The workload's shape: its weight, command, pins, and ladder values.
shape=$(helper shape "$manifest" "$pins_manifest" "$workload")
weight=$(jq -r .weight <<<"$shape")
memory_gib=$(jq -r '.memory_gib // empty' <<<"$shape")
command_kind=$(jq -r .command <<<"$shape")
mapfile -t ladder_values < <(jq -r '.ladder_values[]' <<<"$shape")
if ((${#ladder_values[@]})); then
  params=("${ladder_values[@]}")
  if [[ -n "$param" ]]; then
    printf '%s\n' "${ladder_values[@]}" | grep -Fxq -- "$param" \
      || fail "$param is not a ladder value of $workload (${ladder_values[*]})"
    params=("$param")
  fi
else
  [[ -z "$param" ]] || fail "$workload has no ladder; --param does not apply"
  params=("")
fi

commit=$(git -C "$workspace" rev-parse HEAD)
dirty=false
[[ -z "$(git -C "$workspace" status --porcelain --untracked-files=no)" ]] || dirty=true
if [[ -z "$output" ]]; then
  output="$workspace/target/algo-receipts/${commit:0:8}/$workload"
elif [[ "$output" != /* ]]; then
  output="$PWD/$output"
fi
[[ -z "$atlas" || "$atlas" == /* ]] || atlas="$PWD/$atlas"
[[ "$ALGO_RECEIPT_WORK" == /* ]] || ALGO_RECEIPT_WORK="$workspace/$ALGO_RECEIPT_WORK"
if [[ -n "${ALGO_GRAPH:-}" ]]; then
  algo_graph=("$ALGO_GRAPH")
else
  algo_graph=(cargo run --quiet --release --manifest-path "$workspace/Cargo.toml" -p algo-graph --)
fi

binary_digest=unbuilt
[[ ! -f "$KRUST_BIN" ]] || binary_digest=$(sha256sum "$KRUST_BIN" | cut -d' ' -f1)
prepared="$ALGO_RECEIPT_WORK/prepared/${binary_digest:0:16}"
run="$ALGO_RECEIPT_WORK/run/$workload"

resolve_param() {
  helper resolve "$manifest" "$pins_manifest" "$workload" "$1" "$prepared" "$run" "$run-input/$workload.${2:-input}"
}

input_extension() {
  case "$workload" in
    imp-*) echo imp ;;
    fun-*) echo fun ;;
    *) echo input ;;
  esac
}

if [[ "$dry_run" == 1 ]]; then
  for value in "${params[@]}"; do
    resolved=$(resolve_param "$value" "$(input_extension)")
    echo "[$workload${value:+ $(jq -r .param_name <<<"$resolved")=$value}] $weight"
    while IFS= read -r step; do
      mapfile -t step_args < <(jq -r '.args[]' <<<"$step")
      printf 'prepare (unless %s exists): %s\n' "$(jq -r .creates <<<"$step")" \
        "$(shell_command "$KRUST_BIN" "$(jq -r .command <<<"$step")" "${step_args[@]}")"
    done < <(jq -c '.prepare[]' <<<"$resolved")
    [[ "$(jq -r .input <<<"$resolved")" == null ]] \
      || printf 'input: %s (the ladder template at %s)\n' "$run-input/$workload.$(input_extension)" "$(jq -r .param_name <<<"$resolved")=$value"
    mapfile -t args < <(jq -r '.args[]' <<<"$resolved")
    printf 'measured: KRUST_COUNTERS=%q %s < /dev/null\n' "RECEIPT/counters.json" \
      "$(shell_command "$KRUST_BIN" "$command_kind" "${args[@]}" --timings RECEIPT/timings.json)"
    printf 'traced: KRUST_COUNTERS=%q %s < /dev/null\n' "RECEIPT/counters.traced.json" \
      "$(shell_command "$KRUST_BIN" "$command_kind" "${args[@]}" --trace-aggregate RECEIPT/trace-aggregate.json)"
    printf 'check: %s\n' "$(jq -c .check <<<"$resolved")"
    [[ "$weight" != heavy ]] || echo "guard: the whole job runs under scripts/reference-memory-guard.sh${memory_gib:+ with a $memory_gib GiB scope}"
  done
  exit
fi

if [[ "$weight" == heavy ]]; then
  if [[ -n "$memory_gib" ]]; then
    # The workload's own scope; the fallback's address-space limit and the availability wait
    # keep the guard's 8 GiB of headroom above it.
    export REFERENCE_DIFFERENTIAL_JOB_MEMORY_HIGH_KIB=$((memory_gib * 1024 * 1024))
    export REFERENCE_DIFFERENTIAL_JOB_MEMORY_MAX_KIB=$((memory_gib * 1024 * 1024))
    export REFERENCE_DIFFERENTIAL_JOB_FALLBACK_VIRTUAL_MEMORY_KIB=$(((memory_gib + 8) * 1024 * 1024))
    ((ALGO_RECEIPT_HEAVY_MIN_AVAILABLE_GIB >= memory_gib + 8)) \
      || ALGO_RECEIPT_HEAVY_MIN_AVAILABLE_GIB=$((memory_gib + 8))
  fi
  # shellcheck disable=SC1091  # followed by shellcheck -x
  source "$workspace/scripts/reference-memory-guard.sh"
  reference_enter_whole_job "${original_args[@]}"
fi

[[ -x "$KRUST_BIN" ]] || fail "krust binary is missing: $KRUST_BIN (see --help for the build command)"
if command -v readelf >/dev/null 2>&1; then
  readelf -S "$KRUST_BIN" | grep -q '\.debug_line' || fail "KRUST_BIN has no line tables; build with --profile profiling"
fi
"$KRUST_BIN" "$command_kind" --help | grep -q -- --trace-aggregate \
  || fail "KRUST_BIN has no --trace-aggregate option; rebuild it from this checkout"
if [[ "$dirty" == true && "$allow_dirty" != 1 ]]; then
  fail "the checkout has tracked modifications; commit them or pass --allow-dirty"
fi
while IFS=$'\t' read -r pin checkout revision actual; do
  [[ -e "$checkout/.git" ]] || fail "$pin checkout is missing: $checkout"
  if [[ "$actual" != "$revision" && "$allow_unpinned" != 1 ]]; then
    fail "$pin checkout is $actual; expected $revision (use --allow-unpinned only for exploratory runs)"
  fi
  if [[ -n "$(git -C "$checkout" status --short --untracked-files=no)" && "$allow_unpinned" != 1 ]]; then
    fail "$pin checkout has tracked modifications: $checkout"
  fi
done < <(jq -r '.pins[] | [.name, .checkout, .pinned, .actual // "missing"] | @tsv' <<<"$shape")

if [[ "$weight" == heavy ]]; then
  waited=0
  minimum_kib=$((ALGO_RECEIPT_HEAVY_MIN_AVAILABLE_GIB * 1024 * 1024))
  while available_kib=$(awk '/^MemAvailable:/ { print $2 }' /proc/meminfo) && ((available_kib < minimum_kib)); do
    if ((waited >= ALGO_RECEIPT_HEAVY_WAIT_SECONDS)); then
      echo "skipped: $((available_kib / 1024 / 1024)) GiB available after ${waited} s; $workload needs $ALGO_RECEIPT_HEAVY_MIN_AVAILABLE_GIB GiB" >&2
      exit 4
    fi
    echo "[$workload] waiting: $((available_kib / 1024 / 1024)) GiB available, $ALGO_RECEIPT_HEAVY_MIN_AVAILABLE_GIB GiB needed" >&2
    sleep 30
    waited=$((waited + 30))
  done
fi

mkdir -p "$output" "$prepared" "$run-input"
graph="$ALGO_RECEIPT_WORK/graph-${commit:0:12}.toml"
if [[ ! -f "$graph" || "$dirty" == true ]]; then
  "${algo_graph[@]}" --root "$workspace" graph -o "$graph" >/dev/null 2>&1 \
    || fail "algo-graph graph failed; run ${algo_graph[*]} --root $workspace graph -o $graph"
fi

cpu=unknown
memory=unknown
if [[ -r /proc/cpuinfo ]]; then
  cpu=$(awk -F: '/model name/ { sub(/^[[:space:]]*/, "", $2); print $2; exit }' /proc/cpuinfo)
  memory=$(awk '/MemTotal/ { print $2 * 1024; exit }' /proc/meminfo)
fi
krust_version=$("$KRUST_BIN" --version)
rustc_version=$(rustc --version 2>/dev/null || echo unavailable)
atlas_entries=$(mktemp)
trap 'rm -f "$atlas_entries"' EXIT
not_reached=()

# Record one receipt into $receipt; returns 3 when a ladder run exceeds its stop time.
record_receipt() {
  local value=$1
  local index=$2
  local resolved step creates timeout traced_timeout
  local -a step_args args
  resolved=$(resolve_param "$value" "$(input_extension)")
  : >"$receipt/command.txt"
  while IFS= read -r step; do
    creates=$(jq -r .creates <<<"$step")
    mapfile -t step_args < <(jq -r '.args[]' <<<"$step")
    log_command prepare "$(shell_command "$KRUST_BIN" "$(jq -r .command <<<"$step")" "${step_args[@]}")${creates:+ (skipped when $creates exists)}"
    if [[ ! -e "$creates" ]]; then
      echo "[$workload] preparing $(jq -r .name <<<"$step")"
      "$KRUST_BIN" "$(jq -r .command <<<"$step")" "${step_args[@]}" </dev/null >"$receipt/prepare.log" 2>&1 \
        || { tail -n 5 "$receipt/prepare.log" >&2; fail "prepare step $(jq -r .name <<<"$step") failed"; }
      [[ -e "$creates" ]] || fail "prepare step $(jq -r .name <<<"$step") did not create $creates"
    fi
  done < <(jq -c '.prepare[]' <<<"$resolved")
  rm -f "$receipt/prepare.log"
  if [[ "$(jq -r .input <<<"$resolved")" != null ]]; then
    jq -j .input <<<"$resolved" >"$run-input/$workload.$(input_extension)"
    cp "$run-input/$workload.$(input_extension)" "$receipt/input.$(input_extension)"
    printf 'input: %s written from the ladder template with %s=%s (copy: input.%s)\n' \
      "$run-input/$workload.$(input_extension)" "$(jq -r .param_name <<<"$resolved")" "$value" "$(input_extension)" >>"$receipt/command.txt"
  fi
  jq .check <<<"$resolved" >"$receipt/check.json"
  mapfile -t args < <(jq -r '.args[]' <<<"$resolved")
  timeout=()
  traced_timeout=()
  if [[ "$(jq -r .stop_seconds <<<"$resolved")" != null ]]; then
    timeout=(--timeout "$(jq -r .stop_seconds <<<"$resolved")")
    traced_timeout=(--timeout "$(($(jq -r .stop_seconds <<<"$resolved") * 3))")
  fi

  local load_average
  load_average=$(cut -d' ' -f1-3 /proc/loadavg)
  local timestamp
  timestamp=$(date -u +%Y-%m-%dT%H:%M:%SZ)
  rm -rf "$run" && mkdir -p "$run"
  log_command measured "KRUST_COUNTERS=$(shell_command "$receipt/counters.json") $(shell_command python3 "$workspace/scripts/conformance/measure.py" --log "$receipt/measured" "${timeout[@]}" -- "$KRUST_BIN" "$command_kind" "${args[@]}" --timings "$receipt/timings.json") < /dev/null"
  echo "[$workload${value:+ $value} rep-$index] measured run"
  KRUST_COUNTERS="$receipt/counters.json" python3 "$workspace/scripts/conformance/measure.py" \
    --log "$receipt/measured" "${timeout[@]}" -- \
    "$KRUST_BIN" "$command_kind" "${args[@]}" --timings "$receipt/timings.json" </dev/null || true
  if [[ "$(measure_field "$receipt/measured" timed_out)" == true ]]; then
    echo "[$workload $value] the measured run exceeded $(jq -r .stop_seconds <<<"$resolved") s; the ladder stops" >&2
    return 3
  fi
  local exit_code
  exit_code=$(measure_field "$receipt/measured" exit_code)
  local check
  check=$(helper check "$receipt/check.json" "$receipt/measured.stdout" "$exit_code")
  local files_ok=true
  [[ -f "$receipt/counters.json" ]] || files_ok=false

  rm -rf "$run" && mkdir -p "$run"
  log_command traced "KRUST_COUNTERS=$(shell_command "$receipt/counters.traced.json") $(shell_command python3 "$workspace/scripts/conformance/measure.py" --log "$receipt/traced" "${traced_timeout[@]}" -- "$KRUST_BIN" "$command_kind" "${args[@]}" --trace-aggregate "$receipt/trace-aggregate.json") < /dev/null"
  echo "[$workload${value:+ $value} rep-$index] traced run"
  KRUST_COUNTERS="$receipt/counters.traced.json" python3 "$workspace/scripts/conformance/measure.py" \
    --log "$receipt/traced" "${traced_timeout[@]}" -- \
    "$KRUST_BIN" "$command_kind" "${args[@]}" --trace-aggregate "$receipt/trace-aggregate.json" </dev/null || true
  rm -rf "$run"
  local counters_match=false
  if [[ -f "$receipt/counters.json" && -f "$receipt/counters.traced.json" ]] \
    && cmp -s "$receipt/counters.json" "$receipt/counters.traced.json"; then
    counters_match=true
  fi
  # A result can be large (a FUN ladder run prints gigabytes); keep its digest and first
  # 64 KiB instead once the check has read it.
  local stdout_bytes stdout_sha256 stdout_match=false stdout_kept=true
  stdout_bytes=$(stat -c %s "$receipt/measured.stdout")
  stdout_sha256=$(sha256sum "$receipt/measured.stdout" | cut -d' ' -f1)
  ! cmp -s "$receipt/measured.stdout" "$receipt/traced.stdout" || stdout_match=true
  if ((stdout_bytes > ALGO_RECEIPT_STDOUT_KEEP_BYTES)); then
    stdout_kept=false
    for name in measured traced; do
      head -c 65536 "$receipt/$name.stdout" >"$receipt/$name.stdout.head"
      rm "$receipt/$name.stdout"
    done
  fi

  jq -n \
    --arg workload "$workload" \
    --arg command "$command_kind" \
    --arg weight "$weight" \
    --arg param_name "$(jq -r '.param_name // ""' <<<"$resolved")" \
    --arg param "$value" \
    --argjson repeat "$index" \
    --arg claim "$(jq -r '[.args as $a | range(0; $a | length) | select($a[.] == "--claim") | $a[. + 1]][0] // ""' <<<"$resolved")" \
    --arg timestamp "$timestamp" \
    --arg user "$(id -un)" \
    --arg system "$(uname -a)" \
    --arg kernel "$(uname -r)" \
    --arg cpu "$cpu" \
    --arg memory_bytes "$memory" \
    --arg load_average "$load_average" \
    --arg memory_available_kib "$(awk '/^MemAvailable:/ { print $2 }' /proc/meminfo)" \
    --arg guard "${REFERENCE_DIFFERENTIAL_JOB_GUARD_KIND:-none}" \
    --arg krust_revision "$commit" \
    --argjson krust_dirty "$dirty" \
    --argjson allow_dirty "$([[ "$allow_dirty" == 1 ]] && echo true || echo false)" \
    --argjson pins "$(jq -c .pins <<<"$shape")" \
    --arg krust_version "$krust_version" \
    --arg rustc_version "$rustc_version" \
    --arg krust_path "$KRUST_BIN" \
    --arg krust_sha256 "$binary_digest" \
    --arg features "$KRUST_FEATURES" \
    --argjson wall "$(measure_field "$receipt/measured" wall_seconds)" \
    --argjson rss "$(measure_field "$receipt/measured" peak_rss_kib)" \
    --argjson exit_code "$exit_code" \
    --argjson traced_wall "$(measure_field "$receipt/traced" wall_seconds)" \
    --argjson traced_rss "$(measure_field "$receipt/traced" peak_rss_kib)" \
    --argjson traced_exit "$(measure_field "$receipt/traced" exit_code)" \
    --argjson counters_match "$counters_match" \
    --argjson stdout_bytes "$stdout_bytes" \
    --arg stdout_sha256 "$stdout_sha256" \
    --argjson stdout_match "$stdout_match" \
    --argjson stdout_kept "$stdout_kept" \
    --argjson check "$check" \
    --argjson counters "$([[ -f "$receipt/counters.json" ]] && echo true || echo false)" \
    --argjson timings "$([[ -f "$receipt/timings.json" ]] && echo true || echo false)" \
    --argjson trace "$([[ -f "$receipt/trace-aggregate.json" ]] && echo true || echo false)" \
    --argjson timings_unattributed "$(if [[ -f "$receipt/timings.json" ]]; then jq -c '[.load_unattributed_seconds, .compile_unattributed_seconds, .write_unattributed_seconds] | map(select(type == "number")) | add // 0' "$receipt/timings.json"; else echo null; fi)" \
    '{
      workload: $workload,
      command: $command,
      weight: $weight,
      param_name: (if $param_name == "" then null else $param_name end),
      param: (if $param == "" then null else ($param | tonumber) end),
      repeat: $repeat,
      claim: (if $claim == "" then null else $claim end),
      timestamp: $timestamp,
      user: $user,
      host: {system: $system, kernel: $kernel, cpu: $cpu, memory_bytes: $memory_bytes},
      load_average: ($load_average | split(" ") | map(tonumber)),
      memory_available_kib: ($memory_available_kib | tonumber),
      memory_guard: $guard,
      revisions: {
        krust: $krust_revision, krust_dirty: $krust_dirty,
        k: ($pins | map(select(.name == "k"))[0].actual),
        semantics: ($pins | map(select(.name != "k" and .name != "kevm-plugin"))[0].actual),
        plugin: ($pins | map(select(.name == "kevm-plugin"))[0].actual)
      },
      allow_dirty: $allow_dirty,
      pins: $pins,
      tools: {krust: $krust_version, rustc: $rustc_version},
      binary: {path: $krust_path, sha256: $krust_sha256, retained: null},
      profile: "profiling",
      features: $features,
      sampling: null,
      wall_seconds: $wall,
      peak_rss_kib: $rss,
      unprofiled: {wall_seconds: $wall, peak_rss_kib: $rss, exit_code: $exit_code},
      traced: {wall_seconds: $traced_wall, peak_rss_kib: $traced_rss, exit_code: $traced_exit,
               trace_format: "krust-trace-aggregate/1", counters_match_measured: $counters_match,
               stdout_matches_measured: $stdout_match},
      stdout: {bytes: $stdout_bytes, sha256: $stdout_sha256, kept: $stdout_kept},
      profiled: null,
      output_check: $check,
      outputs: {counters_json: $counters, timings_json: $timings, trace_json: $trace,
                timings_unattributed_seconds: $timings_unattributed}
    }' >"$receipt/metadata.json"

  if [[ "$(jq -r .passed <<<"$check")" != true ]]; then
    echo "error: $workload${value:+ $value} rep-$index failed its output check:" >&2
    jq -r '.checks[] | select(.passed | not) | "  \(.kind): \(.detail)"' <<<"$check" >&2
    return 1
  fi
  [[ "$files_ok" == true ]] || { echo "error: no counters.json; KRUST_BIN lacks the measure feature" >&2; return 1; }
  [[ "$(measure_field "$receipt/traced" exit_code)" == "$exit_code" && -s "$receipt/trace-aggregate.json" ]] \
    || { echo "error: the traced run exited $(measure_field "$receipt/traced" exit_code) or wrote no aggregate" >&2; return 1; }
  [[ "$counters_match" == true ]] \
    || { echo "error: the traced run's counters differ from the measured run's" >&2; return 1; }

  cp "$graph" "$receipt/graph.toml"
  log_command graph "$(shell_command "${algo_graph[@]}" --root "$workspace" graph -o "$graph") (copied to graph.toml)"
  log_command join "$(shell_command "${algo_graph[@]}" --root "$output_root" join --graph "$receipt/graph.toml" --trace "$receipt/trace-aggregate.json" --receipt "$receipt" -o "$receipt/join.toml" --overlay "$receipt/overlay.mmd")"
  "${algo_graph[@]}" --root "$output_root" join --graph "$receipt/graph.toml" \
    --trace "$receipt/trace-aggregate.json" --receipt "$receipt" \
    -o "$receipt/join.toml" --overlay "$receipt/overlay.mmd" >/dev/null
  if [[ -n "$atlas" ]]; then
    jq -n -c \
      --arg workload "$workload" \
      --arg command "$command_kind" \
      --arg param_name "$(jq -r '.param_name // ""' <<<"$resolved")" \
      --arg param "$value" \
      --argjson repeat "$index" \
      --arg join "$(realpath --relative-to="$(dirname "$atlas")" "$receipt/join.toml")" \
      --argjson wall "$(measure_field "$receipt/measured" wall_seconds)" \
      --argjson rss "$(measure_field "$receipt/measured" peak_rss_kib)" \
      '{workload: $workload, command: $command,
        param_name: (if $param_name == "" then null else $param_name end),
        param: (if $param == "" then null else ($param | tonumber) end),
        repeat: $repeat, join: $join, wall_seconds: $wall, peak_rss_kib: $rss}' >>"$atlas_entries"
  fi
  echo "[$workload${value:+ $value} rep-$index] $(measure_field "$receipt/measured" wall_seconds) s, $(measure_field "$receipt/measured" peak_rss_mib) MiB; traced $(measure_field "$receipt/traced" wall_seconds) s; $receipt"
}

# The join records each receipt directory relative to the parent of the workload directory, so
# its label is WORKLOAD/VALUE/rep-K wherever the receipts are kept.
output_root=$(dirname "$output")
status=0
for position in "${!params[@]}"; do
  value=${params[$position]}
  for ((index = 1; index <= repeat; index++)); do
    receipt="$output/${value:-base}/rep-$index"
    rm -rf "$receipt"
    mkdir -p "$receipt"
    set +e
    record_receipt "$value" "$index"
    outcome=$?
    set -e
    if ((outcome == 3)); then
      rm -rf "$receipt"
      not_reached=("${params[@]:position}")
      break 2
    fi
    ((outcome == 0)) || { status=1; break 2; }
  done
done

if [[ -n "$atlas" && -s "$atlas_entries" ]]; then
  helper atlas "$atlas" "$commit" "$atlas_entries"
  echo "[$workload] indexed in $atlas"
fi
if ((${#not_reached[@]})); then
  echo "[$workload] ladder values not reached: ${not_reached[*]}"
fi
exit "$status"
