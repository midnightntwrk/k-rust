#!/usr/bin/env bash
set -euo pipefail

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
if [[ ${K_REFERENCE_REFRESH:-0} != 1 ]]; then
  echo "error: fixture refresh is destructive; rerun with K_REFERENCE_REFRESH=1" >&2
  exit 2
fi
if (($# == 0)); then
  echo "usage: K_REFERENCE_REFRESH=1 $0 <subsystem>/<case>..." >&2
  exit 2
fi

source "$workspace/scripts/reference-memory-guard.sh"
reference_enter_whole_job "$@"
source "$workspace/scripts/reference-pins.sh"

fixture_root="$workspace/crates/k-rust/tests/fixtures/reference"
k_checkout=${K_CHECKOUT:-"$workspace/k"}
kompile=${K_KOMPILE:-}
if [[ -z "$kompile" ]]; then
  kompile=$(command -v kompile || true)
fi
if [[ -z "$kompile" || ! -x "$kompile" ]]; then
  echo "error: set K_KOMPILE to the pinned reference kompile executable" >&2
  exit 2
fi
if [[ ! -d "$k_checkout/k-distribution/include/kframework/builtin" ]]; then
  echo "error: set K_CHECKOUT to the pinned K checkout (default: $workspace/k)" >&2
  exit 2
fi
reference_require_k_version "$kompile"
reference_require_git_pin K "$k_checkout" "$K_REFERENCE_REVISION"

tool_directory=$(cd "$(dirname "$kompile")" && pwd)
export K_KOMPILE="$kompile"
export K_KAST=${K_KAST:-"$tool_directory/kast"}
export K_KRUN=${K_KRUN:-"$tool_directory/krun"}
export K_KPROVE=${K_KPROVE:-"$tool_directory/kprove"}
export K_KORE_PARSER=${K_KORE_PARSER:-"$tool_directory/kore-parser"}
export K_KORE_EXEC=${K_KORE_EXEC:-"$tool_directory/kore-exec"}
if [[ -z ${K_KORE_RPC:-} ]]; then
  if [[ -x "$tool_directory/kore-rpc-booster" ]]; then
    export K_KORE_RPC="$tool_directory/kore-rpc-booster"
  else
    export K_KORE_RPC="$tool_directory/kore-rpc"
  fi
fi
for executable in K_KAST K_KRUN K_KPROVE K_KORE_PARSER K_KORE_EXEC K_KORE_RPC; do
  if [[ ! -x ${!executable} ]]; then
    echo "error: $executable does not name an executable: ${!executable}" >&2
    exit 2
  fi
done
export PATH="$tool_directory:$PATH"
export K_OPTS=${REFERENCE_DIFFERENTIAL_K_OPTS:-'-Xmx2048m -Xss1m -XX:+UseSerialGC -XX:CompressedClassSpaceSize=128m -XX:MaxMetaspaceSize=256m -XX:ReservedCodeCacheSize=128m'}

for selected in "$@"; do
  if [[ ! "$selected" =~ ^[A-Za-z0-9][A-Za-z0-9._-]*/[A-Za-z0-9][A-Za-z0-9._-]*$ ]]; then
    echo "error: fixture selection must be <subsystem>/<case>: $selected" >&2
    exit 2
  fi
  case_directory="$fixture_root/$selected"
  manifest="$case_directory/reference.toml"
  if [[ ! -f "$manifest" ]]; then
    echo "error: unknown reference fixture: $selected" >&2
    exit 2
  fi

  echo "[$selected] refreshing pinned reference artifacts"
  REFERENCE_FIXTURE_CASE="$case_directory" \
  REFERENCE_FIXTURE_MANIFEST="$manifest" \
  REFERENCE_FIXTURE_K_REVISION="$K_REFERENCE_REVISION" \
    python3 - <<'PY'
import hashlib
import os
import re
import shutil
import subprocess
import tempfile
import tomllib
from pathlib import Path

case = Path(os.environ["REFERENCE_FIXTURE_CASE"])
manifest_path = Path(os.environ["REFERENCE_FIXTURE_MANIFEST"])
source = manifest_path.read_text()
manifest = tomllib.loads(source)
expected_revision = os.environ["REFERENCE_FIXTURE_K_REVISION"]
if manifest.get("k_revision") != expected_revision:
    raise SystemExit(
        f"{manifest_path}: fixture pin {manifest.get('k_revision')!r} "
        f"does not match {expected_revision}"
    )

artifacts = manifest.get("artifact", [])
if not artifacts:
    raise SystemExit(f"{manifest_path}: no [[artifact]] rows")

digests = []
with tempfile.TemporaryDirectory(prefix="k-rust-reference-fixture-") as temporary:
    staged = Path(temporary) / case.name
    shutil.copytree(case, staged)
    for artifact in artifacts:
        command = artifact["command"]
        expected_status = artifact["exit_code"]
        completed = subprocess.run(
            [os.environ.get("BASH", "bash"), "-c", command], cwd=staged
        )
        if completed.returncode != expected_status:
            raise SystemExit(
                f"{manifest_path}: {artifact['file']} exited "
                f"{completed.returncode}, expected {expected_status}"
            )
        relative = Path(artifact["file"])
        if relative.is_absolute() or ".." in relative.parts:
            raise SystemExit(f"{manifest_path}: unsafe artifact path {relative}")
        generated = staged / relative
        if not generated.is_file():
            raise SystemExit(f"{manifest_path}: command did not produce {relative}")
        data = generated.read_bytes()
        if len(data) > 512 * 1024:
            raise SystemExit(f"{manifest_path}: {relative} exceeds 512 KiB")
        destination = case / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(data)
        digests.append(hashlib.sha256(data).hexdigest())

blocks = list(
    re.finditer(
        r"(?ms)^\[\[artifact\]\]\n.*?(?=^\[\[[A-Za-z0-9_.-]+\]\]|\Z)", source
    )
)
if len(blocks) != len(digests):
    raise SystemExit(f"{manifest_path}: could not locate every artifact block")
pieces = []
cursor = 0
for block, digest in zip(blocks, digests):
    pieces.append(source[cursor : block.start()])
    text = block.group(0)
    replaced, count = re.subn(
        r'(?m)^sha256\s*=\s*"[0-9a-fA-F]+"$',
        f'sha256 = "{digest}"',
        text,
        count=1,
    )
    if count != 1:
        raise SystemExit(f"{manifest_path}: artifact block has no single sha256")
    pieces.append(replaced)
    cursor = block.end()
pieces.append(source[cursor:])
manifest_path.write_text("".join(pieces))
PY
done

git -C "$workspace" diff --stat -- \
  crates/k-rust/tests/fixtures/reference
