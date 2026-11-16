#!/usr/bin/env bash
# Generate the KORE of the k-rust examples and of IMP with krust, for the round-trip test.
# Usage: scripts/generate-kore.sh OUT_DIR   (run from kore-lean/; OUT_DIR is outside the package
# or under gen/, which .gitignore excludes). Prints the files to pass to `lake exe roundtrip`.
set -u
out=${1:?usage: generate-kore.sh OUT_DIR}
repo=$(cd "$(dirname "$0")/../../../.." && pwd)
krust=$repo/target/release/krust
builtin=$repo/k/k-distribution/include/kframework/builtin
imp=$repo/imp-semantics/src/kimp/kdist/imp-semantics
mkdir -p "$out"
for f in "$repo"/examples/*.k; do
  stem=$(basename "$f" .k)
  module=$(tr a-z A-Z <<<"$stem")
  if "$krust" kcompile "$f" --main-module "$module" -o "$out/$stem" >"$out/$stem.log" 2>&1; then
    echo "$out/$stem/definition.kore $out/$stem/syntaxDefinition.kore"
  else
    echo "skipped $stem (kcompile failed; see $out/$stem.log)" >&2
  fi
done
"$krust" kcompile "$imp/imp.k" --main-module IMP --syntax-module IMP-SYNTAX \
  --builtin-directory "$builtin" -I "$imp" -o "$out/imp" >"$out/imp.log" 2>&1 \
  && echo "$out/imp/definition.kore $out/imp/syntaxDefinition.kore"
"$krust" kcompile "$imp/imp.k" --main-module IMP --syntax-module IMP-SYNTAX --for-proving \
  --builtin-directory "$builtin" -I "$imp" --output-directory "$out/imp-proof" >"$out/imp-proof.log" 2>&1 \
  && "$krust" kcompile "$repo/imp-semantics/examples/specs/imp-simple-spec.k" \
    --compiled-definition "$out/imp-proof" --main-module IMP-SIMPLE-SPEC \
    --definition-module IMP-VERIFICATION --for-proving --builtin-directory "$builtin" -I "$imp" \
    --output-directory "$out/imp-spec" >"$out/imp-spec.log" 2>&1 \
  && echo "$out/imp-proof/definition.kore $out/imp-spec/definition.kore"
