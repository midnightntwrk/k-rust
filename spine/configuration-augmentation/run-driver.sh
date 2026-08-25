#!/usr/bin/env bash
set -euo pipefail

readonly SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
readonly KOMPILE_BIN="$(readlink -f "$(command -v kompile)")"
readonly K_ROOT="$(dirname "$(dirname "${KOMPILE_BIN}")")"
readonly K_JAVA="${K_ROOT}/lib/kframework/java"
readonly BUILD_ROOT="${R2_G_06_BUILD_ROOT:?set R2_G_06_BUILD_ROOT}"

while IFS= read -r tool_bin; do
  PATH="${tool_bin}:${PATH}"
done < <(sed -n "s/^PATH='\([^']*\/bin\)'.*/\1/p" "${KOMPILE_BIN}")
PATH="${K_ROOT}/bin:${PATH}"
LD_LIBRARY_PATH="${LD_LIBRARY_PATH:-}:${K_ROOT}/lib/kframework/native/linux64"
export PATH LD_LIBRARY_PATH

exec java \
  -Dfile.encoding=UTF-8 -Djava.awt.headless=true \
  -Xms64m -Xmx8192m -Xss32m -ea \
  -cp "${BUILD_ROOT}/driver-classes:${BUILD_ROOT}/overlay/classes:${K_JAVA}/*" \
  org.kframework.kink.configuration.ConfigurationAugmentationDriver "$@"
