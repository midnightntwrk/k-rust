#!/usr/bin/env bash
set -euo pipefail

readonly SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
readonly KOMPILE_BIN="$(readlink -f "$(command -v kompile)")"
readonly K_ROOT="$(dirname "$(dirname "${KOMPILE_BIN}")")"
readonly K_JAVA="${K_ROOT}/lib/kframework/java"
readonly BUILD_DIR="${SCRIPT_DIR}/build/java"
readonly SOURCE="${SCRIPT_DIR}/src/java/org/kframework/kink/transport/DefinitionTransportDriver.java"
readonly CLASS="${BUILD_DIR}/org/kframework/kink/transport/DefinitionTransportDriver.class"

# Preserve the executable environment of the installed Nix kompile wrapper.
while IFS= read -r tool_bin; do
  PATH="${tool_bin}:${PATH}"
done < <(sed -n "s/^PATH='\([^']*\/bin\)'.*/\1/p" "${KOMPILE_BIN}")
PATH="${K_ROOT}/bin:${PATH}"
LD_LIBRARY_PATH="${LD_LIBRARY_PATH:-}:${K_ROOT}/lib/kframework/native/linux64"
export PATH LD_LIBRARY_PATH

if [[ ! -f "${K_JAVA}/k-frontend-1.0-SNAPSHOT.jar" ]]; then
  printf 'Cannot locate pinned K Java artifacts below %s\n' "${K_JAVA}" >&2
  exit 2
fi

if [[ ! -e "${CLASS}" || "${SOURCE}" -nt "${CLASS}" ]]; then
  mkdir -p "${BUILD_DIR}"
  javac -encoding UTF-8 -cp "${K_JAVA}/*" -d "${BUILD_DIR}" "${SOURCE}"
fi

exec java \
  -Dfile.encoding=UTF-8 \
  -Djava.awt.headless=true \
  -Xms64m \
  -Xmx8192m \
  -Xss32m \
  -ea \
  -cp "${BUILD_DIR}:${K_JAVA}/*" \
  org.kframework.kink.transport.DefinitionTransportDriver "$@"
