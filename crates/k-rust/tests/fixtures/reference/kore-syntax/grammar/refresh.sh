#!/usr/bin/env bash
set -euo pipefail

for path in pass/*.kore; do
  "$K_KORE_PARSER" "$path" --no-verify >/dev/null 2>&1
  printf '%s\t0\n' "$path"
done

whitespace=$(mktemp)
trap 'rm -f "$whitespace"' EXIT
awk '{ gsub(/<FF>/, sprintf("%c", 12)); gsub(/<VT>/, sprintf("%c", 11)); print }' \
  pass/whitespace.kore.in >"$whitespace"
"$K_KORE_PARSER" "$whitespace" --no-verify >/dev/null 2>&1
printf '%s\t0\n' 'pass/whitespace.kore.in'

for path in fail/*.kore; do
  set +e
  "$K_KORE_PARSER" "$path" --no-verify >/dev/null 2>&1
  status=$?
  set -e
  if ((status == 0)); then
    echo "error: reference unexpectedly accepted $path" >&2
    exit 1
  fi
  printf '%s\t%s\n' "$path" "$status"
done
