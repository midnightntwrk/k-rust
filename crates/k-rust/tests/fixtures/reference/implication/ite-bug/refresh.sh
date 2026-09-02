#!/usr/bin/env bash
set -u

kompile=${K_KOMPILE:?set K_KOMPILE to the pinned reference kompile executable}
kprove=${K_KPROVE:?set K_KPROVE to the pinned reference kprove executable}

"$kompile" ite-bug.k --backend haskell --output-definition ref-kompiled >/dev/null
echo "== with lemmas: kprove passing-spec"
set +e
timeout 600 "$kprove" passing-spec.k --definition ref-kompiled 2>&1 | tail -5
echo "rc=${PIPESTATUS[0]}"
echo "== with lemmas: kprove failing-1-spec"
timeout 600 "$kprove" failing-1-spec.k --definition ref-kompiled 2>&1 | tail -8
echo "rc=${PIPESTATUS[0]}"
cd nolemma
echo "== nolemma kompile"
timeout 300 "$kompile" ite-bug.k --backend haskell --output-definition ref-kompiled 2>&1 | tail -2
echo "rc=${PIPESTATUS[0]}"
echo "== nolemma: kprove passing-spec"
timeout 600 "$kprove" passing-spec.k --definition ref-kompiled 2>&1 | tail -5
echo "rc=${PIPESTATUS[0]}"
echo DONE
