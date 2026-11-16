#!/usr/bin/env bash
# E6's text: one module importing every module of every file of K's builtin directory, kompiled by
# kompile 7.1.337 with default options and --backend haskell into .lake/constructs-e6/ (not
# committed). Usage: test/constructs/kompile-e6.sh. K_KOMPILE names kompile (default: the main k-rust
# checkout's k/result/bin/kompile; K_RUST names that checkout).
#
# Modules left out, each because kompile 7.1.337 rejects the definition that imports it (every
# other module of the files is imported):
#   *-PROGRAM-PARSING (ID-SYNTAX-PROGRAM-PARSING, KVAR-SYNTAX-PROGRAM-PARSING): the program
#     grammar's identifier tokens; imported into a definition, the library's own rules no longer
#     parse (`_` and `_X` variables: "Parse error: unexpected token '_'", domains.md:170).
#   kast.md KCELLS, RULE-CELLS, CONFIG-CELLS, DEFAULT-LAYOUT: modules the rule and configuration
#     grammars import by themselves (RuleGrammarGenerator.getGrammar); imported, `#cells` and
#     `#Layout` are declared twice ("Symbol #cells is not unique").
#   kast.md KAST, KSEQ, KSEQ-SYMBOLIC, K, K-TERM, KREWRITE, K-TOP-SORT, K-BOTTOM-SORT,
#     K-SORT-LATTICE, K-AMBIGUITIES, K-LOCATIONS: K's term language; imported, kompile stops
#     ("Expected to find exactly one production for KLabel: #EmptyK") or the backend's check
#     refuses the text (kore-exec ErrorVerify: "Cannot define constructor ... with variable result
#     sort"). Their productions are E3's rows.
set -eu
K=$(cd "$(dirname "$0")/../.." && pwd)
KR=${K_RUST:-$HOME/git/workspaces/starstream-fv/inspirations/midnightntwrk/k-rust}
KOMPILE=${K_KOMPILE:-$KR/k/result/bin/kompile}
B=$(dirname "$(dirname "$(readlink -f "$KOMPILE")")")/include/kframework/builtin
O=$K/.lake/constructs-e6
EXCL='^(.*-PROGRAM-PARSING|KCELLS|RULE-CELLS|CONFIG-CELLS|DEFAULT-LAYOUT|KAST|KSEQ|KSEQ-SYMBOLIC|K|K-TERM|KREWRITE|K-TOP-SORT|K-BOTTOM-SORT|K-SORT-LATTICE|K-AMBIGUITIES|K-LOCATIONS)$'
rm -rf "$O"; mkdir -p "$O"
files=$(cd "$B" && ls | grep -v '^prelude.md$')
{
  for f in $files; do echo "requires \"$f\""; done
  echo; echo "module ALL-BUILTINS"
  for f in $files; do
    case $f in
      *.md) awk '/^```/ { if (!b) { b = 1; t = substr($0, 4); k = (t == "k" || t ~ /(^|[ {])\.?k([ }]|$)/) } else b = 0; next } b && k' "$B/$f" ;;
      *) cat "$B/$f" ;;
    esac | grep -oE '^\s*module [A-Z0-9-]+' | awk '{print $2}' | grep -vE "$EXCL" | sed 's/^/  imports /'
  done
  echo "endmodule"
} > "$O/all-builtins.k"
echo "kompile-e6: $(grep -c imports "$O/all-builtins.k") modules imported, $(free -g | awk '/^Mem:/ {print $7}') GiB available"
cd "$O"
LEAN_NUM_THREADS=1 systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0 timeout 1800 \
  "$KOMPILE" --backend haskell all-builtins.k -o all-builtins-kompiled > kompile.log 2>&1 \
  || { echo "kompile-e6: kompile failed"; cat kompile.log; exit 1; }
sha256sum all-builtins-kompiled/definition.kore
