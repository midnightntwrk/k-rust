# shellcheck shell=bash
# The generator invocations of every k2lean library, relation and test-data file.
# Sourced (not run) by k2lean/tests/gate.sh, k2lean/demos/regen.sh and k2lean/pipelines/*.sh, so a
# flag is changed once and every caller (the gate on its copies included) uses it.
#
# The calls are registered by area, in areas/AREA.sh beside this file (the areas are LIBS_AREAS
# below; docs/testing.md of the repository says what each owns). An area file defines, for the
# names it owns, any of:
#   kore_AREA NAME OUT  set f, m, s and inc (K file, main and syntax module, include directory) of
#                       definition NAME, after any preparation step that writes under OUT; return 1
#                       when NAME is not the area's, 2 when its preparation failed
#   name_AREA DIR       print the Lean namespace of library DIR; return 1 when DIR is not the area's
#   gen_AREA DIR        set the array GEN_ARGS to the `gen` arguments of library DIR (whose output
#                       directory is $o); return 1 when DIR is not the area's
#   relate_AREA NS      set libs_relate's variables (na ka nb kd f extra) for demo NS; return 1 when
#                       NS is not the area's
# its own commands (libs_soundness, libs_refine, …), and its gate phases (gate_AREA, needs_AREA,
# called by tests/gate.sh only). The dispatchers below ask each area in turn.
#
# The caller sets, before calling a function:
#   G        the k2lean binary
#   GEN      the libraries' output root (a `generated/` directory next to `lean/prelude`: each
#            library requires the prelude as ../../lean/prelude)
#   DEMOS    the demos root (a `demos/` directory): relations write `DEMOS/NS/...`
#   KRS      the directory of the KRS IMP KORE (`demos/k/krs-imp`)
#   FIXTURES the generator's fixtures (`tests/fixtures`): the `nested` library reads its compiled KORE
#   KRUST    krust; BUILTIN, K's builtin include directory
#   KIMP     kimp's K sources (imp-semantics)
#   SD       SIMPLE's K sources (for libs_simple_cases, and the SIMPLE-based compiles)
#   GOLDENS  the golden cases of kimp (k2lean/tests/goldens; only for libs_goldens)
# and defines the function `kore_dir NAME`, which prints the directory of the compiled KORE of
# definition NAME, so that each caller keeps its own layout.

LIBS_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
# the areas, in the order the gate runs them (an area may use what an earlier one built);
# tests/gate-check.py reads this line
LIBS_AREAS="core invariants relational soundness confluence noninterference claims"
for _a in $LIBS_AREAS; do
  # shellcheck source=/dev/null
  . "$LIBS_DIR/areas/$_a.sh"
done
unset _a

# libs_kcompile NAME: compile definition NAME's K source with krust into `kore_dir NAME`.
libs_kcompile() {
  local out; out=$(kore_dir "$1")
  local f='' m='' s='' inc='' a rc
  for a in $LIBS_AREAS; do
    declare -F "kore_$a" > /dev/null || continue
    "kore_$a" "$1" "$out"; rc=$?
    [ "$rc" = 1 ] && continue
    [ "$rc" = 0 ] || return 1
    "$KRUST" kcompile "$f" --main-module "$m" --syntax-module "$s" --output-directory "$out" \
      --builtin-directory "$BUILTIN" -I "$inc"
    return
  done
  echo "libs_kcompile: unknown definition $1" >&2; return 2
}

# libs_name DIR: the Lean namespace of library DIR.
libs_name() {
  local a
  for a in $LIBS_AREAS; do declare -F "name_$a" > /dev/null && "name_$a" "$1" && return 0; done
  echo "libs_name: unknown library $1" >&2; return 2
}

# libs_gen DIR: generate library DIR into GEN/DIR, with its open-obligation list.
libs_gen() {
  local o=$GEN/$1 a GEN_ARGS=()
  for a in $LIBS_AREAS; do
    declare -F "gen_$a" > /dev/null && "gen_$a" "$1" || continue
    "$G" gen "${GEN_ARGS[@]}"
    return
  done
  echo "libs_gen: unknown library $1" >&2; return 2
}

# libs_fixture DIR: the fixture directory (tests/fixtures/NAME) of fixture library DIR.
libs_fixture() {
  local n=${1%b}   # peanob, cellmapb: the fixture of peano, cellmap
  echo "$LIBS_DIR/fixtures/$n"
}

# libs_fixture_args DIR: GEN_ARGS for library DIR generated from its fixture's checked-in KORE
# (tests/fixtures, under the namespace libs_name gives it).
libs_fixture_args() {
  local fx; fx=$(libs_fixture "$1")
  GEN_ARGS=(--kore "$fx/definition.kore" --runtime "$fx/runtime.json"
    --out "$o" --name "$(libs_name "$1")" --prelude ../../lean/prelude --open-obligations "$o/open-obligations.txt")
}

# libs_relate NS: the relation of demo NS and its correspondence report. An area's relate_AREA sets
# the second side (nb, kd), and the first when it is not kimp (na, ka), the file (f: Tr, or Bisim
# for a bisimulation) and extra arguments.
libs_relate() {
  local ns=$1 na=KImp ka nb='' kd='' f=Tr extra=() a found=''
  ka=$(kore_dir kimp)
  for a in $LIBS_AREAS; do declare -F "relate_$a" > /dev/null && "relate_$a" "$ns" && { found=1; break; }; done
  [ -n "$found" ] || { echo "libs_relate: unknown demo $ns" >&2; return 2; }
  # the syntax definitions name the concrete syntax of symbols; the fixtures have none
  local sa=() sb=()
  [ -f "$ka/syntaxDefinition.kore" ] && sa=(--syntax-a "$ka/syntaxDefinition.kore")
  [ -f "$kd/syntaxDefinition.kore" ] && sb=(--syntax-b "$kd/syntaxDefinition.kore")
  "$G" relate --kore-a "$ka/definition.kore" "${sa[@]}" --name-a "$na" \
    --kore-b "$kd/definition.kore" "${sb[@]}" --name-b "$nb" \
    --ns "$ns" "${extra[@]}" --out "$DEMOS/$ns/$ns/$f.lean" --report "$DEMOS/$ns/correspondence.toml"
}
