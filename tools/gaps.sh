#!/bin/sh
# Report steps that saturation cannot close, with SMT off.
# Usage: tools/gaps.sh BOOK [PROP...]   e.g. tools/gaps.sh 1, tools/gaps.sh 1 05 06
# Needs SystemE built and the propositions' imports built (make check).
set -e
book=$1; shift
cd "$(dirname "$0")/../lean"
out=${TMPDIR:-/tmp}/gaps-book$book
mkdir -p "$out"
if [ $# -eq 0 ]; then
  files=$(ls Elements/Book$book/Prop*.lean)
else
  files=$(for p in "$@"; do echo Elements/Book$book/Prop$p.lean; done)
fi
echo "$files" | xargs -P "$(nproc)" -I{} sh -c \
  'lake env lean -Dweak.systemE.smt=false -Dweak.systemE.stats=true {} > '"$out"'/$(basename {} .lean).log 2>&1 || true'
total=0
for f in $files; do
  n=$(basename "$f" .lean)
  log=$out/$n.log
  sat=$(grep -c "stats: saturated" "$log" || true)
  # first unproved literal of each failing step (by line)
  gaps=$(grep "could not prove" "$log" | sed -E 's/^[^:]*:([0-9]+):[0-9]+: error: saturation could not prove (.*), and systemE.smt is off$/\1: \2/' |
    awk -F': ' '!seen[$1]++')
  steps=$(printf '%s' "$gaps" | grep -c . || true)
  total=$((total + steps))
  if [ "$steps" -eq 0 ]; then
    if grep -q "error" "$log"; then echo "$n: other errors, see $log"; else echo "$n: ok ($sat steps)"; fi
  else
    echo "$n: $steps failing steps ($sat saturated)"
    printf '%s\n' "$gaps" | sed 's/^/  /'
  fi
done
echo "failing steps: $total (logs in $out)"
