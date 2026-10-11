#!/bin/bash
# Run the Lean Kernel Arena's published test suite through tenet-hs.
# usage: tools/arena.sh SUITE_DIR [BIN]
# SUITE_DIR holds good/ (must accept) and bad/ (must reject), from
# https://arena.lean-lang.org/lean-arena-tests.tar.gz. Exit codes follow the arena: 0 accept, 1 reject, 2 decline.
set -u
SUITE=${1:?usage: arena.sh SUITE_DIR [BIN]}
BIN=${2:-$(cabal list-bin tenet-hs)}
pass=0; fail=0
while IFS= read -r f; do
  case "$f" in */good/*) want=0 ;; *) want=1 ;; esac
  perl -e 'alarm shift; exec @ARGV' ${ARENA_TIMEOUT:-300} "$BIN" check "$f" --quiet >/dev/null 2>&1; c=$?
  [ $c -eq 4 ] && c=2   # tenet-hs exits 4 to decline (compiled-code trust), which the arena spells 2
  if [ $c -eq $want ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "WRONG ($c, wanted $want): ${f#$SUITE/}"; fi
done < <(find "$SUITE" -name '*.ndjson' | sort)
echo "$pass correct, $fail wrong"
[ $fail -eq 0 ]
