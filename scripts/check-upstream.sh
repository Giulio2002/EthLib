#!/usr/bin/env bash
# usage: check-upstream.sh <path to an ethereum/EthLib clone>; exits non-zero on any difference.
set -euo pipefail
up=ffd60c4bcbafa185ad8fbcf23be544d4b01f6d1c; here=$(cd "$(dirname "$0")/.." && pwd); fail=0
while read -r f; do
  if ! git -C "$1" show "$up:$f" | cmp -s - "$here/$f"; then echo "DIFFERS: $f"; fail=1; fi
done < <(cd "$here" && find EthLib -name '*.lean' | sort)
[ $fail = 0 ] && echo "all $(cd "$here" && find EthLib -name '*.lean' | wc -l) files identical to ethereum/EthLib@$up"
exit $fail
