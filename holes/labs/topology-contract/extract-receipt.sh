#!/usr/bin/env bash
set -euo pipefail
result="$1" token="$2" output="$3"
prefix="TOPOLOGY_RECEIPT_EDN $token "
mapfile -t matches < <(awk -v p="$prefix" 'index($0,p) == 1 { print substr($0,length(p)+1) }' "$result")
[ "${#matches[@]}" -eq 1 ] || {
  echo "expected exactly one nonce-bound receipt, found ${#matches[@]}" >&2
  exit 1
}
printf '%s\n' "${matches[0]}" > "$output"
