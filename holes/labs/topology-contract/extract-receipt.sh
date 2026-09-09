#!/usr/bin/env bash
set -euo pipefail
result="$1" token="$2" output="$3"
here="$(cd "$(dirname "$0")" && pwd)"
prefix="TOPOLOGY_RECEIPT_EDN $token "

# The nonce-uniqueness property is real and stays enforced: the token binds the
# receipt to THIS dispatch, so two starts means an agent echoed the nonce.
starts="$(awk -v p="$prefix" 'index($0,p) == 1 { n++ } END { print n+0 }' "$result")"
[ "$starts" -eq 1 ] || {
  echo "expected exactly one nonce-bound receipt, found $starts" >&2
  exit 1
}

# Extract the EDN FORM rather than one physical line -- see extract_receipt.bb.
bb "$here/extract_receipt.bb" "$result" "$prefix" > "$output"
