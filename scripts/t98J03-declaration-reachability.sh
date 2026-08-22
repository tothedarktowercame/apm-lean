#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

lake build Tools.DeclarationReachability >/dev/null
mkdir -p .lake/build/lib/lean/problems/t98J03/lean
lake env lean -R . \
  -o .lake/build/lib/lean/problems/t98J03/lean/Main.olean \
  problems/t98J03/lean/Main.lean >/dev/null
lake env lean -R . Reports/t98J03DeclarationReachability.lean
