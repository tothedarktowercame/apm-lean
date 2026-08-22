#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

lake build Tools.DeclarationReachability >/dev/null
mkdir -p .lake/build/lib/lean/problems/t03J02/lean
lake env lean -R . \
  -o .lake/build/lib/lean/problems/t03J02/lean/Main.olean \
  problems/t03J02/lean/Main.lean >/dev/null
lake env lean -R . Reports/t03J02DeclarationReachability.lean
