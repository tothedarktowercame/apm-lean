# a96J06

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

Contents:
- `problem.tex`: raw problem source when available
- `informal-solution.md`: best-effort worked mathematical solution
- `proof-outline.md`: formalization-oriented outline and blockers
- `lean/Main.lean`: current Lean development
- `status.json`: machine-readable bundle status

## Imported Provenance

- imported-at: `2026-05-01T19:38:16.950820Z`
- source-frame-id: `apm-v2-a96J06-1775003321530`
- source-module-root: `ApmCanaries.Frames.A96J06.Apm_v2_a96J06_1775003321530`

## Problem Statement

Raw TeX source:

```tex
Let $p(z)=z+\sum_{n=2}^{N}c_n z^n$, with $c_k\in \C$ and $c_N\neq 0$.
Prove that for every $r>0$ there is some point $\zeta\in \{z\in
\C\pipe |z|<r\}$ such that $r<|p(\zeta)|$.
```
