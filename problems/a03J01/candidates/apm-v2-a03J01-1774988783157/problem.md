# a03J01

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

Contents:
- `problem.tex`: raw problem source when available
- `informal-solution.md`: best-effort worked mathematical solution
- `proof-outline.md`: formalization-oriented outline and blockers
- `lean/Main.lean`: current Lean development
- `status.json`: machine-readable bundle status

## Imported Provenance

- imported-at: `2026-05-01T19:38:16.108134Z`
- source-frame-id: `apm-v2-a03J01-1774988783157`
- source-module-root: `ApmCanaries.Frames.A03J01.Apm_v2_a03J01_1774988783157`

## Problem Statement

Raw TeX source:

```tex
Let $\{E_k\}$ be a sequence of Lebesgue measurable sets in $\Rn$ with
the property that $A=\sum_{k=1}^{\infty}m(E_k)<\infty$. Let $F_j$ be
the subset of $\Rn$ such that each point in $F_j$ is an element of
precisely $j$ of the sets $E_k$. Show that
$A=\sum_{j=1}^{\infty}jm(F_j)$.
```
