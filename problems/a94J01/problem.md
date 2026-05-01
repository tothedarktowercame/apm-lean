# a94J01

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

Contents:
- `problem.tex`: raw problem source when available
- `informal-solution.md`: best-effort worked mathematical solution
- `proof-outline.md`: formalization-oriented outline and blockers
- `lean/Main.lean`: current Lean development
- `status.json`: machine-readable bundle status

## Imported Provenance

- imported-at: `2026-05-01T19:38:16.615414Z`
- source-frame-id: `apm-v2-a94J01-1775002964674`
- source-module-root: `ApmCanaries.Frames.A94J01.Apm_v2_a94J01_1775002964674`

## Problem Statement

Raw TeX source:

```tex
Let $f\in L^1(\Rn)$. Show that for any $\epsilon>0$ there is a
$\delta>0$ such that for every Lebesgue measurable set $E\subset \Rn$
with $m(E)<\delta$ we have $|\int_Ef(x)dx|<\epsilon$.
```
