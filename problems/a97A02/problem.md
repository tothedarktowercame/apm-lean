# a97A02

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

Contents:
- `problem.tex`: raw problem source when available
- `informal-solution.md`: best-effort worked mathematical solution
- `proof-outline.md`: formalization-oriented outline and blockers
- `lean/Main.lean`: current Lean development
- `status.json`: machine-readable bundle status

## Imported Provenance

- imported-at: `2026-05-01T19:38:17.014298Z`
- source-frame-id: `apm-v2-a97A02-1775003733088`
- source-module-root: `ApmCanaries.Frames.A97A02.Apm_v2_a97A02_1775003733088`

## Problem Statement

Raw TeX source:

```tex
Let $f\in L^p([0,1])$ ($1\leq p<\infty$), and for $h>0$ define
$f_h:[0,1]\rightarrow \C$ by
$f_h(t)=(1/2h)\int_{t-h}^{t+h}f(x)dx$. Prove that $f_h$ is continuous
and that for all $t\in [0,1]$, $|f_h(t)|\leq (2h)^{-1/p}\|f\|_p$.
```
