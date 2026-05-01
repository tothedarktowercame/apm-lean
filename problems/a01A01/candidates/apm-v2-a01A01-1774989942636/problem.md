# a01A01

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

Contents:
- `problem.tex`: raw problem source when available
- `informal-solution.md`: best-effort worked mathematical solution
- `proof-outline.md`: formalization-oriented outline and blockers
- `lean/Main.lean`: current Lean development
- `status.json`: machine-readable bundle status

## Imported Provenance

- imported-at: `2026-05-01T19:38:15.881545Z`
- source-frame-id: `apm-v2-a01A01-1774989942636`
- source-module-root: `ApmCanaries.Frames.A01A01.Apm_v2_a01A01_1774989942636`

## Problem Statement

Raw TeX source:

```tex
Find a sequence of real-valued nonnegative functions $\{f_k\}$ on
$[0,1]$ such that $\forall x: \limsup f_k(x)=\infty$ and
$\int_{[0,1]}f_kdx\rightarrow 0$. Adapt this argument to the case
where the domain is $\Rn$.
```
