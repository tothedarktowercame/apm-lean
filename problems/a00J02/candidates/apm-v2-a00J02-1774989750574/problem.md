# a00J02

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

Contents:
- `problem.tex`: raw problem source when available
- `informal-solution.md`: best-effort worked mathematical solution
- `proof-outline.md`: formalization-oriented outline and blockers
- `lean/Main.lean`: current Lean development
- `status.json`: machine-readable bundle status

## Imported Provenance

- imported-at: `2026-05-01T19:38:15.758170Z`
- source-frame-id: `apm-v2-a00J02-1774989750574`
- source-module-root: `ApmCanaries.Frames.A00J02.Apm_v2_a00J02_1774989750574`

## Problem Statement

Raw TeX source:

```tex
Let $f:[0,1]\rightarrow\R$ be absolutely continuous and satisfy
$f(0)=0$ and also $\int_0^1|f'(x)|^2 dm(x)<\infty$. Show that
$\lim_{x\rightarrow 0+}x^{-1/2}f(x)$ exists and determine the value of
the limit.
```
