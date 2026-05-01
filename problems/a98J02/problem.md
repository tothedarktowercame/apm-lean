# a98J02

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

Contents:
- `problem.tex`: raw problem source when available
- `informal-solution.md`: best-effort worked mathematical solution
- `proof-outline.md`: formalization-oriented outline and blockers
- `lean/Main.lean`: current Lean development
- `status.json`: machine-readable bundle status

## Imported Provenance

- imported-at: `2026-05-01T19:38:17.147678Z`
- source-frame-id: `apm-v2-a98J02-1775004665812`
- source-module-root: `ApmCanaries.Frames.A98J02.Apm_v2_a98J02_1775004665812`

## Problem Statement

Raw TeX source:

```tex
Suppose that $f:[0,1]\rightarrow \R$ is absolutely continuous and
$\int_0^1|f'(x)|^2 dx<\infty$. Prove that for every $\epsilon>0$ there
is some $\delta$ such that $0\leq y<x\leq 1$ and $|x-y|<\delta$
implies $\frac{|f(x)-f(y)|2}{|x-y|}<\epsilon$.
```
