# a92J02

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

Contents:
- `problem.tex`: raw problem source when available
- `informal-solution.md`: best-effort worked mathematical solution
- `proof-outline.md`: formalization-oriented outline and blockers
- `lean/Main.lean`: current Lean development
- `status.json`: machine-readable bundle status

## Imported Provenance

- imported-at: `2026-05-01T19:38:16.217637Z`
- source-frame-id: `apm-v2-a92J02-1775002223303`
- source-module-root: `ApmCanaries.Frames.A92J02.Apm_v2_a92J02_1775002223303`

## Problem Statement

Raw TeX source:

```tex
Let $f_1,f_2,\ldots $ and $f$ be Lebesgue measurable functions. We say
that $f_n$ converges to $f$ in measure if to each $\epsilon>0$ there
corresponds a $N$ such that for $n>N$, $m\{x\pipe
|f_n(x)-f(x)|>\epsilon\}<\epsilon$. Show that if $f_n$ converges to
$f$ in measure, then some subsequence converges to $f$ almost everywhere.
```
