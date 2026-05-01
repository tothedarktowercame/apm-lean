# a93J03

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

Contents:
- `problem.tex`: raw problem source when available
- `informal-solution.md`: best-effort worked mathematical solution
- `proof-outline.md`: formalization-oriented outline and blockers
- `lean/Main.lean`: current Lean development
- `status.json`: machine-readable bundle status

## Imported Provenance

- imported-at: `2026-05-01T19:38:16.449292Z`
- source-frame-id: `apm-v2-a93J03-1774992011929`
- source-module-root: `ApmCanaries.Frames.A93J03.Apm_v2_a93J03_1774992011929`

## Problem Statement

Raw TeX source:

```tex
For $n=1,2,\ldots $, let $f_n:\R\rightarrow \R$ be a Lebesgue
measurable function. Assume that $A_n=\{x\in \R\pipe|f_n(x)|>n^{-2}\}$
has $\mu(A_n)\leq 2^{-n}$, where $\mu$ signifies Lebesgue measure.
Show that the series $\sum_{n=1}^{\infty}f_n(x)$ is absolutely
convergent for almost every $x\in \R$. Hint: what is the situation for
a point $x$ that lies outside of $A_n$ for all sufficiently large $n$?
```
