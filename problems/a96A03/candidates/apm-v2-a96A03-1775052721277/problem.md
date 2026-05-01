# a96A03

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

Contents:
- `problem.tex`: raw problem source when available
- `informal-solution.md`: best-effort worked mathematical solution
- `proof-outline.md`: formalization-oriented outline and blockers
- `lean/Main.lean`: current Lean development
- `status.json`: machine-readable bundle status

## Imported Provenance

- imported-at: `2026-05-01T19:38:16.669301Z`
- source-frame-id: `apm-v2-a96A03-1775052721277`
- source-module-root: `ApmCanaries.Frames.A96A03.Apm_v2_a96A03_1775052721277`

## Problem Statement

Raw TeX source:

```tex
Let $B=\{f\in L^2(\R)\pipe \|f\|_2\leq 1\}$, where the measure in
question is Lebesgue measure and let $\{f_n\}$ be a sequence from $B$
with the property that $f_n\rightarrow f$ almost everywhere in
$\R$. Show that the limit function $f$ belongs to $B$ and that
$\lim_{n\rightarrow \infty}\int_{-\infty}^{\infty}f_n(x)g(x)dx
=\int_{-\infty}^{\infty}f(x)g(x)dx$ for all $g\in L^2(\R)$. Hint: for
the second part, start by considering the case in which $g$ is a
continuous function supported in a bounded interval.
```
