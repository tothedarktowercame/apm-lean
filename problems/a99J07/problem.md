# a99J07

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

Contents:
- `problem.tex`: raw problem source when available
- `informal-solution.md`: best-effort worked mathematical solution
- `proof-outline.md`: formalization-oriented outline and blockers
- `lean/Main.lean`: current Lean development
- `status.json`: machine-readable bundle status

## Imported Provenance

- imported-at: `2026-05-01T19:38:17.258167Z`
- source-frame-id: `apm-v2-a99J07-1775005157308`
- source-module-root: `ApmCanaries.Frames.A99J07.Apm_v2_a99J07_1775005157308`

## Problem Statement

Raw TeX source:

```tex
Let $p(z)$ be a polynomial with complex coefficients and degree $N\geq
1$. Let $\|p\|_{\infty}=\sup\{|p(z)| \pipe z\in \C, |z|\leq
1\}$. Prove that $|p(w)|\leq \|p\|_{\infty}\max\{1,|w|\}^N$ for all
$w\in \C$.
```
