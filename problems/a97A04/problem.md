# a97A04

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

Contents:
- `problem.tex`: raw problem source when available
- `informal-solution.md`: best-effort worked mathematical solution
- `proof-outline.md`: formalization-oriented outline and blockers
- `lean/Main.lean`: current Lean development
- `status.json`: machine-readable bundle status

## Imported Provenance

- imported-at: `2026-05-01T19:38:17.082580Z`
- source-frame-id: `apm-v2-a97A04-1775003958890`
- source-module-root: `ApmCanaries.Frames.A97A04.Apm_v2_a97A04_1775003958890`

## Problem Statement

Raw TeX source:

```tex
Let $(f_n)$ be a sequence of measurable functions on the measure
space $(X,\Sigma,\mu)$. Suppose that $\forall x\in X:(f_n(x))_{n\in
\N}$ is a bounded sequence. Let $E=\{x\in X \pipe (f_n(x))_{n\in \N}
\text{\ converges}\}$. Show that $E\in \Sigma$.
```
