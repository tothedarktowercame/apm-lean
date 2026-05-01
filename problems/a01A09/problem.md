# a01A09

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

Contents:
- `problem.tex`: raw problem source when available
- `informal-solution.md`: best-effort worked mathematical solution
- `proof-outline.md`: formalization-oriented outline and blockers
- `lean/Main.lean`: current Lean development
- `status.json`: machine-readable bundle status

## Imported Provenance

- imported-at: `2026-05-01T19:38:15.943677Z`
- source-frame-id: `apm-v2-a01A09-1774988409275`
- source-module-root: `ApmCanaries.Frames.A01A09.Apm_v2_a01A09_1774988409275`

## Problem Statement

Raw TeX source:

```tex
Suppose $f$ is a complex-valued function defined on $[0,\infty)$ that
belongs to $L^p([0,\infty))$ for some $p$ such that
$1<p<\infty$. Define $G$ on the right half-plane by
$G(z)=\int_0^{\infty}f(t) e^{tz} dt$. Prove that $G(z)$ is analytic
for $z$ with $\Re z>0$. What additional assumption would ensure that
$f$ is entire?
```
