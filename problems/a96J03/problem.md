# a96J03

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

Contents:
- `problem.tex`: raw problem source when available
- `informal-solution.md`: best-effort worked mathematical solution
- `proof-outline.md`: formalization-oriented outline and blockers
- `lean/Main.lean`: current Lean development
- `status.json`: machine-readable bundle status

## Imported Provenance

- imported-at: `2026-05-01T19:38:16.921058Z`
- source-frame-id: `apm-v2-a96J03-1775003261538`
- source-module-root: `ApmCanaries.Frames.A96J03.Apm_v2_a96J03_1775003261538`

## Problem Statement

Raw TeX source:

```tex
Suppose that $f(x)$ belongs to $L^1(\R,\mu)$, where $\mu$ is Lebesgue
measure. Prove that $$\lim_{t\rightarrow
0}\int_{\R}|f(x-t)-f(x)|d\mu(x)=0.$$
```
