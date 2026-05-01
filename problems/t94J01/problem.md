# t94J01

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

Contents:
- `problem.tex`: raw problem source when available
- `informal-solution.md`: best-effort worked mathematical solution
- `proof-outline.md`: formalization-oriented outline and blockers
- `lean/Main.lean`: current Lean development
- `status.json`: machine-readable bundle status

## Imported Provenance

- imported-at: `2026-05-01T19:38:18.251241Z`
- source-frame-id: `apm-v2-t94J01-1775010781379`
- source-module-root: `ApmCanaries.Frames.T94J01.Apm_v2_t94J01_1775010781379`

## Problem Statement

Raw TeX source:

```tex
A space $X$ is \emph{ladder connected} if for each open cover $U$
of $X$ and each pair of points $p,q\in X$ there is a finite sequence
$U_1,U_2,\ldots ,U_n$ of sets that belong to $U$ such that $p\in U_1$
and $q\in U_n$ and $U_i\cap U_{i+1}\neq \phi$ ($1\leq i\leq
n-1$). Show that a space is connected if and only if it is ladder
connected.
```
