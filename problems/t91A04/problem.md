# t91A04

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

Contents:
- `problem.tex`: raw problem source when available
- `informal-solution.md`: best-effort worked mathematical solution
- `proof-outline.md`: formalization-oriented outline and blockers
- `lean/Main.lean`: current Lean development
- `status.json`: machine-readable bundle status

## Imported Provenance

- imported-at: `2026-05-01T19:38:17.942802Z`
- source-frame-id: `apm-v2-t91A04-1775008241824`
- source-module-root: `ApmCanaries.Frames.T91A04.Apm_v2_t91A04_1775008241824`

## Problem Statement

Raw TeX source:

```tex
Let $M$ be a complete metric space with metric $d(x,y)$ and let
$T:M\rightarrow M$ be a mapping of $M$ to itself. Assume there is a
constant $\lambda\in [0,1)$ such that $\forall x,y\in
M:d(T(x),T(y))\leq \lambda d(x,y)$. 

Show that $T$ has a fixed point. Hint: let $x\in M$ and consider the
sequence $\{T^j(x)\}$ in $M$.
```
