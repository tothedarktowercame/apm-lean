# t99J04

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

Contents:
- `problem.tex`: raw problem source when available
- `informal-solution.md`: best-effort worked mathematical solution
- `proof-outline.md`: formalization-oriented outline and blockers
- `lean/Main.lean`: current Lean development
- `status.json`: machine-readable bundle status

## Imported Provenance

- imported-at: `2026-05-01T19:38:18.952783Z`
- source-frame-id: `apm-v2-t99J04-1775013570926`
- source-module-root: `ApmCanaries.Frames.T99J04.Apm_v2_t99J04_1775013570926`

## Problem Statement

Raw TeX source:

```tex
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{alist}
%------------------------------------------------------------------*
\item Suppose that $X$ in an $n$-dimensional manifold, $x$ is a point
in $X$ and $f^1,\ldots ,f^n:X\rightarrow \R$ are smooth functions such
that the differentials $df^1_x,\ldots ,df^n_x$ are linearly
independent at $x$. Is $f^1,\ldots ,f^n$ necessarily a local
coordinate system in a neighborhood of $x$.
%------------------------------------------------------------------*
\item Suppose that $f:X\rightarrow Y$ is a smooth map from a compact
manifold $X$ to a connected manifold. Assume that $df_x$ is invertible
for all $x\in X$. Prove that $f$ is surjective.
%------------------------------------------------------------------*
\end{alist}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
```
