# t96A08

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

Contents:
- `problem.tex`: raw problem source when available
- `informal-solution.md`: best-effort worked mathematical solution
- `proof-outline.md`: formalization-oriented outline and blockers
- `lean/Main.lean`: current Lean development
- `status.json`: machine-readable bundle status

## Imported Provenance

- imported-at: `2026-05-01T19:38:18.440954Z`
- source-frame-id: `apm-v2-t96A08-1775012559877`
- source-module-root: `ApmCanaries.Frames.T96A08.Apm_v2_t96A08_1775012559877`

## Problem Statement

Raw TeX source:

```tex
Let $M$ be a smooth manifold with a smooth $1$-form $\omega$ defined
on it. Assume that for any two piecewise smooth paths
$\gamma_1,\gamma_2\in M$ with the same initial and terminal points
that $\int_{\gamma_1}\omega=\int_{\gamma_2}\omega$.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{alist}
%------------------------------------------------------------------*
\item Let $0\in M$. Define $f:M\rightarrow M$ by
$f(p)=\int_{\gamma}\omega$ where $\gamma$ is a piecewise smooth path
from $0$ to $p$. Show that $f$ is smooth.
%------------------------------------------------------------------*
\item Show that $\omega$ is exact.
%------------------------------------------------------------------*
\end{alist}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
```
