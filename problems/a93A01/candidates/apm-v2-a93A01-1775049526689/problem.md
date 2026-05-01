# a93A01

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

Contents:
- `problem.tex`: raw problem source when available
- `informal-solution.md`: best-effort worked mathematical solution
- `proof-outline.md`: formalization-oriented outline and blockers
- `lean/Main.lean`: current Lean development
- `status.json`: machine-readable bundle status

## Imported Provenance

- imported-at: `2026-05-01T19:38:16.309074Z`
- source-frame-id: `apm-v2-a93A01-1775049526689`
- source-module-root: `ApmCanaries.Frames.A93A01.Apm_v2_a93A01_1775049526689`

## Problem Statement

Raw TeX source:

```tex
Let $f:(0,1)\rightarrow \R$. Prove that the following are equivalent:
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{alist}
%------------------------------------------------------------------*
\item $f$ is uniformly continuous
%------------------------------------------------------------------*
\item $\forall \epsilon>0:\exists N>0:\forall x,y\in (0,1)$ with
$x\neq y$, if $|(f(x)-f(y))/(x-y)|>N$ then $|f(x)-f(y)|<\epsilon$.
%------------------------------------------------------------------*
\end{alist}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
```
