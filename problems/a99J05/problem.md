# a99J05

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

Contents:
- `problem.tex`: raw problem source when available
- `informal-solution.md`: best-effort worked mathematical solution
- `proof-outline.md`: formalization-oriented outline and blockers
- `lean/Main.lean`: current Lean development
- `status.json`: machine-readable bundle status

## Imported Provenance

- imported-at: `2026-05-01T19:38:17.220546Z`
- source-frame-id: `apm-v2-a99J05-1775005037257`
- source-module-root: `ApmCanaries.Frames.A99J05.Apm_v2_a99J05_1775005037257`

## Problem Statement

Raw TeX source:

```tex
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{alist}
%------------------------------------------------------------------*
\item Give an example of a sequence of functions
$\{f_n\}_{n=1}^{\infty}$ in $L^1([0,1])$ such that $\lim_{n\rightarrow
\infty}\|f_n\|_1=0$ but the sequence fails to converge almost
everywhere on $[0,1]$ with respect to Lebesgue measure.
%------------------------------------------------------------------*
\item If $\|f_n\|_1\leq 2^{-n}$ show that $f_n(x)$ converges to $0$
almost everywhere.
%------------------------------------------------------------------*
\end{alist}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
```
