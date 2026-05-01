# aunk01

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

Contents:
- `problem.tex`: raw problem source when available
- `informal-solution.md`: best-effort worked mathematical solution
- `proof-outline.md`: formalization-oriented outline and blockers
- `lean/Main.lean`: current Lean development
- `status.json`: machine-readable bundle status

## Imported Provenance

- imported-at: `2026-05-01T19:38:17.289577Z`
- source-frame-id: `apm-v2-aunk01-1775005703226`
- source-module-root: `ApmCanaries.Frames.Aunk01.Apm_v2_aunk01_1775005703226`

## Problem Statement

Raw TeX source:

```tex
Let $m$ denote Lebesgue measure on $\R$ and for each Borel set $A$ in
$\R$, define the set $A+y$ by $A+y=\{x+y\pipe x\in A\}$.  Prove the
following results, stating carefully any theorem(s) you use:
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{alist}
%------------------------------------------------------------------*
\item $A+y$ is a Borel set
%------------------------------------------------------------------*
\item $m(A+y)=m(A)$
%------------------------------------------------------------------*
\item if $f\in L^1(\R)$, then
$\int_{\R}f(x+y)dm(x)=\int_{\R}f(x)dm(x)$.
%------------------------------------------------------------------*
\end{alist}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
```
