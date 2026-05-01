# a94A01

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

Contents:
- `problem.tex`: raw problem source when available
- `informal-solution.md`: best-effort worked mathematical solution
- `proof-outline.md`: formalization-oriented outline and blockers
- `lean/Main.lean`: current Lean development
- `status.json`: machine-readable bundle status

## Imported Provenance

- imported-at: `2026-05-01T19:38:16.588078Z`
- source-frame-id: `apm-v2-a94A01-1775002871618`
- source-module-root: `ApmCanaries.Frames.A94A01.Apm_v2_a94A01_1775002871618`

## Problem Statement

Raw TeX source:

```tex
Suppose that for $n=1,2,\ldots $ the function $f_n$ is the
characteristic function of a Lebesgue measurable subset $E_n$ of the
real line and that $f(x)=\lim_{n\rightarrow \infty}f_n(x)$ exists for
almost every $x$ in $\R$. 

Show that
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{alist}
%------------------------------------------------------------------*
\item $f$ is equal almost everywhere to the characteristic function
of a Lebesgue measurable set $E$;
%------------------------------------------------------------------*
\item $\int_Eg(x)dx=\lim_{n\rightarrow \infty}\int_{E_n}g(x)dx$ 
for every Lebesgue measurable integrable function $g:\R\rightarrow
\R$.
%------------------------------------------------------------------*
\end{alist}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Establish necessary and sufficient conditions for $f_n\rightarrow f$
in the $L^p$-norm on $\R$ whenever $1\leq p<\infty$.
```
