# a01J01

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

Contents:
- `problem.tex`: raw problem source when available
- `informal-solution.md`: best-effort worked mathematical solution
- `proof-outline.md`: formalization-oriented outline and blockers
- `lean/Main.lean`: current Lean development
- `status.json`: machine-readable bundle status

## Imported Provenance

- imported-at: `2026-05-01T19:38:15.972105Z`
- source-frame-id: `apm-v2-a01J01-1774988573118`
- source-module-root: `ApmCanaries.Frames.A01J01.Apm_v2_a01J01_1774988573118`

## Problem Statement

Raw TeX source:

```tex
Let $f_n:[0,1]\rightarrow \R$ be Lebesgue measurable and have
$\int_0^1|f_n(t)|^3\ dm(t)\leq 1$ for all $n\in \N$.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{alist}
%------------------------------------------------------------------*
\item Show that for all $\epsilon>0:\exists \delta>0:$ if $E\subset
[0,1]$ is Lebesgue measurable with $m(E)<\delta$ then
$\int_E|f_n(t)|\ dm(t)<\epsilon$ for all $n\in \N$.
%------------------------------------------------------------------*
\item Show by example that the conclusion of (a) is false if
$\int_0^1|f_n(t)|^3\ dm(t)\leq 1$ is replaced by $$\int_0^1|f_n(t)|
\ dm(t)\leq 1$$.
%------------------------------------------------------------------*
\end{alist}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
```
