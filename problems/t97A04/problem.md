# t97A04

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

Contents:
- `problem.tex`: raw problem source when available
- `informal-solution.md`: best-effort worked mathematical solution
- `proof-outline.md`: formalization-oriented outline and blockers
- `lean/Main.lean`: current Lean development
- `status.json`: machine-readable bundle status

## Imported Provenance

- imported-at: `2026-05-01T19:38:18.659272Z`
- source-frame-id: `apm-v2-t97A04-1775012771698`
- source-module-root: `ApmCanaries.Frames.T97A04.Apm_v2_t97A04_1775012771698`

## Problem Statement

Raw TeX source:

```tex
The torus $\Ttw$ can be described as $\Rtw/(x,y)\sim (x+n,y+m)$ where
$n$ and $m$ are arbitrary integers. The linear map $L:\Rtw\rightarrow
\Rtw$ defined by $L(x,y)=(2x+y,y-x)$ induces a map
$\bar{L}:\Ttw\rightarrow \Ttw$ because $L$ carries integral points to
integral points.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{alist}
%------------------------------------------------------------------*
\item What is the degree of $L$?
%------------------------------------------------------------------*
\item Determine the induced homomorphism $\bar{L}:H_1(\Ttw)\rightarrow
H_1(\Ttw)$. 
%------------------------------------------------------------------*
\item What is the Lefschetz number of $\bar{L}$?
%------------------------------------------------------------------*
\end{alist}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
```
