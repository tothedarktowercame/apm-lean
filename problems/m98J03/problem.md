# m98J03

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

Contents:
- `problem.tex`: raw problem source when available
- `informal-solution.md`: best-effort worked mathematical solution
- `proof-outline.md`: formalization-oriented outline and blockers
- `lean/Main.lean`: current Lean development
- `status.json`: machine-readable bundle status

## Imported Provenance

- imported-at: `2026-05-01T19:38:17.805057Z`
- source-frame-id: `apm-v2-m98J03-1775007499607`
- source-module-root: `ApmCanaries.Frames.M98J03.Apm_v2_m98J03_1775007499607`

## Problem Statement

Raw TeX source:

```tex
Let $H$ be a nontrivial hilbert space and let $P$ be the orthogonal
projection of $H$ onto a closed subspace $V$. 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{alist}
%------------------------------------------------------------------*
\item Prove that the spectrum of $P$ ($=\sigma(P)$) is contained in $\{0,
1\}$. When is $\sigma(P)=\{0\}$? When is $\sigma(P)=\{1\}$?
%------------------------------------------------------------------*
\item Prove that $P$ is compact if and only if $V$ is finite
dimensional.
%------------------------------------------------------------------*
\item Define the space $V^{\perp}$ (the orthogonal complement of $V$
in $H$).
%------------------------------------------------------------------*
\item Prove that $V^{\perp}$ is closed.
%------------------------------------------------------------------*
\item Show that if $A$ is a bounded linear operator from $H$ to $H$
such that $AP=PA$ then $A$ maps $V$ into $V$ and $V^{\perp}$ into
$V^{\perp}$.
%------------------------------------------------------------------*
\item Describe explicitly the Hilbert adjoint $P^*$ of $P$. 
%------------------------------------------------------------------*
\end{alist}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
```
