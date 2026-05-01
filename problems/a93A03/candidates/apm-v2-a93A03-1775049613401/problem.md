# a93A03

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

Contents:
- `problem.tex`: raw problem source when available
- `informal-solution.md`: best-effort worked mathematical solution
- `proof-outline.md`: formalization-oriented outline and blockers
- `lean/Main.lean`: current Lean development
- `status.json`: machine-readable bundle status

## Imported Provenance

- imported-at: `2026-05-01T19:38:16.366392Z`
- source-frame-id: `apm-v2-a93A03-1775049613401`
- source-module-root: `ApmCanaries.Frames.A93A03.Apm_v2_a93A03_1775049613401`

## Problem Statement

Raw TeX source:

```tex
Let $\langle \cdot ,\cdot \rangle$ denote the inner product on a
Hilbert space (with norm $\|\cdot \|$). A sequence $(h_n)$ of vectors
in $H$ is said to converge weakly to $h\in H$ if for all $k\in H$,
$\lim_{n\rightarrow \infty}\langle h_n,k \rangle=\langle h,k \rangle$.
Prove the following statements:
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{alist}
%------------------------------------------------------------------*
\item If the sequence $(h_n)$ converges weakly to $h$ and if
$\lim_{n\rightarrow \infty}\|h_n\|=\|h\|$ then $\lim_{n\rightarrow
\infty}\|h_n-h\|=0$.
%------------------------------------------------------------------*
\item If $(h_n)$ converges weakly to $h$ then $\|h\|\leq
\liminf_{n\rightarrow \infty} \|h_n\|$.
%------------------------------------------------------------------*
\end{alist}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\soln{This problem used to be malformed, but now it is ok.}
```
