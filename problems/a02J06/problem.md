# a02J06

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

Contents:
- `problem.tex`: raw problem source when available
- `informal-solution.md`: best-effort worked mathematical solution
- `proof-outline.md`: formalization-oriented outline and blockers
- `lean/Main.lean`: current Lean development
- `status.json`: machine-readable bundle status

## Imported Provenance

- imported-at: `2026-05-01T19:38:16.051451Z`
- source-frame-id: `apm-v2-a02J06-1774988737606`
- source-module-root: `ApmCanaries.Frames.A02J06.Apm_v2_a02J06_1774988737606`

## Problem Statement

Raw TeX source:

```tex
Let $D=\{z\in \C \pipe  |z|<1\}$. Let $f:D\rightarrow \C$ be a holomorphic
function that satisfies
\begin{123list}
%------------------------------------------------------------------*
\item $|f(z)|\leq 1$;
%------------------------------------------------------------------*
\item $f(0)=0$;
%------------------------------------------------------------------*
\item $f'(0)=0$.
%------------------------------------------------------------------*
\end{123list}
Show that $|f(z)|\leq |z|^2$ for all $z\in D$ and $|f''(0)|\leq
2$. Further, show that if $|f(w)|=|w|^2$ for some point $w\neq 0$ in
$D$, then there exists a constant $\beta$ with $|\beta|=1$ such that
$f(z)=\beta z^2$ for all $z\in D$.
```
