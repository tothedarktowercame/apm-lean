# a92J03

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

The informal solution was imported from the harvested APM informal-proof
corpus.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-a92J03.md`
- imported-at: `2026-07-13T17:26:51.869852Z`

## Problem Statement

Raw TeX source:

```tex
For each $f\in L^1(\R)$, define $\hat{f}(\xi):\R\rightarrow \C$ by
$\hat{f}(\xi)=\int_{-\infty}^{\infty}f(x)e^{ix\xi}dx$. Prove the
following results stating carefully any theorem you use.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{alist}
%------------------------------------------------------------------*
\item $\hat{f}(\xi)$ is a continuous function of $\xi$.
%------------------------------------------------------------------*
\item $\sup_{\xi}\{|\hat{f}(\xi)|\}\leq
\int_{-\infty}^{\infty}|f(x)|dx$.
%------------------------------------------------------------------*
\item If $f$ is a finite linear combination of characteristic functions
of intervals, then $\lim_{|\xi|\rightarrow
\infty}|\hat{f}(\xi)|=0$. 
%------------------------------------------------------------------*
\end{alist}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
Deduce that the mapping defined by $f\mapsto \hat{f}$ is a linear
mapping from $L^1(\R)$ into the space $C_0(\R)$ of continuous
functions $\varphi$ such that $\lim_{|\xi|\rightarrow
\infty}|\varphi(\xi)|=0$.
```
