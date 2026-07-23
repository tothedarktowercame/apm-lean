# m93J05

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

The informal solution was imported from the harvested APM informal-proof
corpus.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m93J05.md`
- imported-at: `2026-07-13T17:26:54.641772Z`

## Problem Statement

Raw TeX source:

```tex
Let $\Phi:L^p(\Son)\rightarrow L^p(\Son)$ ($1<p<\infty$) be the map
that takes a function into its truncated Fourier series. \Ie\ if
$f(\theta)=a_0+\sum_{j=1}^{\infty}a_j\cos(j 2\pi\theta)+b_j \sin (2\pi
j \theta)$ then $\Phi[f](\theta)=a_0+\sum_{j=1}^N a_j \cos(j 2\pi
\theta)+b_j \sin (2\pi j \theta)$.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{alist}
%------------------------------------------------------------------*
\item Describe the adjoint $\Phi^*: (L^p(\Son))^*\rightarrow
(L^p(\Son))^*$.
%------------------------------------------------------------------*
\item Describe the kernel and cokernel of $\Phi$.
%------------------------------------------------------------------*
\item Prove that given any $g\in L^q(\Son)$ where $1/p+1/q=1$, the
functional
$J_g(f)=\|f-\Phi[f]\|^{p}_{L^p}+\|\Phi[f]\|_{L^2}^2+\int_{\Son}fg$ is
lower semicontinuous.
%------------------------------------------------------------------*
\item Prove that $J_g$ assumes a minimum value.
%------------------------------------------------------------------*
\item Derive equations for the minimum of $J_g$.
%------------------------------------------------------------------*
\end{alist}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\soln{A better notation for $\Phi$ would be $\Phi_N$, since it is a
map that takes the fourier series to a specific truncation.
The kernel should be anything whose first $N$ terms are $0$.  The
cokernel should be anything whose first $N$ terms are not zero.
I wonder if it is true that every function in $L^p(\Son)$ is
``correctly represented'' by its Fourier series. This is probably
true.
We need to know conditions for an integral operator to assume a
minimum (the $p$-norm and $2$-norm are integral operators as well as
anything else).}
```
