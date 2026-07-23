# m96A05

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

The informal solution was imported from the harvested APM informal-proof
corpus.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m96A05.md`
- imported-at: `2026-07-13T17:26:55.405295Z`

## Problem Statement

Raw TeX source:

```tex
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{alist}
%------------------------------------------------------------------*
\item Show how the approximate formulas $f'(t)\approx
\frac{f(t+h)-f(t-h)}{2h}$, $f''(t)\approx
\frac{f(t+h)-2f(t)+f(t-h)}{h^2}$ can be used to obtain an approximate
solution to the following two-point boundary value problem:
$u''(t)+a(t)u'(t)+b(t)u(t)=c(t)$ ($0<t<1$), $u(0)=0,u(1)=1$. 

(Here $a$, $b$, and $c$ are continuous on $[0,1]$.)
%------------------------------------------------------------------*
\item Prove that if a uniform mesh is used in the numerical procedure of
part (a), that is, $t_i=ih$ ($i\in 0,1,\ldots ,n+1$, $h=1/(n+1)$),
then the resulting system of linear equations will be nonsingular,
provided that $b(t)<0$ and $h$ is sufficiently small.
%------------------------------------------------------------------*
\end{alist}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
```
