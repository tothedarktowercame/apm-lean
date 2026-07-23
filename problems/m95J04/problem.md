# m95J04

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

The informal solution was imported from the harvested APM informal-proof
corpus.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m95J04.md`
- imported-at: `2026-07-13T17:26:55.162870Z`

## Problem Statement

Raw TeX source:

```tex
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{alist}
%------------------------------------------------------------------*
\item Prove that the two-point boundary value problem $x''=f(t,x),
x(0)=x(1)=0$ has a unique solution if $f$ is continuous in
$[0,1]\times (-\infty,\infty)$ and satisfies a Lipschitz condition
$|f(t,u)-f(t,v)|\leq 7.99|u-v|$. You may use the fact that an
equivalent integral equation is $x(t)=-\int_0^1 G(t,s)f(s,x(s))ds$,
where $G(t,s)=t(1-s)$ when $0\leq t\leq s\leq 1$ and $G(s,t)=G(t,s)$.
%------------------------------------------------------------------*
\item Using the result in part (a), prove that this problem has a
unique solution $x''=\sin(x-t)\sin(x+t-1), x(0)=x(1)=0$. Prove also
that the solution function satisfies the equation $x(t)=x(1-t)$.
%------------------------------------------------------------------*
\end{alist}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
```
