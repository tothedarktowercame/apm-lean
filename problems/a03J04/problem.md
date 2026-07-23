# a03J04

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

The informal solution was imported from the harvested APM informal-proof
corpus.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-a03J04.md`
- imported-at: `2026-07-13T17:26:51.763607Z`

## Problem Statement

Raw TeX source:

```tex
Let $f$ be a real-valued Lebesgue measurable function on $\Rn$ and
define the distribution function $\lambda$ on $\R$ 
by $\lambda(\alpha)=m\{x\in \Rn \pipe |f(x)|>\alpha\}$.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{alist}
%------------------------------------------------------------------*
\item Show that $\forall f\in L^1(\Rn):\int_{\Rn}|f|dx
=\int_0^{\infty}\lambda(\alpha)d\alpha$.
%------------------------------------------------------------------*
\item Suppose that $f\in L^1_W(\Rn)$, \ie\ $\sup_{\alpha>0} \{\alpha
\lambda(\alpha)\}=M<\infty$. If $0<p<1$ and $E$ is a subset
of $\Rn$ with finite measure, show that $\int_{E}|f|^p dx<\infty$.
%------------------------------------------------------------------*
\item Extend the argument from part (b) to show that $\int_E|f|^p
dx\leq c(n,p)(m(E))^{1-p}M^p$ for some constant $c(n,p)$.
%------------------------------------------------------------------*
\end{alist}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
```
