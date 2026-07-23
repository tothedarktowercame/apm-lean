# a96A01

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

The informal solution was imported from the harvested APM informal-proof
corpus.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-a96A01.md`
- imported-at: `2026-07-13T17:26:52.448038Z`

## Problem Statement

Raw TeX source:

```tex
Suppose that $f:[0,1]\rightarrow \R$ is a Lebesgue integrable function
and that $0<p\leq 1$. Let $\|f\|_p=(\int_0^1|f(x)|^pdx)^{1/p}$. 

Note that $\|\cdot \|_p$ does nat satisfy the triangle inequality if
$p<1$.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{alist}
%------------------------------------------------------------------*
\item Show that $\|f\|_p\leq \|f\|_q$ when $0<p<q\leq 1$, thus ensuring
that $\|f\|_p$ is finite for all $p$ in question and that
$L=\lim_{p\rightarrow 0}$ exists.
%------------------------------------------------------------------*
\item Under the assumption that $L>0$, prove that $|f(x)|>0$ for
almost every $x$ in $[0,1]$. \emph{N.B.}, $t^p\leq 1+t$ when $t\geq 0$
and $0<p\leq 1$.
%------------------------------------------------------------------*
\item Verif that $L\geq \exp(\int_0^1 \log |f(x)|dx)$.
%------------------------------------------------------------------*
\end{alist}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
```
