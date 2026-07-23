# a94A02

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

The informal solution was imported from the harvested APM informal-proof
corpus.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-a94A02.md`
- imported-at: `2026-07-13T17:26:52.117764Z`

## Problem Statement

Raw TeX source:

```tex
A sequence of nondecreasing, absolutely continuous functions
$f_n:[0,1]\rightarrow [0,\infty)$ satisfies
$\sum_{n=1}^{\infty}f_n(1)<\infty$. Plainly
$f(x)=\sum_{n=1}^{\infty}f_n(x)$ defines a nondecreasing continuous
function $f:[0,1]\rightarrow [0,\infty)$.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{alist}
%------------------------------------------------------------------*
\item Define $g:[0,1]\rightarrow [0,\infty]$ as follows:
$g(x)=\sum_{n=1}^{\infty}f'_n(x)$ if each of the given functions $f_n$
is differentiable at $x$, otherwise $g(x)=0$. Verify that the function
$g$ is integrable with respect to Lebesgue measure, and hence that $g$
is finite almost everywhere in $[0,1]$.
%------------------------------------------------------------------*
\item Demonstrate that $f'(x)=g(x)$ almost everywhere in $[0,1]$.
Hint: first check that $f'(x)\geq g(x)$ almost everywhere in $[0,1]$.
%------------------------------------------------------------------*
\end{alist}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
```
