# t93A02

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

The informal solution was imported from the harvested APM informal-proof
corpus.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t93A02.md`
- imported-at: `2026-07-13T17:26:57.589858Z`

## Problem Statement

Raw TeX source:

```tex
Let $(X,d)$ be a metric space. If $A\subset X$ and $\epsilon>0$,
define $U(A,\epsilon)=\bigcup_{a\in A}B(a,\epsilon)$. Let $H$ denote
the set of all closed, bounded subsets of $X$. There is a metric $D$
on $H$ defined by $D(A,B)=\mathrm{glb}(\{\epsilon\pipe A\subset
U(B,\epsilon) \text{\ and\ } B\subset U(A,\epsilon)\})$. Prove that if
$(X,d)$ is complete, so is $(H,D)$.

Hint: let $\{A_n\}$ be a Cauchy sequence in $H$. By passing to a
subsequence, assume that $D(A_n,A_{n+1})<1/2^n$. Define $\bar{A}$ to
be the set of all points $x$ that are the limits of sequences
$\{x_n\}$ such that $x_n\in A_n$ for each $n$ and
$d(x_n,x_{n+1})<1/2^n$. Show that $A_n\rightarrow
\bar{A}$.
```
