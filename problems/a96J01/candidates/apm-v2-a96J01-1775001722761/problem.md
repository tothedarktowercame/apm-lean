# a96J01

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

Contents:
- `problem.tex`: raw problem source when available
- `informal-solution.md`: best-effort worked mathematical solution
- `proof-outline.md`: formalization-oriented outline and blockers
- `lean/Main.lean`: current Lean development
- `status.json`: machine-readable bundle status

## Imported Provenance

- imported-at: `2026-05-01T19:38:16.828920Z`
- source-frame-id: `apm-v2-a96J01-1775001722761`
- source-module-root: `ApmCanaries.Frames.A96J01.Apm_v2_a96J01_1775001722761`

## Problem Statement

Raw TeX source:

```tex
For each positive integer $n$, let $f_n:[0,1]\rightarrow \R$ be a
continuous function. Suppose that $\forall x\in [0,1]: 0\leq f_n(x)$;
that the sequence of partial sums $\sum_{n=1}^N f_n(x)$ converges
uniformly on $[0,1]$ as $N\rightarrow \infty$; and that
$\sum_{n=1}^{\infty}\sup\{f_n(x)\pipe 0\leq x\leq 1\}$ diverges.
Show by giving an example that such a sequence of functions exists,
or prove that such a sequence can not exist.

\soln{ % Wed Oct 29 13:43:26 2003
The sequence of partial sums
(converges uniformly) \defn{
\item $X$ set 
\item $(Y,\rho)$ metric space 
\item $\forall n \in \N: f_n:X \rightarrow Y$ 
\item $f:X \rightarrow Y$ 
\item $\forall \epsilon>0:\exists N\in \mathbf{N}: \forall n>N: \forall x\in X: \rho(f_n(x),f(x))<\epsilon$}
if the sequence gets ``uniformly close'' to some function on $[0,1]$.
By building a sequence of functions out of disjoint pieces, eg.
$f_1$ has support only on $[0,1/2]$, $f_2$ has support only on
$[1/2,3/4]$, $f_3$ has support only on $[3/4, 7/8]$, etc., we make
our lives simpler, because the sum is not complicated to compute or
visualize. Let's further specify that $f_n$ attains its maximum
height at the midpoint of its support, and that this maximum height
is $1/n$. Then $\sum_{n=1}^{\infty}\sup\{f_n(x)\pipe 0\leq x\leq
1\}=\sum_{n=1}^{\infty} 1/n$, which diverges. However, given
$\epsilon>0$, we need only choose $N>\lceil 1/\epsilon \rceil$, and
we will have, at any point $x\in [0,1]$, $|\sum_{n=1}^N f_n(x) -
f(x)|<\epsilon$, where $f$ is the pointwise limit of the
$f_n$'s. This is because whereever $\sum_{n=1}^N f_n(x)$ is nonzero,
it is equal to $f$, and where it is zero, the difference between it
and $f$ is at most $1/N$, which is less than $\epsilon$ by our
hypothesis.}
```
