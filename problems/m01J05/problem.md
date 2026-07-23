# m01J05

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

The informal solution was imported from the harvested APM informal-proof
corpus.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m01J05.md`
- imported-at: `2026-07-13T17:26:54.339811Z`

## Problem Statement

Raw TeX source:

```tex
Contraction mapping theorem. 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{alist}
%------------------------------------------------------------------*
\item State and prove the Contraction Mapping Theorem for an operator
$T:X\rightarrow X$ on a complete metric space $X$.
%------------------------------------------------------------------*
\item Let $F:\R^n\rightarrow \R^n$ be a smooth map and let $x_*$ be a
simple root of $F$ in the sense that $F(X_*)=0$ and the derivative
$DF(x_*)$ is invertible. For a given starting point $x_0$ consider
the Newton iteration scheme $x_{x+1}=G(x_k)$ for $k=0,1,2,\ldots $,
where $G(x)=x-DF(x)^{-1}F(X)$. Use part (a) to show that $\exists
\epsilon>0$ such that for any starting point satisfying
$|x_0-x_*|\leq\epsilon$, the sequence $x_k$ is well-defined and
converges to $x_*$. Hint: first show that $DG(x_*)=0$ and then that
$G$ is a strict contraction on a small ball centered at $x_*$.
%------------------------------------------------------------------*
\end{alist}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\soln{
(contraction mapping theorem)  \defn{
\item $X$ complete metric space
\item $f:X\rightarrow X$ contraction
\item $\exists !x\in X:f(x)=x \et \forall x'\in X:(x',f(x'),
f(f(x')), \ldots )\rightarrow x$} Let $X$ be a complete metric space
and let $f:X\rightarrow X$ be a contraction. Then there is a unique
element $x\in X$ such that (i) $f(x)=x$; and (ii) any element $x'\in
X$ has the property that the sequence $x', f(x'), f(f(x')), \ldots $
tends to $x$. Now for the proof...}
```
