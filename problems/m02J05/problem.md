# m02J05

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

The informal solution was imported from the harvested APM informal-proof
corpus.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m02J05.md`
- imported-at: `2026-07-13T17:26:54.521616Z`

## Problem Statement

Raw TeX source:

```tex
Suppose that $\alpha: [0,\infty) \rightarrow \R$ is continuous and
strictly increasing from $\alpha(0)=0$ to $\lim_{t\rightarrow
\infty} \alpha(t)=\infty$. Let $A(t)=\int_{0}^t\alpha(\tau)d\tau$ and
$\tilde{A}(t)=\int_{0}^t\alpha^{-1}(\tau)d\tau$, where $\alpha^{-1}$
is the inverse of $\alpha$. Let $$K_A=\{u: u\ \mathrm{measurable},
\int_{0}^1A(|u(x)|)dx<\infty\}.$$ 
Define the Orlicz space $L_A$ to be the set of $u$'s that are
measurable and $\exists \lambda\neq 0,
\lambda u \in K_A$.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{alist}
%------------------------------------------------------------------*
\item Prove that $K_A$ is convex;
%------------------------------------------------------------------*
\item Prove that $L_A$ is a linear space (\ie\ a vector space);
%------------------------------------------------------------------*
\item Define $\|u\|_A=\inf \{\lambda>0: \int_{0}^1 A
(\frac{|u(x)|}{\lambda}) dx \leq 1\}$ and show that $\|u\|_A$ is a
well-defined norm on $L_A$.
%------------------------------------------------------------------*
\item Prove the following variant of H\"older's inequality: 
$\int_{0}^1 u(x)v(x)dx \leq 2\|u\|_A \|v\|_{\tilde{A}}$. Hint: first
show that for any $s,t\in [0,\infty)$ that $st\leq A(s)+\tilde{A}(t)$.
%------------------------------------------------------------------*
\end{alist}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
```
