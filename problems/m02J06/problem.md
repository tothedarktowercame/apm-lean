# m02J06

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

The informal solution was imported from the harvested APM informal-proof
corpus.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m02J06.md`
- imported-at: `2026-07-13T17:26:54.529654Z`

## Problem Statement

Raw TeX source:

```tex
Let $K$ be the set of functions in $L^1(\R)$ such that
$\int|f(x+h)-f(x)|dx\leq h^{1/2}; \int|f(x)|dx\leq 1; |x|=0\Rightarrow
f(x)=0$. Let $\varphi_{\epsilon}(\cdot )$ be a mollifier constructed
from a function $\varphi\in C_{0}^{\infty}(\R)$ with $\int
\varphi(x)dx=1; |x|\geq 1\Rightarrow \varphi(x)=0; \max |\varphi|=M$
by putting
$\varphi_{\epsilon}(x)=\frac{1}{\epsilon}\varphi(\frac{x}{\epsilon})$. Prove that 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{alist}
%------------------------------------------------------------------*
\item $\|f-f \ast \varphi_{\epsilon}\|\leq \epsilon^{1/2}$; 
%------------------------------------------------------------------*
\item the set $K_{\epsilon}=\{f \ast \varphi_{\epsilon} \pipe  f\in K\}$ is
equicontinuous, specifically $|f \ast
\varphi_{\epsilon}(x)-f \ast
\varphi_{\epsilon}(y)|\leq \frac{M}{\epsilon}|x-y|^{1/2}$ with the same
$M$ as above;
%------------------------------------------------------------------*
\item the set $K$ is compact.
%------------------------------------------------------------------*
\end{alist}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
```
