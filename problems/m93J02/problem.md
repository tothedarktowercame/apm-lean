# m93J02

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

The informal solution was imported from the harvested APM informal-proof
corpus.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m93J02.md`
- imported-at: `2026-07-13T17:26:54.601791Z`

## Problem Statement

Raw TeX source:

```tex
Let $\Omega$ be a compact connected set in $\Rn$. Given a function
$f:\Omega\rightarrow \R$ define $\|f\|_{\alpha}$ to be 
$$\sup_{x\in
\Omega}\limsup_{\epsilon\rightarrow
0}\sup_{X}\{|f(z)-f(y)|/|z-y|^{\alpha}\},$$ where $X=\{(y,z)\in
\Omega\times \Omega\pipe |y-x|\leq \epsilon, |z-x|\leq \epsilon, z\neq y\}$.
Define $\|f\|_{C^{\alpha}}$ to be $$\sup_{x,y\in \Omega, x\neq
y}\{|f(x)-f(y)|/|x-y^{\alpha}|\}.$$

Prove or disprove the following statements:
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{alist}
%------------------------------------------------------------------*
\item $\|f\|_{\alpha}<\infty\Rightarrow \|f\|_{C^{\alpha}}<\infty$.
%------------------------------------------------------------------*
\item $\|f\|_{C^{\alpha}}<\infty\Rightarrow \|f\|_{\alpha}<\infty$.
%------------------------------------------------------------------*
\item $\|f\|_{\alpha}\leq K\|f\|_{C^{\alpha}}$ for some $K$ depending
only on $\Omega$.
%------------------------------------------------------------------*
\item $\|f\|_{C^{\alpha}}\leq K\|f\|_{\alpha}$ for some $K$ depending
only on $\Omega$.
%------------------------------------------------------------------*
\item If you define $|f|_{\alpha}$ to be $\|f\|_{\alpha}+\sup_{x\in
\Omega}\{|f(x)|\}$, then it is a norm.
%------------------------------------------------------------------*
\item If you define $|f|_{C^{\alpha}}$ to be
$\|f\|_{C^{\alpha}}+\sup_{x\in \Omega}\{|f(x)|\}$, then it is a norm.
%------------------------------------------------------------------*
\end{alist}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

If you answered yes to either (e) or (f), discuss whether the
resulting normed space is complete. Hint: notice that the truth or
falsehood of some of the statements implies something for some others.
```
