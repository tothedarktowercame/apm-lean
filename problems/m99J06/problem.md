# m99J06

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

The informal solution was imported from the harvested APM informal-proof
corpus.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m99J06.md`
- imported-at: `2026-07-13T17:26:56.309176Z`

## Problem Statement

Raw TeX source:

```tex
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{alist}
%------------------------------------------------------------------*
\item Describe the \emph{Sobolev space} $H_0^1(0,1)$ over the interval 
$\Omega=(0,1)$. 
%------------------------------------------------------------------*
\item Let $f\in L^2(0,1)$ be given. Show that the weak problem 
of finding $u\in H_0^1(0,1)$ such that
$(u,v)_{L^2(0,1)}+(u',v')_{L^2(0,1)}=(f,v)_{L^2(0,1)}$ for all $v\in
H_0^1(0,1)$ is equivalent to the strong problem of finding $u$ such
that $u-u''=f$ and $u(0)=u(1)=0$.
%------------------------------------------------------------------*
\item For each $n\geq 1$ let $V_n$ be a finite dimensional subspace
with $V_1\subset V_2\subset V_3\subset \ldots V\equiv H_0^1(0,1)$ and
assume that $\bigcup \{V_n \pipe n\geq 1\}$ is dense in $V$. For each $n\geq
1$, show that there is a unique $u_n\in V_n$ such that
$(u,v)_{L^2(0,1)}+(u',v')_{L^2(0,1)}=(f,v)_{L^2(0,1)}$ for all $v\in
V_n$. Hint: why is it sufficient to show uniqueness?
%------------------------------------------------------------------*
\item Show that there exists a $u\in H_0^1(0,1)$ such that $u_n$
converges weakly to $u$ in $H_0^1(0,1)$. Hint: show that the sequence
$\{u_n\}$ is bounded.
%------------------------------------------------------------------*
\item Show that the limit $u$ is a solution of the weak problem in
part (b).
%------------------------------------------------------------------*
\end{alist}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
```
