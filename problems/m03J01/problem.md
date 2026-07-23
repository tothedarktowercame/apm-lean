# m03J01

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

The informal solution was imported from the harvested APM informal-proof
corpus.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m03J01.md`
- imported-at: `2026-07-13T17:26:54.540662Z`

## Problem Statement

Raw TeX source:

```tex
Let $V$ be a real Hilbert space and let $f\in V'$ be a continuous
linear functional on $V$. Define the quadratic function
$\varphi:V\rightarrow \R$ by $\varphi(v)=\frac{1}{2}\|v\|^2-f(v)$,
where the norm is that of $V$.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{alist} 
%------------------------------------------------------------------*
\item Show that $\varphi$ is bounded below and that there is
a unique point $u\in V$ at which $\varphi$ realizes its minimum value.
%------------------------------------------------------------------*
\item Show that with $u$ as in (a), $\forall v\in V: (u,v)_V =f(v)$.
%------------------------------------------------------------------*
\item Show that $f\mapsto u$ is a continuous map from $V'$ to
$V$.
%------------------------------------------------------------------*
\item Let $\Omega$ be a bounded domain in $\Rn$. 
Use appropriate choices of $V$, $f$, and $\varphi$ to show that there
is a unique weak solution to the boundary-value problem $-\triangle
u+u=F$ on $\Omega$, $u=0$ on $\partial \Omega$. Carefully specify $V$,
the assumptions on $F$, and explain what is meant by a weak solution
to the given boundary-value problem.
%------------------------------------------------------------------*
\item Suppose that we know that $F\in L^2(\Omega)$ implies $U\in
H^2(U)$. Show that with this condition $F\mapsto u$ is a continuous
map from $L^2(\Omega)$ to $H^2(\Omega)$.
%------------------------------------------------------------------*
\end{alist}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
```
