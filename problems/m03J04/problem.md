# m03J04

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

The informal solution was imported from the harvested APM informal-proof
corpus.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m03J04.md`
- imported-at: `2026-07-13T17:26:54.555420Z`

## Problem Statement

Raw TeX source:

```tex
Let $V$ and $W$ be Hilbert spaces and let $B:V\rightarrow W'$ be a
continuous linear map.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{alist}
%------------------------------------------------------------------*
\item Define the \emph{adjoint} operator $B':W\rightarrow V'$ 
$B'w(v)=Bv(w)$. Show that $B'$ is continuous and that its adjoint is
equal to $B$.
%------------------------------------------------------------------*
\item Let $U$ be a subset of $W$. Define the \emph{annihilator} of
$U$ to be the set of functionals $U^o=\{f\in W'\pipe \forall w\in
U:f(w)=0\}$. Show that $U^o$ is a closed subspace of $W'$.
%------------------------------------------------------------------*
\item Show that the closure of the image of $B$ is the annihilator
of the kernel of $B'$, \ie\ $\overline{B(V)}=(\ker B')^o$.
%------------------------------------------------------------------*
\item Show that if $\exists \alpha>0:\forall v\in V: \sup_{w\in W}
B_v(w)/\|w\|_W \geq \alpha \|v\|_V$ then $B$ is an isomorphism of $V$
with $(\ker B')^o$.
%------------------------------------------------------------------*
\end{alist}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
```
