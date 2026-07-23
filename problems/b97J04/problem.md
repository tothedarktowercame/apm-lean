# b97J04

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

The informal solution was imported from the harvested APM informal-proof
corpus.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b97J04.md`
- imported-at: `2026-07-13T17:26:54.132576Z`

## Problem Statement

Raw TeX source:

```tex
Let $F$ be an algebraically closed field, $V$ a finite dimensional
vector space over $F$ and $T:V\rightarrow V$ a linear map of $V$ into
itself (\ie\ $T\in \mathrm{End}_F(V)$). Recall that $T$ is
\emph{nilpotent} if $T^k=0$ for some integer $k$ and \emph{unipotent}
if it is of the form $T=I+N$ where $I$ is the identity and $N$ is
nilpotent. Also, $T$ is \emph{semisimple} if its minimal polynomial
has distinct roots \ie\ $T$ if is diagonalizable.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{alist}
%------------------------------------------------------------------*
\item Prove that there are $S,N\in \mathrm{End}_F(V)$ such that
$S$ is simisimple, $N$ nilpotent, $SN=NS$ and $T=S+N$. Note there is
more than one way to do this. It follows from a result on the syllabus
for the exam. It can also be proved using the ideas in part (c) below.
%------------------------------------------------------------------*
\item Prove that $S$ and $T$ have the same characteristic polynomial.
%------------------------------------------------------------------*
\item The purpose of this part is to show that the $S$ and $N$ found
in part (a) are unique. Thus, suppose that $S$ and $N$ are elements of
$\mathrm{End}_F(V)$ satisfying these conditions: $S$ is semisimple,
$N$ is nilpotent, $SN=NS$ and $T=S+N$. 

For each $\lambda\in F$, let $V_{\lambda}=\{v\in V\pipe Sv=\lambda
v\}$ and let $W_{\lambda}=\{v\in V \pipe \exists k\in \Z, k>0,
(T-\lambda)^kv=0\}$. Prove that 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{rlist}
%------------------------------------------------------------------*
\item $V_{\lambda}\subset W_{\lambda}$ 
%------------------------------------------------------------------*
\item $V_{\lambda} \supset W_{\lambda}$ 
%------------------------------------------------------------------*
\end{rlist}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
Conclude that $S$ and $N$ are uniquely determined by $T$.

Hint for (ii): $V$ is the direct sum of the $V_{\lambda}$'s and is
also the direct sum of the $W_{\lambda}$'s. (Why?)
%------------------------------------------------------------------*
\item Suppose that $T\in GL(V)$ (\ie\ $T$ is invertble). Prove that there
is are unique $S,N\in GL(V)$ such that $S$ is semisimple, $U$ is
unipotent, $SU=US$ and $T=SU$.
%------------------------------------------------------------------*
\end{alist}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
```
