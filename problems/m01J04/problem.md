# m01J04

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

The informal solution was imported from the harvested APM informal-proof
corpus.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m01J04.md`
- imported-at: `2026-07-13T17:26:54.334771Z`

## Problem Statement

Raw TeX source:

```tex
Weak convergence. Suppose that $\Omega$ is a domain in $\R^d$.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{alist}
%------------------------------------------------------------------*
\item If $X$ is a Banach space and $f_n$ converges weakly to $f$ in $X$,
$g_n$ converges strongly to $g$ in $X^*$, show that the duality
pairing converges as $\langle f_n,g_n \rangle\rightarrow \langle f,g
\rangle$.
%------------------------------------------------------------------*
\item If $\{u_n\}_{n=1}^{\infty}$ is a bounded sequence in
$H^1(\Omega)$, prove that there is a subsequence
$\{u_{n_k}\}_{k=1}^{\infty}$ such that the vector $u_{n_k}\nabla
u_{n_k}$ converges to $u\nabla u$ for some $u\in H^1(\Omega)$ in the
sense that for any vector $\psi\in (L_{\infty}(\Omega))^d$ we have
$\lim_{n\rightarrow \infty}\int_{\Omega} u_{n_k}\nabla u_{n_k}\cdot
\psi\ dx=\int_{\Omega}u \nabla u \cdot \psi\ dx$.
%------------------------------------------------------------------*
\item Suppose that $f_n$ converges weakly to $f$ in $H^1(\Omega)$ and the
vector sequence $\mathbf{v}_n$ converges weakly to $\mathbf{v}$ in
$(L_2(\Omega))^d$ -- in other words, each component converges weakly
in $L_2(\Omega)$. If $\nabla \cdot \mathbf{v}_n$ converges strongly in
$H^{-1}(\Omega)$, show that for any $\varphi\in C^{\infty}_0(\Omega)$
that $\lim_{n\rightarrow \infty}\int_{\Omega}\mathbf{v}_n\cdot \nabla
f_n\varphi dx=\int_{\Omega}\mathbf{v}\cdot \nabla f\varphi dx$.
%------------------------------------------------------------------*
\end{alist}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
```
