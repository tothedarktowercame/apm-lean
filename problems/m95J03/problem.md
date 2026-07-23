# m95J03

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

The informal solution was imported from the harvested APM informal-proof
corpus.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m95J03.md`
- imported-at: `2026-07-13T17:26:55.127833Z`

## Problem Statement

Raw TeX source:

```tex
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{alist}
%------------------------------------------------------------------*
\item Criticize the following statement.

If $A$ is an $m\times n$ matrix and we want to find a solution to the
equation to the equation $Ax=b$, we can employ a left inverse of $A$,
\ie\ an $n\times m$ matrix $L$ such that $LA=I$. 

Hint: start with $Ax=b$, multiply by $L$ and get $LAx=Lb$ or $x=Lb$.
%------------------------------------------------------------------*
\item Is the Jordan canonical form of a square matrix a continuous
function of the matrix? In discussing this, use the following example:
$$B(\rho)=
\left(\begin{array}{cccc}
\rho & 0 & 0 & 0 \\
1 & \rho^2 & 0 & 0 \\ 0 & 1 & \rho^3 & 0 \\ 0 & 0 & 1 & \rho^4
\end{array}\right)$$
%------------------------------------------------------------------*
\item Define $e^A$ for an arbitrary square matrix $A$ and describe how
to compute it using the Jordan cannonical form.
%------------------------------------------------------------------*
\item Compute $e^{B(0)}$ where $B(\rho)$ is as defined in part (b).
%------------------------------------------------------------------*
\item Solve the initial value problem $\mathbf{x}'=B(0)\mathbf{x},
\mathbf{x}(0)=\mathbf{v}$. (Here $\mathbf{v}$ is an arbitrary
$4$-vector.)
%------------------------------------------------------------------*
\end{alist}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
```
