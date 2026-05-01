# a01A12

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

This bundle was synthesized from the legacy `lean-proofs/` tree because
no proof-frame bundle existed for this problem at import time.

- legacy-source: `lean-proofs/a01A12`
- imported-at: `2026-05-01T19:52:19.159981Z`

## Problem Statement

Raw TeX source:

```tex
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{alist}
%------------------------------------------------------------------*
\item Construct a one-to-one conformal mapping of the upper half plane 
$H=\{z\in \C \pipe \Im z>0\}$ onto the angle region with interval removed
$A=\{z\in \C \pipe  z\neq 0, \arg z\in (-\pi/4,\pi/4)\}\setminus\{z\in \C:
0\leq \Re z \leq 1 \mathrm{\ and\ }\Im z=0\}$.
%------------------------------------------------------------------*
\item Describe all the one-to-one conformal mappings of $H$ onto $A$.
%------------------------------------------------------------------*
\end{alist}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\soln{ 
\begin{alist}
\item 
\begin{rlist}
\item map from upper half plane to right half plane by $f_1(z)=-iz$
\item map from right half plane to complex plane minus $(-\infty,0]$
by $f_2(z)=z^2$
\item map from the complex plane minus $(-\infty,0]$ to the complex
plane minus $(-\infty,1]$ by $f_3(z)=z+1$
\item map from the complex plane minus $(-\infty,1]$ to the right
half plane minus $(0,1]$ by $f_4(z)=\sqrt[4]{z} \pod{\text{branch cut on negative real axis}}$
\end{rlist}
\item % This one looks hard. OK, maybe not too hard - use schwarz-christoffel formula
Schwarz-Christoffel formula, considering the angle region with interval removed to 
be a weird polygon.
\end{alist}
}
```
