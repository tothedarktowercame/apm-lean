# t96J01

## Bundle Overview

This directory is the canonical APM problem bundle for this problem.

The informal solution was imported from the harvested APM informal-proof
corpus.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t96J01.md`
- imported-at: `2026-07-13T17:26:58.394495Z`

## Problem Statement

Raw TeX source:

```tex
Let $f:X\rightarrow Y$ be a continuous surjection, where $X$ is
compact and $Y$ Hausdorff. Let $A$ and $B$ be closed subsets of $X$
such that $f(A)\cap f(B)=\phi$. Show that there exists a continous
function $g:Y\rightarrow [0,1]$ such that $g\circ f(x)=0$ if $x\in A$
and $g\circ f(x)=1$ if $x\in B$. 

\soln{ % this looks like a good beginning to me
The solution to this problem comprises in the proof (a) of
``urysohn's lemma'', which says that in a normal space, every pair of
disjoint closed sets is associated with some map that takes the value
$0$ on one of the sets and $1$ on the other; \emph{and}, (b) of the
fact that any compact hausdorff space is a normal space; \emph{and},
(c) of the fact that whenever we have a continuous, surjective map
from a compact topological space to another topological space, the
image-space is also compact. With these steps in mind, here is the
proof:}
```
