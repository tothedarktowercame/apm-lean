# APM tunk02: Products of regular spaces

Use the neighborhood form of regularity: for every point $x$ in an open set
$O$, there is an open $U$ such that

$$
x\in U\subseteq\overline U\subseteq O.
$$

This is equivalent to separation of a point from a closed set by disjoint open
neighborhoods.

Let $(x,y)$ lie in an open set $W\subseteq X\times Y$. Choose a basic open box
$A\times B$ with

$$
(x,y)\in A\times B\subseteq W.
$$

Regularity of the factors gives open sets $U\subseteq X$ and $V\subseteq Y$
such that

$$
x\in U\subseteq\overline U\subseteq A,
\qquad
y\in V\subseteq\overline V\subseteq B.
$$

The closure of a product is the product of the closures, so

$$
(x,y)\in U\times V
\subseteq\overline{U\times V}
=\overline U\times\overline V
\subseteq A\times B\subseteq W.
$$

The neighborhood criterion proves that $X\times Y$ is regular. If one's
definition of regular also includes the $T_1$ axiom, products preserve $T_1$
as well, since points in the product are closed.
