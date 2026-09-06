# APM tunk03: Closed equivalence relations and Hausdorff quotients

Let $q:X\to X/{\sim}$ be the quotient map and let $\Delta$ be the diagonal of
the quotient. The relation satisfies

$$
R=\{(x,y):x\sim y\}=(q\times q)^{-1}(\Delta).
$$

If the quotient is Hausdorff, its diagonal is closed. Since $q\times q$ is
continuous, $R$ is closed.

Conversely, suppose $R$ is closed and take distinct classes $q(x)\ne q(y)$.
Then $(x,y)$ lies in the open complement of $R$, so there are open
neighborhoods $U\ni x$ and $V\ni y$ with

$$
(U\times V)\cap R=\varnothing.
$$

Because the equivalence relation is open, $q$ is an open map. Hence $q(U)$ and
$q(V)$ are open neighborhoods of $q(x)$ and $q(y)$. They are disjoint: a class
in their intersection would have representatives $u\in U$ and $v\in V$ with
$u\sim v$, placing $(u,v)$ in $(U\times V)\cap R$. Thus distinct quotient
points have disjoint open neighborhoods, and $X/{\sim}$ is Hausdorff.

The openness assumption is used exactly in the reverse implication. The
forward implication needs only continuity of the quotient projection. This is
the same exercise and argument as `t94J11`.
