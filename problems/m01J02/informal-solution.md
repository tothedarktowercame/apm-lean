<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM m01J02: Sums and products of orthogonal projections

*(In (c), "$P\cap N$" is read as $M\cap N$.)*

## Why It's Hard

Everything hinges on the algebraic characterization **orthogonal projection $=$
idempotent $+$ self-adjoint** ($P^2=P$, $P^*=P$). Once that is in hand, both parts become
operator-identity manipulations, but the manipulations are delicate: in (b) you must turn
"the sum is idempotent" into "$M\perp N$" by squeezing the cross terms
$P_MP_N+P_NP_M=0$ down to $P_NP_M=0$ using self-adjointness and positivity ($\langle
P_Ny,y\rangle=\|P_Ny\|^2$); in (c) the equivalence "product is a projection $\iff$ they
commute" is really "self-adjoint $\iff$ commute," and then identifying the range as $M\cap
N$ uses commutativity to land the image in *both* subspaces.

## The Key Insight

- **(a)** $P_M$ is bounded, linear, $P_M^2=P_M$, $P_M^*=P_M$, with range $M$ —
  equivalently $P_Mx\in M$ and $x-P_Mx\perp M$.
- **(b)** $(P_M+P_N)^2=P_M+P_N\iff P_MP_N+P_NP_M=0$; sandwiching by $P_M$ gives
  $P_MP_NP_M=0$, hence $\|P_NP_Mx\|^2=\langle P_MP_NP_Mx,x\rangle=0$, so $P_NP_M=0$, i.e.
  $M\perp N$. Conversely $M\perp N$ makes $P_M+P_N$ the orthogonal projection onto the
  closed sum $M\oplus N$.
- **(c)** $P_MP_N$ self-adjoint $\iff(P_MP_N)^*=P_NP_M=P_MP_N$ (commute); commuting makes
  it idempotent and self-adjoint, hence a projection, with range $M\cap N$.

## Complete Proof

$H$ is a Hilbert space, $M,N$ closed subspaces, $P_M,P_N$ the orthogonal projections.

### (a) Definition of orthogonal projection

$P_M:H\to H$ is the **orthogonal projection onto $M$** if it is a bounded linear operator
that is **idempotent** and **self-adjoint**:
$$
P_M^2=P_M,\qquad P_M^*=P_M,
$$
with range $M$. Equivalently (and this is the geometric content): for every $x\in H$,
$P_Mx$ is the unique point of $M$ satisfying $P_Mx\in M$ and $x-P_Mx\perp M$ (the nearest
point of $M$ to $x$). Then $I-P_M=P_{M^\perp}$, $P_M|_M=\mathrm{id}$, $P_M|_{M^\perp}=0$.
We use freely that for an orthogonal projection $\langle P x,y\rangle=\langle x,Py\rangle$
and $\langle Px,x\rangle=\|Px\|^2\ge0$.

### (b) $P_M+P_N=P_{M+N}\iff M\perp N$

**($\Leftarrow$).** Suppose $M\perp N$. Then $M+N=M\oplus N$ is an orthogonal direct sum,
hence closed, and $P_{M+N}$ is defined. For $x\in H$ put $y=P_Mx+P_Nx\in M+N$. We check
$x-y\perp M+N$. For $m\in M$,
$$
\langle x-P_Mx-P_Nx,\,m\rangle=\underbrace{\langle x-P_Mx,m\rangle}_{=0}-\underbrace{\langle P_Nx,m\rangle}_{=0}=0,
$$
the first since $x-P_Mx\perp M$, the second since $P_Nx\in N\perp M$. Symmetrically $x-y
\perp N$, so $x-y\perp M+N$. As $y\in M+N$ and $x-y\perp(M+N)$, by uniqueness of the
orthogonal decomposition $y=P_{M+N}x$. Hence $P_M+P_N=P_{M+N}$.

**($\Rightarrow$).** Suppose $P_M+P_N=P_{M+N}$ is an orthogonal projection, hence
idempotent. Expanding $(P_M+P_N)^2=P_M+P_N$ and using $P_M^2=P_M$, $P_N^2=P_N$,
$$
P_M+P_MP_N+P_NP_M+P_N=P_M+P_N\quad\Longrightarrow\quad P_MP_N+P_NP_M=0 .
$$
Multiply on both sides by $P_M$ and use $P_M^2=P_M$:
$$
P_M(P_MP_N+P_NP_M)P_M=2\,P_MP_NP_M=0\ \Longrightarrow\ P_MP_NP_M=0 .
$$
Then for every $x$, using self-adjointness of $P_M$ and $\langle P_N z,z\rangle=\|P_Nz\|^2$,
$$
0=\langle P_MP_NP_Mx,\,x\rangle=\langle P_N(P_Mx),\,P_Mx\rangle=\|P_NP_Mx\|^2 ,
$$
so $P_NP_M=0$. Thus for any $m\in M$, $P_Nm=P_NP_Mm=0$, i.e. $m\in N^\perp$. Hence
$M\subseteq N^\perp$, i.e. $M\perp N$. $\quad\checkmark$

### (c) $P_MP_N$ is an orthogonal projection $\iff P_MP_N=P_NP_M$, and then it projects onto $M\cap N$

**($\Rightarrow$).** If $P:=P_MP_N$ is an orthogonal projection, it is self-adjoint, so
$$
P_MP_N=P=P^*=(P_MP_N)^*=P_N^*P_M^*=P_NP_M ,
$$
i.e. $P_M$ and $P_N$ commute.

**($\Leftarrow$).** Suppose $P_MP_N=P_NP_M$, and set $P=P_MP_N$. Then
$$
P^2=P_MP_NP_MP_N=P_M(P_MP_N)P_N=P_M^2P_N^2=P_MP_N=P
$$
(idempotent, using commutativity to swap $P_NP_M\to P_MP_N$), and
$$
P^*=(P_MP_N)^*=P_NP_M=P_MP_N=P
$$
(self-adjoint). So $P$ is idempotent and self-adjoint, hence an orthogonal projection.

**Range is $M\cap N$.** Assume $P_M,P_N$ commute and $P=P_MP_N$.
- For any $x$, $Px=P_MP_Nx\in M$ (range of $P_M$), and also $Px=P_NP_Mx\in N$ (range of
  $P_N$, using commutativity). So $\operatorname{ran}P\subseteq M\cap N$.
- If $y\in M\cap N$, then $P_Ny=y$ and $P_My=y$, so $Py=P_MP_Ny=P_My=y$. Thus $y\in
  \operatorname{ran}P$ and $P$ fixes $y$.

Hence $\operatorname{ran}P=M\cap N$ and $P$ fixes $M\cap N$ pointwise. An orthogonal
projection is determined by its range, so $P=P_MP_N=P_{M\cap N}$. $\quad\blacksquare$

### Remark

The two parts contrast neatly: a **sum** of orthogonal projections is again one exactly
when the subspaces are *orthogonal* (it then projects onto $M\oplus N$), whereas a
**product** is one exactly when the projections *commute* (it then projects onto $M\cap
N$). Both are special cases of the principle that an idempotent is an *orthogonal*
projection iff it is self-adjoint, and the failure modes are instructive: $P_MP_N$ for
non-commuting projections is the iterate underlying the von Neumann alternating-projection
theorem, whose limit *is* $P_{M\cap N}$ even when a single product is not a projection.
