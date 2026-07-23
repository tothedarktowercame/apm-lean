<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM m00A01: Two closed subspaces in algebraic direct sum sit at a positive angle

*(Reading the statement as: $H$ a Hilbert space, $M,N$ closed subspaces with $M\cap N=\{0\}$
and $H=M+N$; $P_N$ the orthogonal projection onto $N$, and $P_N^\perp:=P_{N^\perp}$ the
orthogonal projection onto $N^\perp$.)*

## Why It's Hard

The decomposition $H=M+N$ with $M\cap N=\{0\}$ is an *algebraic* direct sum of closed
subspaces, but $M$ and $N$ need **not** be orthogonal, so $P_N$ restricted to $M$ is not
obviously well-behaved. The trick is to look at $Q=I-P_N$, which is the orthogonal
projection onto $N^\perp$, and to see that on $M$ it becomes a *bijection* onto $N^\perp$
— injectivity from $M\cap N=\{0\}$, surjectivity from the decomposition. Part (c) is then
the deep step: turning bijectivity into a uniform lower bound $\|Qx\|\ge\alpha\|x\|$ is
exactly the **Bounded Inverse / Open Mapping Theorem**, and it requires the *closedness*
(completeness) of $M$ and $N^\perp$. The constant $\alpha$ is the sine of the minimal
angle between $M$ and $N$.

## The Key Insight

$I-P_N=P_{N^\perp}$ on all of $H$ (orthogonal decomposition $H=N\oplus N^\perp$). So
$Q=(I-P_N)|_M=P_{N^\perp}|_M:M\to N^\perp$.
- **Injective:** $Qx=0\Rightarrow x=P_Nx\in N$, so $x\in M\cap N=\{0\}$.
- **Surjective:** for $z\in N^\perp$ write $z=m+n$ ($m\in M,n\in N$); then $z=P_{N^\perp}z
  =P_{N^\perp}m=Qm$.
- **Bounded below:** $M,N^\perp$ are complete and $Q$ is a bounded bijection, so $Q^{-1}$
  is bounded; $\|x\|=\|Q^{-1}Qx\|\le\|Q^{-1}\|\,\|Qx\|$ gives $\|Qx\|\ge\alpha\|x\|$ with
  $\alpha=\|Q^{-1}\|^{-1}>0$.

## Complete Proof

### (a) The space $N^\perp$

$$
N^\perp=\{x\in H:\ \langle x,y\rangle=0\ \text{for all }y\in N\}.
$$
It is the orthogonal complement of $N$: a closed linear subspace of $H$, and since $N$ is
closed, $H=N\oplus N^\perp$ is an orthogonal direct sum. The associated orthogonal
projections satisfy $P_N+P_{N^\perp}=I$ and $P_N P_{N^\perp}=0$.

### (b) $Q=I-P_N$ equals $P_{N^\perp}$ on $M$, and is a bijection $M\to N^\perp$

From $P_N+P_{N^\perp}=I$ we get, as operators on all of $H$,
$$
Q=I-P_N=P_{N^\perp}=:P_N^\perp .
$$
In particular $Q$ maps into $N^\perp$, and restricted to $M$ it coincides with
$P_{N^\perp}|_M$ (and with $P_N^\perp|_M$). Now view $Q:M\to N^\perp$.

**Injective.** Let $x\in M$ with $Qx=0$. Then $(I-P_N)x=0$, i.e. $x=P_Nx\in N$. Thus
$x\in M\cap N=\{0\}$, so $x=0$. Hence $Q$ is injective on $M$.

**Surjective.** Let $z\in N^\perp$. Since $H=M+N$, write $z=m+n$ with $m\in M$, $n\in N$.
Because $z\in N^\perp$, $P_{N^\perp}z=z$; and $P_{N^\perp}n=0$ (as $n\in N$). Therefore
$$
z=P_{N^\perp}z=P_{N^\perp}(m+n)=P_{N^\perp}m=Qm,
$$
with $m\in M$. So every $z\in N^\perp$ is in the image of $Q$, i.e. $Q$ is surjective onto
$N^\perp$.

Thus $Q:M\to N^\perp$ is a linear bijection. $\quad\checkmark$

### (c) A uniform lower bound: $\exists\,\alpha>0$ with $\|x-P_Nx\|\ge\alpha\|x\|$ on $M$

Note $\|x-P_Nx\|=\|Qx\|$, so the claim is that $Q$ is bounded below on $M$.

$M$ and $N^\perp$ are closed subspaces of the Hilbert space $H$, hence are themselves
complete (Banach, indeed Hilbert) spaces. The operator $Q=P_{N^\perp}|_M$ is bounded:
orthogonal projections have norm $\le1$, so
$$
\|Qx\|=\|P_{N^\perp}x\|\le\|x\|\qquad(x\in M).
$$
By part (b), $Q:M\to N^\perp$ is a bounded **bijection** between Banach spaces. By the
Bounded Inverse Theorem (a consequence of the Open Mapping Theorem), its inverse
$Q^{-1}:N^\perp\to M$ is bounded; let $C=\|Q^{-1}\|<\infty$ (note $C>0$ since
$Q^{-1}\neq0$). Then for every $x\in M$,
$$
\|x\|=\|Q^{-1}(Qx)\|\le C\,\|Qx\|,\qquad\text{i.e.}\qquad \|Qx\|\ge\frac1C\,\|x\|.
$$
Setting $\alpha=\tfrac1C=\|Q^{-1}\|^{-1}>0$ gives
$$
\|x-P_Nx\|=\|Qx\|\ge\alpha\,\|x\|\qquad\text{for all }x\in M. \qquad\blacksquare
$$

### Remark

The estimate in (c) says $M$ and $N$ are "uniformly transverse": the quantity $\alpha\le
\inf_{x\in M\setminus\{0\}}\frac{\|x-P_Nx\|}{\|x\|}=\inf_{x\in M\setminus\{0\}}
\frac{\operatorname{dist}(x,N)}{\|x\|}$ is positive, and it is precisely $\sin\theta$
where $\theta$ is the minimal (Friedrichs) angle between the subspaces. Closedness is
essential: if $M+N$ failed to be closed (or $M,N$ were not closed), $Q$ could be a
bounded bijection onto a *dense* but proper image and have unbounded inverse, with
$\alpha=0$ — exactly the situation of two subspaces meeting at angle zero. The same
argument shows the (non-orthogonal) projection of $H$ onto $M$ along $N$ is a *bounded*
operator, i.e. the algebraic direct sum $H=M\oplus N$ is in fact a topological direct sum.
