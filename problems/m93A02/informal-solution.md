<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m93A02: Solving a quadratic equation in Banach space by contraction — and why surjectivity is load-bearing

## Why It's Hard

The equation $Lh + Q(h,h) = k$ is **nonlinear** (quadratic in $h$), so no
linear-algebra inverse solves it. The right instrument is the **Banach
fixed-point theorem** applied to
$$T(h) = L^{-1}\big(k - Q(h,h)\big),$$
but three things must come together:

1. **Recover $L^{-1}$.** $L$ is given only as *surjective* and *bounded below*
   ($\|Lh\|\ge\delta\|h\|$). One must notice that bounded-below $\Rightarrow$
   injective, so together with surjectivity $L$ is a bijection, and the
   bound-below constant hands you $\|L^{-1}\|\le 1/\delta$ **for free** — without
   even assuming $L$ is continuous.
2. **Juggle two competing inequalities.** Picking the ball radius $r$ on which
   $T$ operates is a balancing act: the **self-map** condition wants $r$ *large*
   relative to $\|k\|$, while the **contraction** condition (factor $\sim
   2Mr/\delta$) wants $r$ *small* in absolute terms. The sweet spot is
   $r\sim\|k\|/\delta$, which exists only when $\|k\|$ is small — that smallness
   threshold *is* the $\epsilon$ being sought.
3. **Flip the intuition for (b).** Surjectivity looks like a throwaway
   hypothesis; part (b) reveals it as the **load-bearing** one. The clean
   counterexample has the nonlinear solution-surface lying *tangent* to
   $\operatorname{ran}L$ at the origin, so a whole cone of arbitrarily small $k$
   transverse to the range stays unreachable.

## The Key Insight

Surjective + bounded-below makes $L^{-1}$ exist and bounded by $1/\delta$, which
**recasts the equation as a fixed point**
$$h = L^{-1}k - L^{-1}Q(h,h).$$
The nonlinear part is *quadratic*, so its Lipschitz constant on a ball of radius
$r$ is $\sim 2Mr/\delta$ — proportional to $r$, hence $<1$ once $r$ is small.
This is the engine of the **inverse function theorem**: a map whose derivative at
$0$ (here $L$) is invertible is locally invertible, with the quadratic remainder
controlled by contraction. Part (b) is the converse lesson: if the derivative
$L$ is merely injective (bounded below) but *not onto*, local solvability onto a
full neighborhood **fails** — the image is a thin tangent surface, and small
$k$ off it have no preimage.

## Complete Proof

**Preliminary: $L^{-1}$ exists and $\|L^{-1}\|\le 1/\delta$.** The bound
$\|Lh\|\ge\delta\|h\|$ forces $L$ injective ($Lh=0\Rightarrow\|h\|=0$). With
surjectivity, $L:H\to K$ is a bijection. For any $k\in K$ write $k=Lh$ with
$h=L^{-1}k$; then $\|k\|=\|Lh\|\ge\delta\|h\|=\delta\|L^{-1}k\|$, so
$$\|L^{-1}k\|\le\tfrac1\delta\|k\|\qquad\forall k\in K. \tag{$\dagger$}$$

### Part (a) — Existence and the linear bound

Solving $Lh+Q(h,h)=k$ is equivalent (apply $L^{-1}$) to finding a fixed point of
$$T(h):=L^{-1}k-L^{-1}Q(h,h).$$

**Claim.** With
$$\boxed{\ \epsilon=\frac{\delta^2}{4M},\qquad B=\frac{2}{\delta}\ }$$
every $k$ with $0<\|k\|<\epsilon$ admits a solution $h$ with $\|h\|<B\|k\|$.

Fix such a $k$ and set $r:=\dfrac{2\|k\|}{\delta}$. Work on the closed ball
$\overline{B}_r=\{h\in H:\|h\|\le r\}$, a complete metric space (closed subset of
the Banach space $H$).

**$T$ maps $\overline{B}_r$ into itself.** Using $(\dagger)$ and
$\|Q(h,h)\|\le M\|h\|^2$, for $\|h\|\le r$:
$$\|T(h)\|\le\tfrac1\delta\|k\|+\tfrac1\delta M\|h\|^2
\le\frac{\|k\|}{\delta}+\frac{M r^2}{\delta}
=\frac{\|k\|}{\delta}+\frac{M}{\delta}\cdot\frac{4\|k\|^2}{\delta^2}
=\frac{\|k\|}{\delta}\Big(1+\frac{4M\|k\|}{\delta^2}\Big).$$
Since $\|k\|<\epsilon=\dfrac{\delta^2}{4M}$, the bracket is $<2$, so
$\|T(h)\|<\dfrac{2\|k\|}{\delta}=r$. Thus $T(\overline{B}_r)\subseteq\overline{B}_r$.

**$T$ is a contraction on $\overline{B}_r$.** Bilinearity gives the telescoping
identity
$$Q(h_1,h_1)-Q(h_2,h_2)=Q(h_1,h_1-h_2)+Q(h_1-h_2,h_2),$$
hence $\|Q(h_1,h_1)-Q(h_2,h_2)\|\le M(\|h_1\|+\|h_2\|)\|h_1-h_2\|$. Therefore,
for $h_1,h_2\in\overline{B}_r$,
$$\|T(h_1)-T(h_2)\|\le\tfrac1\delta\|Q(h_1,h_1)-Q(h_2,h_2)\|
\le\frac{M(\|h_1\|+\|h_2\|)}{\delta}\|h_1-h_2\|\le\frac{2Mr}{\delta}\|h_1-h_2\|.$$
The factor is
$$q:=\frac{2Mr}{\delta}=\frac{2M}{\delta}\cdot\frac{2\|k\|}{\delta}=\frac{4M\|k\|}{\delta^2}<1,$$
again because $\|k\|<\epsilon$. So $T$ is a contraction with constant $q<1$.

**Conclusion.** By the Banach fixed-point theorem, $T$ has a (unique) fixed point
$h\in\overline{B}_r$, which solves $Lh+Q(h,h)=k$. The self-map estimate above is
strict, so
$$\|h\|=\|T(h)\|<\frac{2\|k\|}{\delta}=B\|k\|.$$
(For $k=0$, $h=0$ is the solution.) This proves (a) with $\epsilon=\delta^2/4M$
and $B=2/\delta$. $\blacksquare$

*Remark (the constants are not sacred).* Any pair with $\epsilon\le\delta^2/4M$
works; the only requirements are that the radius $r\sim\|k\|/\delta$ simultaneously
satisfy self-map ($\frac{Mr^2}{\delta}\lesssim r$) and contraction
($\frac{2Mr}{\delta}<1$), which is possible exactly when $\|k\|$ is below an
$O(\delta^2/M)$ threshold.

### Part (b) — Without surjectivity: **No.** A counterexample

Drop surjectivity but keep bounded-below. We claim no $\epsilon>0$ can work, by
explicit counterexample.

**Construction.** Let
$$H=\mathbb R,\qquad K=\mathbb R^2,\qquad L(h)=(h,0),\qquad Q(h_1,h_2)=(0,\,h_1h_2).$$
Check the hypotheses:
- $L$ is linear with $\|Lh\|=|h|=\|h\|$, so it is **bounded below** with
  $\delta=1$. Its range is the $x$-axis $\{(t,0)\}$, a proper subspace of
  $\mathbb R^2$, so $L$ is **not surjective**.
- $Q$ is bilinear with $\|Q(h_1,h_2)\|=|h_1h_2|=\|h_1\|\|h_2\|$, so it is bounded
  with $M=1$.

**The equation cannot be solved for small transverse $k$.** Here
$$Lh+Q(h,h)=(h,\,0)+(0,\,h^2)=(h,\,h^2),$$
so the set of attainable right-hand sides is exactly the parabola
$P=\{(t,t^2):t\in\mathbb R\}$. Now take
$$k=(0,\eta),\qquad \eta\ne 0.$$
A solution would need $h=0$ (first coordinate) and $h^2=\eta$ (second
coordinate), i.e. $0=\eta$ — impossible. Yet $\|k\|=|\eta|$ can be made as small
as we like. Hence for **every** $\epsilon>0$ there is a $k$ with $\|k\|<\epsilon$
(e.g. $k=(0,\epsilon/2)$) for which the equation has no solution. $\blacksquare$

**Why it fails — the geometric reason.** At the origin the parabola $P$ is
*tangent* to $\operatorname{ran}L$ (the $x$-axis): the quadratic term $h^2$ is
higher order, so near $0$ it cannot supply the missing vertical direction. Thus
the image of the nonlinear map is a thin surface hugging $\operatorname{ran}L$,
and a whole cone of small $k$ transverse to the range is unreachable. This is
precisely the **inverse function theorem** obstruction: local solvability onto a
*full neighborhood* requires the linearization $L$ at $0$ to be **onto**;
bounded-below only guarantees it is one-to-one. In part (a), surjectivity is
what makes $L^{-1}$ defined on *all* of $K$, and that global inverse is the one
thing the contraction argument cannot do without.

## What Connects

**To the inverse/implicit function theorem.** Part (a) is the quantitative
Banach-space inverse function theorem for the map $F(h)=Lh+Q(h,h)$ with
$F(0)=0$, $DF(0)=L$ invertible: $F$ is a local homeomorphism near $0$ with a
Lipschitz local inverse, and the bound $\|h\|<B\|k\|$ is the Lipschitz constant
of that inverse. Part (b) shows the hypothesis "$DF(0)$ surjective" is sharp.

**To Newton–Kantorovich.** The contraction $T(h)=L^{-1}(k-Q(h,h))$ is a
simplified Newton iteration (the derivative is frozen at $L=DF(0)$ rather than
updated). The smallness threshold $\epsilon=O(\delta^2/M)$ is the basin-of-
attraction radius, with $1/\delta=\|L^{-1}\|$ and $M$ the bound on the
nonlinearity — exactly the data the Newton–Kantorovich theorem tracks.

**To bifurcation and tangency.** The counterexample's tangency of the
solution-surface to $\operatorname{ran}L$ is the prototype of a *fold/turning
point*: when the linearization drops rank (or misses directions), small data off
the critical direction has no solution while data along it has two (here
$h=\pm\sqrt{\eta}$ would solve $(0,h^2)=(0,\eta)$ only after also matching the
first coordinate — the mismatch is what kills it). This tangency picture recurs
throughout nonlinear functional analysis whenever the leading linear operator
fails to be onto.
