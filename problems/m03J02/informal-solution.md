<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m03J02: The scalar ODE $u'+u=\cos u$ — Picard–Banach existence/uniqueness and global convergence to the unique equilibrium

## Why It's Hard

The equation $u'(t)+u(t)=\cos(u(t))$, $u(0)=u_0$, is a scalar autonomous ODE $u'=g(u)$ with $g(u)=-u+\cos u$. Both parts are standard *in technique* but each has a trap:

- **(a)** asks specifically for the **contraction mapping theorem**, so one cannot just cite Picard–Lindelöf as a black box — one must exhibit the integral operator, identify the right complete metric space, and prove the contraction estimate. The subtlety is that the naive sup-norm contraction only works on a *short* time interval ($LT<1$); promoting "local unique solution" to "a unique solution on all of $[0,\infty)$ for each $u_0$" requires noticing that $g$ is **globally** Lipschitz, so the local existence time is uniform and the solution patches together without blow-up.
- **(b)** asks to show that *all* trajectories, regardless of $u_0$, converge to *one and the same* limit $\xi$. The tempting route — a Lyapunov/energy estimate $\frac{d}{dt}\tfrac12(u-\xi)^2\le -c(u-\xi)^2$ — **stalls**, because $g'(u)=-1-\sin u$ vanishes at $u=-\tfrac\pi2+2k\pi$, so $g$ is *not uniformly* strictly decreasing and there is no global exponential rate $c>0$. The clean argument instead uses the **scalar autonomous structure**: monotonicity of the trajectory (it cannot cross the equilibrium, by uniqueness) plus boundedness, with the limit pinned down as the unique zero of $g$.

## The Key Insight

Write the equation as $u'=g(u)$, $\ g(u)=-u+\cos u$. Two facts about $g$ run everything:

1. **$g$ is globally Lipschitz**, with constant $L=2$: $g'(u)=-1-\sin u\in[-2,0]$, so $|g(a)-g(b)|\le 2|a-b|$. A *uniform* Lipschitz constant makes the Picard iteration a contraction on a time-step that does not depend on the data, giving uniqueness **and** global existence by repetition.

2. **$g$ is strictly decreasing with a unique zero $\xi$** (the "Dottie number", $\cos\xi=\xi$, $\xi\approx0.739$): since $g'\le0$ and $g(0)=1>0>g(2)$, there is exactly one $\xi$ with $g(\xi)=0$. The constant $u\equiv\xi$ is therefore an equilibrium solution.

For a scalar autonomous equation with a strictly decreasing $g$, the unique zero is a **globally attracting** equilibrium: a trajectory starting above $\xi$ has $u'=g(u)<0$ and decreases, one starting below has $u'>0$ and increases; by uniqueness neither can cross $\xi$, so each is monotone and bounded, hence convergent, and the only possible limit is the zero $\xi$. The same $\xi$ works for every $u_0$ — which is exactly the claim.

## Complete Proof

Set $g(u)=-u+\cos u$, so the IVP is $u'=g(u)$, $u(0)=u_0$. We first record:

**$g$ is globally Lipschitz.** $g$ is $C^1$ with $g'(u)=-1-\sin u$, and $-2\le g'(u)\le0$ for all $u$. By the mean value theorem, for all $a,b$,
$$
|g(a)-g(b)|\le \Big(\sup_{u}|g'(u)|\Big)\,|a-b|=2\,|a-b|,\qquad L:=2 .
$$

### Part (a): existence and uniqueness via the contraction mapping theorem

A continuous $u$ solves the IVP on an interval $I\ni0$ iff it solves the integral equation
$$
u(t)=u_0+\int_0^t g(u(s))\,ds ,\tag{$\ast$}
$$
the equivalence being the fundamental theorem of calculus (if $u$ is continuous then $s\mapsto g(u(s))$ is continuous, so the right side is $C^1$ with derivative $g(u(t))$, and $u(0)=u_0$; conversely a $C^1$ solution integrates to $(\ast)$).

**A contraction on a short interval.** Fix $T$ with $0<T<\tfrac1L=\tfrac12$, and work in the complete metric space $X=C([0,T])$ with the sup norm $\|\cdot\|_\infty$. Define $\Phi:X\to X$ by
$$
(\Phi u)(t)=u_0+\int_0^t g(u(s))\,ds .
$$
$\Phi u$ is continuous, so $\Phi$ maps $X$ into $X$. For $u,v\in X$ and $t\in[0,T]$,
$$
|(\Phi u)(t)-(\Phi v)(t)|=\Big|\int_0^t\!\big(g(u(s))-g(v(s))\big)ds\Big|
\le\int_0^t L\,|u(s)-v(s)|\,ds\le L\,T\,\|u-v\|_\infty .
$$
Taking the supremum over $t\in[0,T]$ gives
$$
\|\Phi u-\Phi v\|_\infty\le LT\,\|u-v\|_\infty,\qquad LT<1 .
$$
Thus $\Phi$ is a contraction. By the **Banach contraction mapping theorem**, $\Phi$ has a unique fixed point $u\in C([0,T])$, which is the unique solution of $(\ast)$ — hence the unique solution of the IVP — on $[0,T]$.

**Extension to $[0,\infty)$.** The crucial point is that $T$ may be chosen **independently of the data**: fix the step $h=\tfrac14<\tfrac1L$ once and for all. The argument just given, applied on $[t_0,t_0+h]$ with initial value $u(t_0)$ (replacing $u_0$ by $u(t_0)$ and $0$ by $t_0$), produces a unique solution on $[t_0,t_0+h]$ for *any* real initial value, because $L=2$ is a *global* Lipschitz constant and $h<1/L$ regardless of $u(t_0)$. Starting from $t_0=0$ and iterating over $[0,h],[h,2h],[2h,3h],\dots$, we obtain a solution on all of $[0,\infty)$; the pieces agree at the junction points (each new piece starts from the previous endpoint), so they glue to a single $C^1$ solution. (No finite-time blow-up can occur precisely because each step has the same length $h$.)

**Global uniqueness.** If $u,\tilde u$ both solve the IVP on $[0,\infty)$, then on $[0,h]$ they are both fixed points of $\Phi$, hence equal; then they share the value at $h$, so by the same contraction on $[h,2h]$ they agree there, and inductively on every $[kh,(k+1)h]$. Thus $u=\tilde u$ on $[0,\infty)$.

Hence for each $u_0\in\mathbb{R}$ there is **exactly one** solution $u:[0,\infty)\to\mathbb{R}$. $\qquad\checkmark$

*(Remark: one can reach $[0,\infty)$ in a single stroke instead of patching, by running $\Phi$ on $C([0,\infty))$ under the Bielecki norm $\|u\|_\beta=\sup_{t\ge0}e^{-\beta t}|u(t)|$ with $\beta>L$; there $\|\Phi u-\Phi v\|_\beta\le\frac{L}{\beta}\|u-v\|_\beta$ is a contraction. The patching argument above is the elementary version.)*

### Part (b): every solution converges to the unique equilibrium $\xi$

**The equilibrium exists and is unique.** A constant $u\equiv\xi$ solves the ODE iff $g(\xi)=0$, i.e. $\cos\xi=\xi$. Now $g(u)=-u+\cos u$ is continuous with $g(0)=1>0$ and $g(2)=-2+\cos2<0$, so by the intermediate value theorem $g$ has a zero $\xi\in(0,2)$. It is **unique**: for $a<b$,
$$
g(b)-g(a)=\int_a^b g'(s)\,ds=\int_a^b(-1-\sin s)\,ds<0,
$$
since the integrand is $\le0$ and equals $0$ only at the isolated points $s=-\tfrac\pi2+2k\pi$. So $g$ is strictly decreasing, hence injective, and has exactly one zero $\xi$. Fix this $\xi$ — it depends only on $g$, **not** on $u_0$.

Let $u$ be the solution for a given $u_0$ (from part (a), defined on all of $[0,\infty)$). We show $u(t)\to\xi$.

**Case $u_0=\xi$.** Then $u\equiv\xi$ solves the IVP, and by uniqueness it *is* the solution; trivially $u(t)\to\xi$.

**Case $u_0>\xi$.** First, $u(t)>\xi$ for all $t\ge0$. Indeed the constant $\xi$ is a solution; if $u(t_1)=\xi$ for some $t_1$, then $u$ and the constant solution $\xi$ agree at $t_1$, so by uniqueness (applied with initial time $t_1$) $u\equiv\xi$, contradicting $u_0>\xi$. Continuity then forces $u(t)>\xi$ throughout. While $u>\xi$, strict monotonicity of $g$ gives $u'=g(u)<g(\xi)=0$, so $u$ is **strictly decreasing**. Being decreasing and bounded below by $\xi$, $u(t)\downarrow\ell$ for some finite $\ell\ge\xi$.

The limit is an equilibrium: since $u(t)\to\ell$ and $g$ is continuous, $u'(t)=g(u(t))\to g(\ell)$. If $g(\ell)\ne0$, then (as $g(\ell)<0$ here) there is $t_0$ with $u'(t)\le \tfrac12 g(\ell)<0$ for $t\ge t_0$, forcing $u(t)\to-\infty$ and contradicting $u(t)\ge\xi$. Hence $g(\ell)=0$, so $\ell=\xi$ by uniqueness of the zero. Therefore $u(t)\to\xi$.

**Case $u_0<\xi$.** Symmetric: $u(t)<\xi$ for all $t$ (same uniqueness barrier), so $u'=g(u)>g(\xi)=0$ and $u$ is strictly increasing and bounded above by $\xi$, hence $u(t)\uparrow\ell\le\xi$; the same limit-is-a-zero argument gives $g(\ell)=0$, so $\ell=\xi$.

In every case $\displaystyle\lim_{t\to\infty}u(t)=\xi$, with the **same** $\xi$ for all $u_0\in\mathbb{R}$. This is exactly the assertion $\exists\,\xi\in\mathbb{R}\ \forall u_0\in\mathbb{R}:\ \lim_{t\to\infty}u(t)=\xi$. $\qquad\blacksquare$

### Remark — structure and rate

The two parts are the two halves of "global asymptotic stability of a scalar equilibrium." Part (a) uses that $g$ is **globally Lipschitz** (uniform step $\Rightarrow$ global existence and uniqueness); part (b) uses that $g$ is **strictly decreasing with a single zero** ($\Rightarrow$ monotone trapped trajectories converging to that zero). The phrase "boundary value problem" in the statement is a slight misnomer — it is the same initial value problem of part (a); the "boundary" condition is the asymptotic one $u(\infty)=\xi$, which the proof *produces* rather than imposes.

Although there is no *global* exponential rate (because $g'(u)=-1-\sin u$ touches $0$), convergence **is** eventually exponential: near the equilibrium the linearization is $w'\approx g'(\xi)\,w$ with $g'(\xi)=-1-\sin\xi\approx-1.673<0$, so for large $t$ one has $|u(t)-\xi|\lesssim Ce^{-(1+\sin\xi)t}$. The monotone-convergence argument above is what guarantees the trajectory actually reaches this neighborhood from every starting point.
