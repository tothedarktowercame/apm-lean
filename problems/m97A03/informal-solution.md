<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m97A03: A nonlinear integral equation solved by the contraction mapping principle — where the threshold $|\lambda|<1/4$ comes from

## Why It's Hard

The equation
$$
u(t)-\lambda\int_0^1\sqrt{\tfrac{t+3}{s}}\,\sin\big(t\,u(s)\big)\,ds=e^t,\qquad 0\le t\le 1,
$$
is a **nonlinear** (Hammerstein-type) integral equation, and the request is an existence theorem with a *specific* smallness threshold. Three things must be handled carefully:

- **The kernel is singular.** The factor $\sqrt{(t+3)/s}=\sqrt{t+3}\,s^{-1/2}$ blows up like $s^{-1/2}$ as $s\to0^+$, so the integral is **improper**. One must check it converges (it does: $\int_0^1 s^{-1/2}ds=2<\infty$) and that the resulting operator actually maps continuous functions to continuous functions.
- **The nonlinearity** $\sin(t\,u(s))$ has to be tamed without linearizing. The lever is that **$\sin$ is $1$-Lipschitz**, which converts $|\sin(tu)-\sin(tv)|$ into $t|u-v|$ — and that stray factor of $t$ turns out to matter for the constant.
- **The threshold $1/4$ is not a guess.** It is *exactly* the reciprocal of the operator's Lipschitz constant, and getting it requires evaluating two suprema/integrals and multiplying: $\sup_t t\sqrt{t+3}=2$ and $\int_0^1 s^{-1/2}ds=2$, giving Lipschitz constant $4|\lambda|$. The condition $4|\lambda|<1$ *is* $|\lambda|<1/4$.

Once these are in place, the **Banach contraction mapping theorem** on $C([0,1])$ closes it — and as a bonus delivers uniqueness.

## The Key Insight

Recast the equation as a fixed point $u=Tu$ on the complete metric space $X=C([0,1])$ with the sup norm, where
$$
(Tu)(t)=e^t+\lambda\int_0^1\sqrt{\tfrac{t+3}{s}}\,\sin\big(t\,u(s)\big)\,ds .
$$
A continuous solution is exactly a fixed point of $T$. The map $T$ is a **contraction with constant $4|\lambda|$**, because the difference $Tu-Tv$ inherits three bounded factors that multiply to $4$:
$$
\underbrace{|\sin(tu)-\sin(ty)|\le t|u-v|}_{\sin\text{ is }1\text{-Lipschitz}},\qquad
\underbrace{\int_0^1 s^{-1/2}\,ds=2}_{\text{singularity integrable}},\qquad
\underbrace{\sup_{0\le t\le1}t\sqrt{t+3}=2}_{\text{max at }t=1:\,1\cdot\sqrt4} .
$$
Hence $\|Tu-Tv\|_\infty\le 4|\lambda|\,\|u-v\|_\infty$, and $4|\lambda|<1\iff|\lambda|<1/4$. Banach's theorem then gives a unique fixed point — the desired continuous solution.

## Complete Proof

Let $X=C([0,1])$ with norm $\|w\|_\infty=\max_{0\le t\le1}|w(t)|$; $(X,\|\cdot\|_\infty)$ is a complete metric space. Define $T:X\to X$ by
$$
(Tu)(t)=e^t+\lambda\sqrt{t+3}\int_0^1 s^{-1/2}\,\sin\big(t\,u(s)\big)\,ds .
$$
A function $u\in X$ solves the integral equation iff $Tu=u$.

### Step 1: $T$ maps $C([0,1])$ into itself

Fix $u\in X$. For each $t$, the integrand $s\mapsto s^{-1/2}\sin(tu(s))$ satisfies $|s^{-1/2}\sin(tu(s))|\le s^{-1/2}$, and $\int_0^1 s^{-1/2}\,ds=\big[2s^{1/2}\big]_0^1=2<\infty$, so the (improper) integral converges absolutely; call it $\Phi(t)$. Continuity of $\Phi$: if $t_n\to t$, then $s^{-1/2}\sin(t_nu(s))\to s^{-1/2}\sin(tu(s))$ pointwise, dominated by the integrable $s^{-1/2}$, so by the dominated convergence theorem $\Phi(t_n)\to\Phi(t)$. Therefore $t\mapsto e^t+\lambda\sqrt{t+3}\,\Phi(t)$ is continuous, i.e. $Tu\in C([0,1])$.

### Step 2: $T$ is a contraction with constant $4|\lambda|$

Let $u,v\in X$. For each $t\in[0,1]$,
$$
(Tu)(t)-(Tv)(t)=\lambda\sqrt{t+3}\int_0^1 s^{-1/2}\big[\sin(tu(s))-\sin(tv(s))\big]\,ds .
$$
Since $\sin$ is $1$-Lipschitz, $\big|\sin(tu(s))-\sin(tv(s))\big|\le |tu(s)-tv(s)|=t\,|u(s)-v(s)|\le t\,\|u-v\|_\infty$. Hence
$$
\big|(Tu)(t)-(Tv)(t)\big|\le |\lambda|\,\sqrt{t+3}\,\cdot t\,\|u-v\|_\infty\int_0^1 s^{-1/2}\,ds
= 2|\lambda|\,\big(t\sqrt{t+3}\big)\,\|u-v\|_\infty .
$$
On $[0,1]$ the function $t\mapsto t\sqrt{t+3}$ is increasing (product of nonnegative increasing factors), so its maximum is at $t=1$:
$$
\max_{0\le t\le1}t\sqrt{t+3}=1\cdot\sqrt{4}=2 .
$$
Therefore, taking the supremum over $t$,
$$
\|Tu-Tv\|_\infty\le 2|\lambda|\cdot 2\cdot\|u-v\|_\infty=4|\lambda|\,\|u-v\|_\infty .
$$

### Step 3: apply the contraction mapping theorem

Assume $|\lambda|<\tfrac14$. Then the contraction constant $k:=4|\lambda|<1$, and $T:X\to X$ is a contraction on the complete metric space $X=C([0,1])$. By the **Banach contraction mapping theorem**, $T$ has a unique fixed point $u\in C([0,1])$. This $u$ is a continuous solution of
$$
u(t)-\lambda\int_0^1\sqrt{\tfrac{t+3}{s}}\,\sin\big(t\,u(s)\big)\,ds=e^t,\qquad 0\le t\le1,
$$
and it is the *unique* continuous solution. $\qquad\blacksquare$

### Remark — the anatomy of the constant, and what the threshold protects

The number $1/4$ is exactly the radius of contraction: the operator's Lipschitz constant factors as
$$
\big(\text{Lipschitz const. of }\sin\big)\times\Big(\sup_t t\sqrt{t+3}\Big)\times\Big(\int_0^1 s^{-1/2}ds\Big)=1\times2\times2=4,
$$
so $T$ contracts precisely when $4|\lambda|<1$. Two robustness points are worth noting. First, **boundedness of $\sin$ is not what is used** — only its Lipschitz constant; the same proof works for any nonlinearity $g(t,u)$ with $\sup|\partial_ug|\le 1$. Second, the **$s^{-1/2}$ singularity is harmless** precisely because $-1/2>-1$ makes it integrable; a kernel singularity $s^{-\alpha}$ with $\alpha<1$ would simply replace the factor $2=\int_0^1 s^{-1/2}$ by $\frac{1}{1-\alpha}$ and shift the threshold accordingly. The contraction method gives existence *and* uniqueness *and* a convergent iteration $u_{n+1}=Tu_n$ (Picard iteration) with geometric error $\|u_n-u\|_\infty\le \frac{k^n}{1-k}\|u_1-u_0\|_\infty$, all from the single inequality of Step 2.
