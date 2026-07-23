<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM a98A07: Boundary L¹-domination forces interior uniform convergence via the Cauchy kernel

## Why It's Hard

Every hypothesis lives on the **boundary circle** $|z|=1$, yet the conclusion is about the **interior**: uniform convergence on compact subsets of the open disk, and holomorphy of the limit. We need a device that transports boundary information inward — the **Cauchy integral formula** — and the hint says exactly this.

The real trap is the boundary bound. It does **not** give uniform boundedness: as $t\to 0^+$ the dominating function $\Phi(t) = \dfrac{1}{t(\log(t/4\pi))^2}$ blows up, so the $f_n$ may be unbounded near $z=1$. A naïve appeal to Montel's theorem with a sup-bound is therefore unavailable. The bound is instead an **$L^1$ domination**, and the entire problem hinges on recognizing that $\Phi$ is the classic *borderline-integrable* function: $\int \frac{dt}{t(\log t)^2}$ converges, while $\int\frac{dt}{t\log t}$ and $\int\frac{dt}{t}$ diverge.

There is even a deliberate trap in the constant $4\pi$. On $0<t<2\pi$ we have $t/4\pi\in(0,\tfrac12)$, so $\log(t/4\pi)$ stays $\le -\ln 2 <0$ and the only singularity of $\Phi$ is the (integrable) one at $t=0$. Had the problem written $\log(t/2\pi)$, the log would vanish at $t=2\pi$, producing a $\sim (t-2\pi)^{-2}$ blow-up there that is **not** integrable — and the whole argument would collapse. The $4\pi$ is doing real work.

## The Key Insight

The Cauchy integral formula writes each interior value as an **$L^1$-pairing of boundary values against the Cauchy kernel**:
$$f_n(z) = \frac{1}{2\pi}\int_0^{2\pi} \frac{f_n(e^{it})\,e^{it}}{e^{it}-z}\,dt, \qquad |z|<1.$$
On a compact disk $\{|z|\le r\}$ ($r<1$) the kernel is **uniformly bounded**:
$$\left|\frac{e^{it}}{e^{it}-z}\right| = \frac{1}{|e^{it}-z|} \le \frac{1}{1-r}.$$
So if the boundary values converge *in $L^1$*, the interior values converge *uniformly* on $\{|z|\le r\}$ — the bounded kernel converts $L^1$-convergence of inputs into sup-norm convergence of outputs. And $L^1$-convergence of the boundary values is precisely what the **Dominated Convergence Theorem** delivers, because the a.e. limit $g(t)=\lim_n f_n(e^{it})$ is dominated by the *integrable* function $\Phi$. Define the limit by the same Cauchy integral with $g$ in place of the boundary values; uniform-on-compacta limits of holomorphic functions are holomorphic.

## Complete Proof

Write $\overline D = \{|z|\le 1\}$ and let $D=\{|z|<1\}$. Each $f_n$ is holomorphic on an open set containing $\overline D$. Parametrize the boundary by $w=e^{it}$, $t\in[0,2\pi]$. Set $\Phi(t) := \dfrac{1}{t(\log(t/4\pi))^2}$ for $0<t<2\pi$, so the hypothesis is $|f_n(e^{it})|\le \Phi(t)$ for all $n$ and a.e. $t$.

### Step 1 — The dominating weight is integrable: $\Phi\in L^1(0,2\pi)$

For $0<t<2\pi$ we have $t/4\pi\in(0,\tfrac12)$, hence $\log(t/4\pi)\le -\ln 2<0$ and $\Phi$ is continuous and positive on $(0,2\pi)$. The only possible blow-up is as $t\to 0^+$. Substitute $u=\log(t/4\pi)$, $du=\dfrac{dt}{t}$; as $t$ runs over $(0,\delta]$, $u$ runs over $(-\infty,\log(\delta/4\pi)]$, so
$$
\int_0^{\delta}\frac{dt}{t(\log(t/4\pi))^2} = \int_{-\infty}^{\log(\delta/4\pi)}\frac{du}{u^2} = \left[-\frac1u\right]_{-\infty}^{\log(\delta/4\pi)} = \frac{1}{|\log(\delta/4\pi)|} < \infty .
$$
On $[\delta,2\pi)$, $\Phi$ is continuous (and bounded, since $\log(t/4\pi)$ never reaches $0$ there), so its integral is finite. Hence
$$
\int_0^{2\pi}\Phi(t)\,dt < \infty, \qquad \text{i.e. } \Phi\in L^1(0,2\pi). \tag{1}
$$

### Step 2 — Boundary values converge in $L^1$

By hypothesis $g(t):=\lim_{n\to\infty} f_n(e^{it})$ exists for a.e. $t\in(0,2\pi)$; as an a.e. limit of measurable functions $g$ is measurable, and passing to the limit in $|f_n(e^{it})|\le \Phi(t)$ gives
$$|g(t)|\le \Phi(t)\quad\text{a.e.}, \qquad\text{so } g\in L^1(0,2\pi) \text{ by (1).}$$
Now consider $h_n(t):=|f_n(e^{it})-g(t)|$. Then $h_n\to 0$ a.e., and
$$h_n(t)\le |f_n(e^{it})|+|g(t)|\le 2\Phi(t)\in L^1(0,2\pi).$$
By the **Dominated Convergence Theorem**,
$$
\int_0^{2\pi}\big|f_n(e^{it})-g(t)\big|\,dt \longrightarrow 0 \qquad (n\to\infty). \tag{2}
$$

### Step 3 — Cauchy representation and the candidate limit

Since $f_n$ is holomorphic on a neighborhood of $\overline D$, the Cauchy integral formula gives, for every $z\in D$,
$$
f_n(z)=\frac{1}{2\pi i}\oint_{|w|=1}\frac{f_n(w)}{w-z}\,dw
=\frac{1}{2\pi}\int_0^{2\pi}\frac{f_n(e^{it})\,e^{it}}{e^{it}-z}\,dt, \tag{3}
$$
using $w=e^{it}$, $dw=ie^{it}\,dt$. Define the candidate limit by the same formula with $g$ in place of the boundary values:
$$
f(z):=\frac{1}{2\pi}\int_0^{2\pi}\frac{g(t)\,e^{it}}{e^{it}-z}\,dt, \qquad z\in D. \tag{4}
$$
This is well-defined: for $z\in D$ the kernel $t\mapsto \dfrac{e^{it}}{e^{it}-z}$ is bounded and continuous, and $g\in L^1$, so the integrand is integrable.

### Step 4 — Uniform convergence on compact subsets

Fix $r\in(0,1)$ and let $|z|\le r$. For every $t$,
$$
\left|\frac{e^{it}}{e^{it}-z}\right| = \frac{1}{|e^{it}-z|}\le \frac{1}{|e^{it}|-|z|}=\frac{1}{1-|z|}\le \frac{1}{1-r}. \tag{5}
$$
Subtracting (4) from (3) and using (5),
$$
|f_n(z)-f(z)|
=\left|\frac{1}{2\pi}\int_0^{2\pi}\frac{\big(f_n(e^{it})-g(t)\big)e^{it}}{e^{it}-z}\,dt\right|
\le \frac{1}{2\pi(1-r)}\int_0^{2\pi}\big|f_n(e^{it})-g(t)\big|\,dt .
$$
The right-hand side is **independent of $z$** on $\{|z|\le r\}$ and tends to $0$ by (2). Hence
$$
\sup_{|z|\le r}|f_n(z)-f(z)| \le \frac{1}{2\pi(1-r)}\int_0^{2\pi}\big|f_n(e^{it})-g(t)\big|\,dt \longrightarrow 0,
$$
i.e. $f_n\to f$ **uniformly on $\{|z|\le r\}$**. Since every compact subset of $D$ is contained in some such disk, $f_n\to f$ uniformly on compact subsets of $D$.

### Step 5 — The limit is holomorphic

Each $f_n$ is holomorphic on $D$, and $f_n\to f$ uniformly on every compact subset of $D$. By the **Weierstrass convergence theorem** (a locally uniform limit of holomorphic functions is holomorphic — e.g. via Morera's theorem: $\oint_\gamma f = \lim_n \oint_\gamma f_n = 0$ over every triangle $\gamma\subset D$), the limit $f$ is holomorphic on $D$.

Therefore $(f_n)$ converges uniformly on compact subsets of the open unit disk to a holomorphic function $f$, given explicitly by the Cauchy-type integral (4). $\qquad\blacksquare$

### Remark — the structure and the two ways $\Phi$ matters

The proof is a clean "boundary $\to$ interior" pipeline: **DCT** (Step 2) turns a.e. boundary convergence into $L^1$ boundary convergence; the **bounded Cauchy kernel** (Step 4) turns $L^1$ boundary convergence into uniform interior convergence; **Weierstrass** (Step 5) turns uniform interior convergence into holomorphy. The weight $\Phi$ enters at exactly two points and must be integrable for both: it dominates $g$ (so $g\in L^1$ and the integral (4) makes sense) and it dominates the differences $h_n$ (so DCT applies). The choice of $4\pi$ rather than $2\pi$ is what guarantees that integrability, by keeping $\log(t/4\pi)$ away from $0$ throughout $(0,2\pi)$ so the singularity at $t=0$ is the only one — and it is the borderline-convergent kind.
