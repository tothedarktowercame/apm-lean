<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM a98A04: An L¹ function that is essentially unbounded on every interval

## Why It's Hard

Part (a) is a one-line integral, but its real purpose is hidden: the normalization $1/\sqrt{b-a}$ is engineered so that the integral comes out to the **same constant for every interval $(a,b)$**, no matter how short or where it sits. That constancy is the lever for part (b).

Part (b) asks for something that violates naïve intuition about $L^1$. An integrable function "ought to be small most of the time" — yet we must produce one that, on *every* open interval, and *after any modification on a null set*, has supremum $+\infty$. The two demands pull against each other:

- **Local wildness everywhere:** the function must blow up inside every interval $(\alpha,\beta)$ — and there are uncountably many such intervals.
- **Global finiteness:** the total $L^1$ mass must stay finite.

The resolution is to superpose countably many integrable singular spikes — one anchored near every rational point — and the only way the masses can sum to something finite is if each spike costs a *controllable, bounded* amount. That is exactly the constant from part (a). The final twist is that "unbounded" must be upgraded to "**essentially** unbounded": robust against redefinition on a null set. That forces a positive-measure argument, not a mere pointwise one.

## The Key Insight

Part (a) computes
$$\int_{-\infty}^\infty f_{a,b} = 2 \quad\text{for every } a<b,$$
a value **independent of the interval**. This is the whole game. Because each spike $f_{a,b}$ carries the *same* finite mass $2$ regardless of how tiny $(a,b)$ is, we can place a spike inside every rational-endpoint interval and damp the $k$-th one by a summable weight $c_k = 2^{-k}$. The total mass is then
$$\sum_k c_k \cdot 2 = 2\sum_k 2^{-k} < \infty,$$
so the superposition $f = \sum_k 2^{-k} f_{a_k,b_k}$ is integrable (Beppo Levi / monotone convergence for series of nonnegative functions). Yet inside *any* open interval there sits a rational subinterval $(a_k,b_k)$, and on it $f \ge 2^{-k} f_{a_k,b_k}$, which blows up like $(x-a_k)^{-1/2}$ at the left endpoint. The blow-up happens on a set of **positive measure** at every height, which is precisely what makes the unboundedness survive any null-set surgery.

## Complete Proof

### Part (a): $f_{a,b}$ is integrable and $\int_{\mathbb{R}} f_{a,b} = 2$

Recall $f_{a,b}(x) = \dfrac{1}{\sqrt{(b-a)(x-a)}}$ for $a<x<b$ and $f_{a,b}(x)=0$ otherwise. It is nonnegative and measurable (continuous on $(a,b)$, zero elsewhere), so its Lebesgue integral is well-defined in $[0,\infty]$ and equals the improper Riemann integral when that converges.

Pull out the constant $\tfrac{1}{\sqrt{b-a}}$ and substitute $u = x-a$:
$$
\int_{\mathbb{R}} f_{a,b}
= \frac{1}{\sqrt{b-a}}\int_a^b (x-a)^{-1/2}\,dx
= \frac{1}{\sqrt{b-a}}\int_0^{b-a} u^{-1/2}\,du .
$$
The integrand $u^{-1/2}$ has exponent $-\tfrac12 > -1$, so it is integrable near $0$, and
$$
\int_0^{b-a} u^{-1/2}\,du = \Big[\,2u^{1/2}\,\Big]_0^{\,b-a} = 2\sqrt{b-a}.
$$
Therefore
$$
\boxed{\;\int_{-\infty}^{\infty} f_{a,b}(x)\,dx = \frac{1}{\sqrt{b-a}}\cdot 2\sqrt{b-a} = 2.\;}
$$
In particular the integral is finite, so $f_{a,b} \in L^1(\mathbb{R})$, and the value $2$ does **not** depend on $a$ or $b$.

### Part (b): an integrable function essentially unbounded on every interval

**Construction.** The open intervals with rational endpoints form a countable family; enumerate them as $\big((a_k,b_k)\big)_{k=1}^\infty$ with $a_k<b_k$ rational. Define
$$
f(x) := \sum_{k=1}^\infty 2^{-k}\, f_{a_k,b_k}(x), \qquad x \in \mathbb{R}.
$$
Each term is nonnegative and measurable, so the partial sums increase to $f$, and $f:\mathbb{R}\to[0,\infty]$ is measurable.

**$f$ is integrable.** Apply the **monotone convergence theorem for series** (Beppo Levi): for nonnegative measurable terms, integral and sum interchange. Using part (a),
$$
\int_{\mathbb{R}} f
= \int_{\mathbb{R}} \sum_{k=1}^\infty 2^{-k} f_{a_k,b_k}
= \sum_{k=1}^\infty 2^{-k} \int_{\mathbb{R}} f_{a_k,b_k}
= \sum_{k=1}^\infty 2^{-k}\cdot 2
= 2\sum_{k=1}^\infty 2^{-k} = 2 < \infty .
$$
Thus $f \in L^1(\mathbb{R})$. In particular $\int f < \infty$ forces $f(x) < \infty$ for a.e. $x$, so $f$ is a genuine (a.e. finite) integrable function.

**$f$ is essentially unbounded on every open interval.** Fix any open interval $(\alpha,\beta)$ with $\alpha<\beta$. We must show that whenever $g = f$ a.e., $\displaystyle\sup_{\alpha<x<\beta} g(x) = \infty$.

Choose rationals $a_k, b_k$ with $\alpha < a_k < b_k < \beta$; such a pair exists by density of $\mathbb{Q}$, and $(a_k,b_k)$ is one of the enumerated intervals. Since every term of the defining series is nonnegative,
$$
f(x) \ge 2^{-k}\, f_{a_k,b_k}(x) = \frac{2^{-k}}{\sqrt{(b_k-a_k)(x-a_k)}} \qquad \text{for } a_k < x < b_k. \tag{$\dagger$}
$$
Fix any height $N>0$. The right side of $(\dagger)$ exceeds $N$ exactly when
$$
x - a_k < \frac{2^{-2k}}{(b_k-a_k)\,N^2} =: \eta_N > 0 .
$$
Hence the level set
$$
E_N := \{x \in (\alpha,\beta) : f(x) > N\} \;\supseteq\; \big(a_k,\; a_k+\min(\eta_N,\,b_k-a_k)\big)
$$
contains a nonempty open interval, so $m(E_N) > 0$ for **every** $N$.

Now let $g = f$ a.e., say $g = f$ off a null set $Z$. Then
$$
\{x\in(\alpha,\beta) : g(x) > N\} \supseteq E_N \setminus Z,
$$
and $m(E_N \setminus Z) = m(E_N) > 0$, so this set is nonempty. Thus there exists $x \in (\alpha,\beta)$ with $g(x) > N$. As $N$ was arbitrary,
$$
\sup_{\alpha<x<\beta} g(x) = \infty .
$$
Since $(\alpha,\beta)$ and the representative $g$ were arbitrary, $f$ is integrable on $\mathbb{R}$ and essentially unbounded on every open interval. $\qquad\blacksquare$

### Remark — why the constant in (a) is the engine

The construction succeeds *because* the answer to (a) is a finite constant independent of the interval. Each spike injects an honest singularity ($x^{-1/2}$ blow-up) into its interval while costing only a fixed amount of $L^1$ mass; the geometric weights $2^{-k}$ then pay for *all* of them at once. Replacing $1/\sqrt{b-a}$ by, say, the un-normalized $1/\sqrt{x-a}$ would still give a finite per-interval mass ($2\sqrt{b-a}$), so $c_k=2^{-k}$ would still work — the normalization is a convenience, not a necessity. What is essential is (i) each spike is $L^1$ with a controllable mass, (ii) each blows up on a set of positive measure at every height (giving *essential*, null-set-robust unboundedness), and (iii) the rationals let countably many spikes reach into every interval at once.
