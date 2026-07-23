<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m93J05: Fourier truncation as a self-adjoint projection, and a variational problem split by frequency

## Why It's Hard

The map `\Phi` (better written `\Phi_N`) looks analytic — "truncate the Fourier series" —
but every part of the problem is really about recognizing it as one clean algebraic object:
a **self-adjoint, finite-rank, idempotent projection** onto the `(2N+1)`-dimensional space
`T_N` of trigonometric polynomials of degree `\le N`. Once that is seen, the adjoint and the
kernel/cokernel fall out immediately, and the entire space splits as `L^p = T_N \oplus \ker\Phi`
— low frequencies and high frequencies.

The genuinely hard parts are variational, and they are subtle for two reasons. First,
"lower semicontinuous" has to be interpreted in the **weak** topology, since that is the
only topology in which the direct method can extract a limit from a bounded minimizing
sequence — and weak lower semicontinuity is *not* automatic; it needs convexity. Second,
coercivity is not obvious: the functional `J_g` mixes an `L^p` term, an `L^2` term, and a
linear term, and you must see that the `L^p` power controls the *high-frequency* part while
the `L^2` square controls the *low-frequency* part — the two energies are tuned to the two
summands of the splitting, and only together do they dominate `\|f\|_{L^p}`.

## The Key Insight

`\Phi` is the integral operator with the **Dirichlet kernel**

$$\Phi[f](\theta) = \int_{S^1} D_N(\theta-\varphi)\,f(\varphi)\,d\varphi,
\qquad D_N(x) = 1 + 2\sum_{j=1}^{N}\cos(2\pi j x),$$

and `D_N` is real and even, so `D_N(\theta-\varphi)=D_N(\varphi-\theta)`. That single symmetry
makes `\Phi` **self-adjoint** for the pairing `\langle f,g\rangle = \int_{S^1} fg`, and `\Phi^2=\Phi`
because truncating twice is truncating once. Everything else is a consequence:

- **(a)** `\Phi^* = \Phi` (the same truncation, now read on `L^q`).
- **(b)** `\operatorname{ran}\Phi = T_N` (degree `\le N`), `\ker\Phi = ` high-frequency
  functions; `\operatorname{coker}\Phi \cong \ker\Phi`.
- **(c)–(e)** Write `f = u + w` with `u = \Phi f \in T_N` and `w = (I-\Phi)f \in \ker\Phi`.
  Then `J_g(f) = \|w\|_{L^p}^p + \|u\|_{L^2}^2 + \int fg`. The first term is a coercive power
  of the high part, the second a coercive square of the low part (on the finite-dimensional
  `T_N` all norms are equivalent). Convex + continuous gives weak lsc; coercive + reflexive
  gives a minimizer; and projecting the Euler–Lagrange equation onto `T_N` and `\ker\Phi`
  decouples it into an **explicit** formula for `u` and a nonlinear **`p`-duality** equation
  for `w`.

## Complete Proof

Let `S^1 = \mathbb{R}/\mathbb{Z}`, `T_N = \operatorname{span}\{1,\cos(2\pi j\theta),\sin(2\pi j\theta): 1\le j\le N\}`
(dimension `2N+1`), and pair `L^p` with `L^q` (`\tfrac1p+\tfrac1q=1`) by
`\langle f,g\rangle = \int_{S^1} fg`. For `1<p<\infty`, `\Phi` is bounded on `L^p` (it is the
partial-sum operator `S_N`; for fixed `N` it has finite rank `2N+1`), and `\Phi^2=\Phi`, so
`\Phi` is a bounded projection with `\operatorname{ran}\Phi = T_N`.

---

### (a) The adjoint `\Phi^*`

Under `(L^p)^* \cong L^q`, the adjoint is defined by `\langle \Phi f, g\rangle = \langle f, \Phi^* g\rangle`.
Using the Dirichlet-kernel representation and Fubini,

$$\langle \Phi f, g\rangle = \iint D_N(\theta-\varphi) f(\varphi)\,g(\theta)\,d\varphi\,d\theta
= \int f(\varphi)\Big(\int D_N(\varphi-\theta)\,g(\theta)\,d\theta\Big)d\varphi
= \langle f, \Phi g\rangle,$$

where we used `D_N(\theta-\varphi)=D_N(\varphi-\theta)`. Hence

$$\boxed{\ \Phi^* = \Phi\ }$$

— identifying `(L^p)^*` with `L^q`, the adjoint is the *same* order-`N` Fourier truncation,
now acting on `L^q`:
`\Phi^*[g] = a_0(g) + \sum_{j=1}^N a_j(g)\cos(2\pi j\theta) + b_j(g)\sin(2\pi j\theta)`. It is
again an idempotent rank-`(2N+1)` projection onto `T_N \subset L^q`. So `\Phi` is "self-adjoint"
in the bilinear sense `\int(\Phi f)g = \int f(\Phi g)`.

---

### (b) Kernel and cokernel

Since `\Phi` keeps exactly the Fourier coefficients of order `\le N`:

$$\boxed{\ \ker\Phi = \{f\in L^p : \hat f(j)=0\ \text{for}\ |j|\le N\}\ }$$

— the closed, **infinite-dimensional** subspace of functions with no spectral content in
degrees `0,1,\dots,N` (the `L^p`-closure of `\operatorname{span}\{e^{2\pi i j\theta}: |j|>N\}`).

The image is `\operatorname{ran}\Phi = T_N`, the trig polynomials of degree `\le N`, a
**closed** `(2N+1)`-dimensional space. Because `\Phi` is a projection, `L^p = T_N \oplus \ker\Phi`,
and

$$\boxed{\ \operatorname{coker}\Phi = L^p/\operatorname{ran}\Phi = L^p/T_N \ \cong\ \ker\Phi\ }$$

via the complementary projection `I-\Phi`; it is infinite-dimensional. (Both `\ker` and
`\operatorname{coker}` are infinite-dimensional, so `\Phi` is *not* Fredholm.) In the language
of the problem's marginal note: the kernel is everything whose first `2N+1` Fourier modes
vanish; the cokernel is `L^p` modulo the degree-`\le N` polynomials.

---

### (c) `J_g` is (weakly) lower semicontinuous

Write `J_g(f) = \|(I-\Phi)f\|_{L^p}^p + \|\Phi f\|_{L^2}^2 + \int_{S^1} fg`. We show `J_g` is
**convex and strongly continuous**, hence **weakly lower semicontinuous** — the form needed
in (d).

*Convexity.* `f\mapsto (I-\Phi)f` and `f\mapsto \Phi f` are linear; `\|\cdot\|_{L^p}` and
`\|\cdot\|_{L^2}` are norms (convex); `t\mapsto t^p` and `t\mapsto t^2` are convex and
nondecreasing on `[0,\infty)`. So `\|(I-\Phi)f\|_{L^p}^p` and `\|\Phi f\|_{L^2}^2` are convex
(convex-nondecreasing composed with convex), and `f\mapsto\int fg` is affine. A sum of convex
functions is convex.

*Continuity.* `I-\Phi` is bounded on `L^p` and `t\mapsto t^p` is continuous, so the first term
is continuous. The map `\Phi : L^p \to L^2` is bounded — its range `T_N` is finite-dimensional,
where `\|\cdot\|_{L^2}\le C\|\cdot\|_{L^p}`, so `\|\Phi f\|_{L^2}\le C\|\Phi f\|_{L^p}\le C'\|f\|_{L^p}`
— hence the second term is continuous. The third satisfies `|\int fg|\le\|f\|_{L^p}\|g\|_{L^q}`
(Hölder), so it is continuous (indeed weakly continuous).

*Weak lsc.* For each `c\in\mathbb{R}`, the sublevel set `\{f: J_g(f)\le c\}` is convex (by
convexity) and strongly closed (by continuity), hence **weakly closed** (a convex strongly
closed set is weakly closed, by Hahn–Banach/Mazur). Therefore `J_g` is weakly lower
semicontinuous: if `f_k \rightharpoonup f` then `J_g(f)\le\liminf_k J_g(f_k)`. ∎

---

### (d) `J_g` attains its minimum

We run the direct method, using that `L^p` is **reflexive** for `1<p<\infty`.

*Coercivity.* Decompose `f = u + w`, `u=\Phi f\in T_N`, `w=(I-\Phi)f\in\ker\Phi`; note
`(I-\Phi)f = w` and `\Phi f = u`, so

$$J_g(f) = \|w\|_{L^p}^p + \|u\|_{L^2}^2 + \int fg.$$

On the finite-dimensional `T_N`, norms are equivalent: `\|u\|_{L^2}\ge c\,\|u\|_{L^p}` for some
`c>0`. By Hölder, `\big|\int fg\big| \le \|g\|_{L^q}(\|u\|_{L^p}+\|w\|_{L^p})`. Hence

$$J_g(f) \ \ge\ \Big(\|w\|_{L^p}^p - \|g\|_{L^q}\|w\|_{L^p}\Big) + \Big(c^2\|u\|_{L^p}^2 - \|g\|_{L^q}\|u\|_{L^p}\Big).$$

Each function `t\mapsto t^p - \|g\|_{L^q}\,t` (`p>1`) and `t\mapsto c^2 t^2 - \|g\|_{L^q}\,t` is
bounded below on `[0,\infty)` and tends to `+\infty` as `t\to\infty`. So `J_g` is bounded below,
and since `\|f\|_{L^p}\le\|u\|_{L^p}+\|w\|_{L^p}\le 2\max(\|u\|_{L^p},\|w\|_{L^p})`, letting
`\|f\|_{L^p}\to\infty` forces one of `\|u\|_{L^p},\|w\|_{L^p}\to\infty`, driving the
corresponding bracket — and thus `J_g(f)` — to `+\infty`. So `J_g` is **coercive**.

*Existence.* Let `m=\inf_{L^p} J_g > -\infty`. Choose a minimizing sequence `f_k`,
`J_g(f_k)\to m`. Coercivity bounds `\{f_k\}` in `L^p`; by reflexivity (Banach–Alaoglu +
Eberlein–Šmulian) a subsequence `f_{k_j}\rightharpoonup f^\star`. By weak lsc (part c),

$$J_g(f^\star) \le \liminf_j J_g(f_{k_j}) = m.$$

Since `m` is the infimum, `J_g(f^\star)=m`. Thus the minimum is attained at `f^\star`. ∎

(The minimizer is in fact **unique**: `\|u\|_{L^2}^2` is strictly convex on `T_N` and
`\|w\|_{L^p}^p` is strictly convex on `\ker\Phi` for `1<p<\infty`, so `J_g` is strictly convex.)

---

### (e) Equations for the minimum

At the minimizer `f` the Gâteaux derivative vanishes: `\frac{d}{dt}J_g(f+th)\big|_{t=0}=0` for
all `h\in L^p`. Differentiating term by term (writing `w=(I-\Phi)f`, and using
`\frac{d}{dt}\int|w+tk|^p|_0 = p\int|w|^{p-2}w\,k`):

- `\dfrac{d}{dt}\|(I-\Phi)(f+th)\|_{L^p}^p\Big|_0 = p\int |(I-\Phi)f|^{p-2}(I-\Phi)f\,\cdot\,(I-\Phi)h
   = p\int (I-\Phi)\!\big(|(I-\Phi)f|^{p-2}(I-\Phi)f\big)\,h`  (using `(I-\Phi)^*=I-\Phi`);
- `\dfrac{d}{dt}\|\Phi(f+th)\|_{L^2}^2\Big|_0 = 2\langle\Phi f,\Phi h\rangle = 2\int (\Phi f)\,h`
   (using `\Phi^*\Phi=\Phi^2=\Phi`);
- `\dfrac{d}{dt}\int(f+th)g\Big|_0 = \int g\,h`.

Setting the sum to zero for all `h` gives the **Euler–Lagrange equation** in `L^q`:

$$\boxed{\ p\,(I-\Phi)\!\Big(|(I-\Phi)f|^{p-2}(I-\Phi)f\Big) \;+\; 2\,\Phi f \;+\; g \;=\; 0.\ }$$

**Decoupling by frequency.** Apply `\Phi` and `I-\Phi`, using `\Phi(I-\Phi)=0` and
`(I-\Phi)^2=I-\Phi`:

- *Low frequencies* (apply `\Phi`): the nonlinear term dies, leaving `2\Phi f + \Phi g = 0`, i.e.

$$\boxed{\ \Phi f = -\tfrac12\,\Phi g\ }$$

— the degree-`\le N` part of the minimizer is `-\tfrac12` times the truncated Fourier series of `g`,
given **explicitly**.

- *High frequencies* (apply `I-\Phi`): with `w=(I-\Phi)f`,

$$\boxed{\ p\,(I-\Phi)\!\big(|w|^{p-2}w\big) = -(I-\Phi)g\ }$$

— a nonlinear equation for the high-frequency part `w`, involving the `L^p` duality map
`w\mapsto |w|^{p-2}w`. (For `p=2` it collapses to `2w = -(I-\Phi)g`, i.e. `w=-\tfrac12(I-\Phi)g`,
and the whole minimizer is `f=-\tfrac12 g`, as expected.)

Together these two projected equations are the complete set of conditions characterizing the
minimum of `J_g`. ∎
