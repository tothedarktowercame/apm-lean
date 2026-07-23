<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m95A04: Foundations of distributions — embedding, derivatives, |x|, injectivity, a Green's function, and Sobolev completeness

## Why It's Hard

This is a tour of the foundational moves of distribution theory, and the difficulty is that each part
uses the *same* underlying device — **define everything by duality against test functions** — in a
different guise. A locally integrable function becomes a distribution by *integrating against* test
functions (a); the derivative is moved *onto* the test function by integration by parts (b); and
because that transfer never fails (test functions are infinitely smooth with compact support),
non-differentiable functions like `|x|` acquire derivatives, producing the jump `\mathrm{sgn}` and then
the Dirac mass `2\delta` (c). The conceptual traps are: realizing the function-to-distribution map is
*injective* (so the identification is honest); seeing that the *same* derivative operator has trivial
kernel on `\mathcal D` but a line of constants as kernel on `\mathcal D'` (because compact support
forbids nonzero constant test functions) (d); recognizing the causal Green's function (e); and
understanding that Sobolev completeness (f) works precisely because the distributional-derivative
relation is *closed* under `L^p` limits, again by duality with test functions.

## The Key Insight

**Duality makes operations robust.** Integration against `\mathcal D` turns functions into continuous
linear functionals, and integration by parts turns differentiation into the rule
`\langle Du, \varphi\rangle = -\langle u, \varphi'\rangle`. This one rule:

- gives every distribution infinitely many derivatives, so `|x| \mapsto \mathrm{sgn} \mapsto 2\delta`;
- is *insensitive to the space's constants*: on `\mathcal D` no nonzero constant has compact support
  (kernel of `D` is `\{0\}`), but on `\mathcal D'` the constant `1` is a distribution with `D1 = 0`
  (kernel is all constants);
- lets the equation `T' + \lambda T = \delta` be solved by the **causal** distribution
  `T = H(t)e^{-\lambda t}`, since `DT = \delta - \lambda T`;
- makes the Sobolev space `W^{1,p}` complete, because `Dw_n \to v` together with `w_n \to w` in `L^p`
  forces `v = Dw` (pass the limit through `\langle Dw_n, \varphi\rangle = -\langle w_n, \varphi'\rangle`),
  i.e. the graph of `D` is closed.

## Complete Proof

Let `\mathcal D = C_c^\infty` (test functions) and `\mathcal D'` its dual (distributions).

### (a) Locally integrable functions are distributions

For `f \in L^1_{loc}(\Omega)`, define the functional `T_f : \mathcal D(\Omega) \to \mathbb C`,

$$T_f(\varphi) = \int_\Omega f(x)\,\varphi(x)\,dx.$$

This is well defined (`\varphi` has compact support `K`, `f \in L^1(K)`, so `|T_f(\varphi)| \le \|\varphi\|_\infty \int_K|f| < \infty`),
linear, and continuous on `\mathcal D`: if `\varphi_n \to 0` in `\mathcal D` (supports in a fixed compact
`K`, derivatives `\to 0` uniformly), then `|T_f(\varphi_n)| \le \|\varphi_n\|_\infty \int_K |f| \to 0`.
So `T_f \in \mathcal D'`. Crucially the map `f \mapsto T_f` is **injective**: if `T_f = 0`, i.e.
`\int f\varphi = 0` for all `\varphi \in \mathcal D`, then `f = 0` a.e. (the fundamental lemma of the
calculus of variations / du Bois-Reymond). "All locally integrable functions are distributions" means
exactly this: `f \mapsto T_f` is an injective linear embedding `L^1_{loc} \hookrightarrow \mathcal D'`,
so we *identify* `f` with `T_f`; distributions of this form are called **regular**.

### (b) The derivative of a distribution

Motivated by integration by parts for smooth `f` (`\int f'\varphi = -\int f\varphi'`, boundary terms
vanishing by compact support), define for `u \in \mathcal D'` its derivative `Du` by

$$\boxed{\ (Du)(\varphi) = -u(\varphi') \quad \text{for all } \varphi \in \mathcal D,\ }$$

and more generally `\partial^\alpha u\,(\varphi) = (-1)^{|\alpha|} u(\partial^\alpha \varphi)`. Since
`\varphi \mapsto -\varphi'` is linear and continuous on `\mathcal D`, `Du \in \mathcal D'`. Thus **every
distribution is infinitely differentiable**, and on regular distributions `D` extends the classical
derivative.

### (c) Derivatives of `f(x) = |x|`

`|x|` is continuous, hence `L^1_{loc}`, hence a distribution. For `\varphi \in \mathcal D`,

$$\langle D|x|, \varphi\rangle = -\int_{-\infty}^\infty |x|\,\varphi'(x)\,dx
= -\Big[\int_{-\infty}^0 (-x)\varphi' + \int_0^\infty x\,\varphi'\Big].$$

Integrating by parts each piece (boundary terms vanish: `\varphi(\pm\infty)=0` and `x\varphi|_0 = 0`),
`\int_0^\infty x\varphi' = -\int_0^\infty \varphi` and `\int_{-\infty}^0(-x)\varphi' = \int_{-\infty}^0\varphi`, so

$$\langle D|x|, \varphi\rangle = \int_0^\infty \varphi - \int_{-\infty}^0 \varphi = \int \mathrm{sgn}(x)\,\varphi(x)\,dx,
\qquad \boxed{D|x| = \mathrm{sgn}(x)}$$

(`= 2H - 1`, `H` the Heaviside function). For the second derivative,

$$\langle D^2|x|, \varphi\rangle = -\langle \mathrm{sgn}, \varphi'\rangle = -\Big[\int_0^\infty \varphi' - \int_{-\infty}^0 \varphi'\Big]
= -\big[(-\varphi(0)) - (\varphi(0))\big] = 2\varphi(0), \qquad \boxed{D^2|x| = 2\delta.}$$

### (d) `D` is injective on `\mathcal D` but not on `\mathcal D'`

**On `\mathcal D`:** if `\varphi \in \mathcal D` and `\varphi' = 0`, then `\varphi` is constant; but a
constant with **compact support** must be `0`. So `D\varphi = 0 \Rightarrow \varphi = 0`: `D` is
injective on test functions.

**On `\mathcal D'`:** the constant distribution `1` (`\varphi \mapsto \int \varphi`) satisfies
`\langle D1, \varphi\rangle = -\int \varphi' = -[\varphi]_{-\infty}^{\infty} = 0`, so `D1 = 0` though
`1 \ne 0`. Hence `\ker D` on `\mathcal D'` contains all constants and `D` is **not** injective. The
contrast is entirely about whether nonzero constants live in the space: compact support excludes them
from `\mathcal D` but not from `\mathcal D'`. (In fact `Du = 0 \iff u` is a constant distribution.)

### (e) A distributional solution of `T' + \lambda T = \delta`

Take the **causal** candidate `T = H(t)\,e^{-\lambda t}` (`H` Heaviside). Writing `\psi(t) = e^{-\lambda t}`
(smooth), the product rule for distributions gives

$$DT = D(H\psi) = H'\psi + H\psi' = \psi(0)\,\delta + H\psi' = \delta - \lambda H e^{-\lambda t} = \delta - \lambda T,$$

using `\psi(0) = 1` and `\psi' = -\lambda\psi`. Therefore

$$T' + \lambda T = (\delta - \lambda T) + \lambda T = \delta, \qquad \boxed{T = H(t)\,e^{-\lambda t}.}$$

This is the fundamental solution (Green's function) of `\frac{d}{dt} + \lambda`. The general
distributional solution is `T = H(t)e^{-\lambda t} + C e^{-\lambda t}`, `C \in \mathbb C`, since the
homogeneous equation `T' + \lambda T = 0` has solutions `e^{-\lambda t}`.

### (f) `W = \{w \in L^p([0,1]) : Dw \in L^p([0,1])\}` is a Banach space

`\|w\|_W = \big(\|w\|_{L^p}^p + \|Dw\|_{L^p}^p\big)^{1/p}` is a norm — it is the `L^p \times L^p` norm of
the pair `(w, Dw)`, so the map `J : W \to L^p \times L^p`, `J(w) = (w, Dw)`, is a **linear isometry**.
It remains to prove completeness; equivalently, that the range of `J` is closed.

Let `(w_n)` be Cauchy in `W`. Then `(w_n)` and `(Dw_n)` are each Cauchy in `L^p([0,1])`, which is
complete, so `w_n \to w` and `Dw_n \to v` in `L^p` for some `w, v \in L^p`. We claim `v = Dw`. For any
`\varphi \in C_c^\infty(0,1)`, by definition of the distributional derivative,

$$\int_0^1 (Dw_n)\,\varphi\,dx = -\int_0^1 w_n\,\varphi'\,dx.$$

Pass `n \to \infty` using the `L^p`–`L^{p'}` duality (`\varphi, \varphi' \in L^{p'}` since `\varphi`
is smooth with compact support): the left side `\to \int_0^1 v\varphi` and the right side
`\to -\int_0^1 w\varphi'`. Hence

$$\int_0^1 v\,\varphi = -\int_0^1 w\,\varphi' = \langle Dw, \varphi\rangle \quad \forall \varphi,$$

so `Dw = v \in L^p`, i.e. `w \in W`. Finally

$$\|w_n - w\|_W^p = \|w_n - w\|_{L^p}^p + \|Dw_n - Dw\|_{L^p}^p = \|w_n - w\|_{L^p}^p + \|Dw_n - v\|_{L^p}^p \to 0,$$

so `w_n \to w` in `W`. Therefore `W` is complete — a **Banach space** (it is `W^{1,p}(0,1)`). The
mechanism: `J` realizes `W` as the subspace `\{(w, Dw)\}` of `L^p \times L^p`, and this subspace is
*closed* because the relation `v = Dw` survives `L^p` limits — which is exactly the duality identity
`\langle Dw_n, \varphi\rangle = -\langle w_n, \varphi'\rangle` passing to the limit. ∎

**Remark.** Every part is one face of the same idea: operations defined by *duality against test
functions* (integration in (a), integration by parts in (b)–(c), limits in (f)) are automatically
linear, continuous, and stable under limits, which is why distribution theory extends classical
calculus past the reach of pointwise differentiation while keeping the algebra intact.
