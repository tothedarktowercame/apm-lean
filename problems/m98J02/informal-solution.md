<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m98J02: Compactly supported distributions, convolution, and solving Tw = f by a fundamental solution

## Why It's Hard

This problem builds the convolution of two distributions and then uses it to solve a PDE — and the
machinery is delicate precisely because distributions are not functions you can multiply or integrate
pointwise. The central technical issue lives in part (b): convolution `u * v` of two general distributions
is **not defined** (you would need to "integrate `u(y)v(x-y)` over all `y`", but the overlap is unbounded).
The compact-support hypothesis on `u` is exactly what fixes this — it produces an intermediate quantity
that is smooth but not compactly supported, and a *compactly supported* distribution is precisely the kind
of object that can be paired with arbitrary smooth functions (`\mathcal E'` is the dual of `C^\infty`).
Seeing why "one factor compact" is the right hypothesis, and where it is used, is the heart of (a)–(c).

Part (d) is the **fundamental-solution method**: given `Tw_0 = \delta_0`, the convolution `w = w_0 * f`
solves `Tw = f` because a constant-coefficient operator commutes with convolution and `\delta_0` is the
convolution identity. The subtleties are the *regularity* claim (the convolution inherits the smoothness of
`f`) and *uniqueness* — which fails, because the non-elliptic operator `T` has a large kernel.

## The Key Insight

- **(a)** `u` has compact support if it vanishes outside some compact `K`: `\langle u,\varphi\rangle = 0`
  whenever `\operatorname{supp}\varphi \cap K = \varnothing`; equivalently `\operatorname{supp} u` is compact.
- **(b)** For `u \in \mathcal E'` (compact support), `v \in \mathcal D'`, the function
  `\Psi(x) = \langle v_y, \varphi(x+y)\rangle` is `C^\infty` (but not compactly supported), and since `u`
  acts on **all** smooth functions, `\langle u*v, \varphi\rangle := \langle u_x, \Psi(x)\rangle` is defined.
  This is exactly where compact support of `u` is essential.
- **(c)** `\varphi \mapsto \Psi_\varphi` is continuous `\mathcal D \to \mathcal E`, and `u` is continuous on
  `\mathcal E`, so their composition is continuous — `u*v \in \mathcal D'`.
- **(d)** `w = w_0 * f` gives `Tw = (Tw_0)*f = \delta_0 * f = f`; convolution with the `C^2` function `f`
  makes `w \in C^2` (derivatives fall on `f`); and the solution is **not unique** (`T` has nontrivial
  kernel — e.g. `T1 = 0`, `Tx = 0`).

## Complete Proof

### (a) Compact support

A distribution `u \in \mathcal D'(\mathbb R^n)` **vanishes on an open set** `\Omega` if
`\langle u, \varphi\rangle = 0` for all `\varphi \in \mathcal D` with `\operatorname{supp}\varphi \subseteq \Omega`.
The **support** of `u`, `\operatorname{supp} u`, is the complement of the largest open set on which `u`
vanishes. We say `u` **has compact support** if `\operatorname{supp} u` is compact; equivalently, there is a
compact set `K` with `\langle u, \varphi\rangle = 0` for every test function `\varphi` whose support is
disjoint from `K`. Such distributions form `\mathcal E'`, and they extend to act continuously on **all** of
`C^\infty = \mathcal E` (not merely `\mathcal D`).

### (b) Definition of `u * v` for `u` of compact support

Let `u \in \mathcal E'` and `v \in \mathcal D'`. For `\varphi \in \mathcal D`, define

$$\Psi_\varphi(x) = \langle v_y,\, \varphi(x+y)\rangle.$$

For each fixed `x`, `y \mapsto \varphi(x+y)` is a test function, so `\Psi_\varphi(x)` is defined; as `x`
varies, `x \mapsto \varphi(x + \cdot)` is a smooth `\mathcal D`-valued map, so `\Psi_\varphi \in C^\infty`
with `\partial^\alpha \Psi_\varphi(x) = \langle v_y, \partial_x^\alpha \varphi(x+y)\rangle`. Although
`\Psi_\varphi` need **not** have compact support, `u \in \mathcal E'` acts on all smooth functions, so we may
define

$$\boxed{\ \langle u * v, \varphi\rangle := \langle u_x,\, \langle v_y, \varphi(x+y)\rangle\rangle = \langle u, \Psi_\varphi\rangle.\ }$$

This is the point of the compact-support hypothesis: it lets `u` be applied to the smooth, non-compactly-
supported function `\Psi_\varphi`.

### (c) `u * v` is a distribution

`u * v` is **linear** in `\varphi` because `\varphi \mapsto \Psi_\varphi` is linear and `u` is linear.

For **continuity**, suppose `\varphi_n \to 0` in `\mathcal D`: their supports lie in a fixed compact `L` and
all derivatives `\partial^\beta \varphi_n \to 0` uniformly. Then for `x` in any compact set, the test
functions `\varphi_n(x + \cdot)` have supports in a fixed compact set and tend to `0` in `\mathcal D`, so by
continuity of `v`, `\partial^\alpha \Psi_{\varphi_n}(x) = \langle v_y, \partial^\alpha \varphi_n(x+y)\rangle \to 0`
uniformly on compacts for each `\alpha`. That is exactly `\Psi_{\varphi_n} \to 0` in `\mathcal E = C^\infty`.
Since `u \in \mathcal E'` is continuous on `\mathcal E`,

$$\langle u*v, \varphi_n\rangle = \langle u, \Psi_{\varphi_n}\rangle \to 0.$$

Thus `u * v` is a continuous linear functional on `\mathcal D`, i.e. `u * v \in \mathcal D'`. ∎

### (d) Solving `Tw = f` with `T = 2\,\partial_x^2 - \partial_y + 3\,\partial_x\partial_y`

Assume `Tw_0 = \delta_0` (a fundamental solution) and `f \in C^2(\mathbb R^2)` (compactly supported, so the
convolution below is covered by part (b) with `f` the compactly supported factor).

**A solution.** Set `w = w_0 * f`. Since `T` is a **constant-coefficient** differential operator, it
commutes with convolution, `\partial^\alpha(w_0 * f) = (\partial^\alpha w_0) * f`, so

$$Tw = T(w_0 * f) = (Tw_0) * f = \delta_0 * f = f,$$

using that `\delta_0` is the identity for convolution (`\delta_0 * f = f`). Hence `w = w_0 * f` solves
`Tw = f`.

**Regularity `w \in C^2`.** Differentiating the convolution onto the smooth factor, for `|\alpha| \le 2`,

$$\partial^\alpha w = \partial^\alpha (w_0 * f) = w_0 * (\partial^\alpha f),$$

and `\partial^\alpha f` is continuous (compactly supported); convolution of a (locally integrable
fundamental-solution) distribution with a continuous compactly supported function is continuous, so all
partials of `w` up to order `2` exist and are continuous. Therefore `w \in C^2(\mathbb R^2)`, and `Tw = f`
holds in the **classical** sense. (Equivalently: convolution with the `C^2` function `f` cannot lose
smoothness — the derivatives always fall on `f`.)

**Uniqueness — no.** The solution is **not unique**: if `Tw = f` and `Tw_h = 0`, then `T(w + w_h) = f`. The
operator `T` has an infinite-dimensional kernel, because it is *not elliptic* — its principal symbol
`-2\xi^2 - 3\xi\eta = -\xi(2\xi + 3\eta)` has real characteristics. Concretely:

$$T(1) = 0, \qquad T(x) = 2\cdot 0 - 0 + 3\cdot 0 = 0, \qquad T(ax + b) = 0,$$

and `T(e^{ax+by}) = (2a^2 + 3ab - b)e^{ax+by} = 0` whenever `2a^2 + 3ab - b = 0` (a one-parameter family).
So one can add any such homogeneous solution `w_h` to `w` and still solve `Tw = f`. Uniqueness is recovered
only by imposing side conditions (boundary/initial data, or growth/support restrictions). ∎

**Remark.** Parts (a)–(c) are the apparatus that makes (d) rigorous: a *fundamental solution* `w_0`
(`Tw_0 = \delta_0`) is a **convolution inverse** of the constant-coefficient operator `T`, and `w_0 * f`
solves `Tw = f` for the same reason `\delta_0` is the convolution unit and `T` commutes with `*`. The
compact-support hypothesis from (b) is what licenses the convolution `w_0 * f` (here via the compactly
supported `f`). The failure of uniqueness is the distributional shadow of `T` being a non-elliptic operator
with a large null space — fundamental solutions are themselves non-unique up to the kernel.
