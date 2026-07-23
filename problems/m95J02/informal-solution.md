<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m95J02: The fundamental solution of the Laplacian by radial reduction to an Euler equation

## Why It's Hard

The equation `\triangle u = \delta` mixes two very different kinds of information, and the trick is to
separate them. Radial symmetry collapses the *partial* differential equation into an *ordinary*
differential equation in `r = |x|` — an Euler (equidimensional) equation solved by the trial `u = r^s`.
But the trial `r^s` solves only `\triangle u = 0` **away from the origin**; the Dirac mass at `0` is
completely invisible to that ODE. So the indicial equation hands you the *shape* of the solution and the
free constants, but it cannot by itself fix the multiplicative constant `A` — that requires a separate,
*global* argument tying the strength of the singularity to the unit mass of `\delta`.

A second subtlety is that the dimension `n` controls a **bifurcation**: the two roots of the indicial
equation collide exactly when `n = 2`, so the `n=2` fundamental solution is logarithmic while `n \ge 3`
gives a power `r^{2-n}`. Missing this degenerate case is the standard error. Finally, one must see why
the *point-source* solution `u` solves the *arbitrary-source* Poisson equation — namely by convolution,
which works precisely because `\triangle` commutes with translation.

## The Key Insight

For a radial function the Laplacian is

$$\triangle u = u''(r) + \frac{n-1}{r}\,u'(r) = \frac{1}{r^{n-1}}\big(r^{n-1}u'\big)'.$$

Setting this to zero and substituting `u = r^s` gives the **indicial equation**

$$s(s-1) + (n-1)s = s\,(s + n - 2) = 0 \ \Longrightarrow\ s = 0 \ \text{ or } \ s = 2 - n,$$

so harmonic radial solutions are spanned by `\{1,\ r^{2-n}\}` for `n \ne 2`, and by `\{1,\ \log r\}` for
`n = 2` (the degenerate double root `s = 0`). The additive constant is irrelevant (it stays harmonic),
so `u = A r^{2-n}` (or `A\log r`). The constant `A` is **not** determined by the ODE; it is fixed by the
**divergence theorem on a small sphere**: integrating `\triangle u = \delta` over `B(0,\varepsilon)`,

$$1 = \int_{B(0,\varepsilon)} \triangle u = \int_{\partial B(0,\varepsilon)} \nabla u \cdot \hat n \,dS = u'(\varepsilon)\cdot \omega_{n-1}\varepsilon^{n-1},$$

a flux that is independent of `\varepsilon` and pins `A`. Then `u` solves `\triangle u = f` for general `f`
by **convolution** `u = \Phi * f`, since `\triangle(\Phi * f) = (\triangle\Phi)*f = \delta * f = f`.

## Complete Proof

Let `\omega_{n-1} = |S^{n-1}| = \dfrac{2\pi^{n/2}}{\Gamma(n/2)}` be the surface area of the unit sphere.

### Step 1 — Reduce to a radial ODE

For `u = u(r)`, `r = |x|`, the chain rule gives `\nabla u = u'(r)\,\hat r` and

$$\triangle u = u'' + \frac{n-1}{r}\,u' = \frac{1}{r^{n-1}}\big(r^{n-1}u'\big)'.$$

Away from the origin `\triangle u = 0` therefore becomes the **Euler equation**

$$u'' + \frac{n-1}{r}\,u' = 0, \qquad r > 0. \tag{1}$$

### Step 2 — Solve by `u = r^s`

Substituting `u = r^s` (so `u' = s\,r^{s-1}`, `u'' = s(s-1)r^{s-2}`) into (1):

$$r^{s-2}\big[s(s-1) + (n-1)s\big] = r^{s-2}\, s(s+n-2) = 0 \ \Longrightarrow\ s = 0 \text{ or } s = 2-n.$$

- **`n \ge 3`:** the roots `0` and `2-n` are distinct, so the radial harmonic functions are
  `u(r) = A\,r^{2-n} + B`.
- **`n = 2`:** the roots coincide (`s = 0` double), and the second independent solution of (1) is `\log r`
  (directly: `(1)` reads `(r u')' = 0`, so `r u' = c`, `u' = c/r`, `u = c\log r + B`). Thus
  `u(r) = A\log r + B`.

The constant `B` is harmonic everywhere and contributes nothing to `\triangle u = \delta`; drop it (or fix
it by a normalization/decay condition). So `u = A\,r^{2-n}` (`n\ge3`) or `u = A\log r` (`n=2`).

### Step 3 — Evaluate the constant `A` by the flux condition

The ODE cannot see the `\delta`; `A` is determined by requiring that the singularity carry unit mass.
Integrate `\triangle u = \delta` over the small ball `B(0,\varepsilon)` and apply the divergence theorem
(outward normal `\hat n = \hat r`, `\nabla u\cdot\hat n = u'(\varepsilon)`):

$$1 = \int_{B(0,\varepsilon)} \triangle u\,dx = \int_{\partial B(0,\varepsilon)} u'(\varepsilon)\,dS
= u'(\varepsilon)\,\omega_{n-1}\,\varepsilon^{n-1}. \tag{2}$$

- **`n \ge 3`:** `u = A r^{2-n}`, `u'(\varepsilon) = A(2-n)\varepsilon^{1-n}`. Then (2) gives
  `A(2-n)\varepsilon^{1-n}\cdot \omega_{n-1}\varepsilon^{n-1} = A(2-n)\omega_{n-1} = 1`, so

$$\boxed{\ A = \frac{1}{(2-n)\,\omega_{n-1}} = -\frac{1}{(n-2)\,\omega_{n-1}}, \qquad
u(x) = -\frac{1}{(n-2)\,\omega_{n-1}}\,\frac{1}{|x|^{n-2}}.\ }$$

  (Check `n=3`: `\omega_2 = 4\pi`, `A = -\tfrac{1}{4\pi}`, `u = -\tfrac{1}{4\pi|x|}` — the Newtonian
  potential.)

- **`n = 2`:** `u = A\log r`, `u'(\varepsilon) = A/\varepsilon`. Then (2) gives
  `(A/\varepsilon)\cdot \omega_1\,\varepsilon = A\cdot 2\pi = 1`, so

$$\boxed{\ A = \frac{1}{2\pi}, \qquad u(x) = \frac{1}{2\pi}\,\log|x|.\ }$$

In every case the flux (2) is independent of `\varepsilon`, which is exactly the consistency that makes
`\triangle u = \delta` hold. (One can verify directly that these `u` are locally integrable and that the
distribution `\triangle u` equals `\delta`.)

### Step 4 — Solving the Poisson equation `\triangle u = f` via convolution

Let `\Phi` denote the fundamental solution just found, so `\triangle \Phi = \delta`. For a source `f`
(say `f \in C_c^\infty(\mathbb{R}^n)`, or with enough decay), define

$$u = \Phi * f, \qquad u(x) = \int_{\mathbb{R}^n} \Phi(x - y)\,f(y)\,dy.$$

Because the Laplacian has constant coefficients it commutes with translation and hence with convolution:

$$\triangle u = \triangle(\Phi * f) = (\triangle \Phi) * f = \delta * f = f.$$

So `u = \Phi * f` solves `\triangle u = f`. Concretely, this superposes the point-source responses weighted
by the source density: e.g. for `n \ge 3`,

$$u(x) = -\frac{1}{(n-2)\omega_{n-1}}\int_{\mathbb{R}^n} \frac{f(y)}{|x-y|^{n-2}}\,dy,$$

the Newtonian potential of `f` (the logarithmic potential `\tfrac{1}{2\pi}\int \log|x-y|\,f(y)\,dy` for
`n=2`). The convolution converges because `\Phi \in L^1_{loc}` (`r^{2-n}` and `\log r` are integrable near
`0` in `\mathbb{R}^n`) and `f` is well behaved. ∎

**Remark.** The division of labor is the lesson: the **Euler ODE** (indicial equation `s(s+n-2)=0`) supplies
the *form* `r^{2-n}` or `\log r` and exhibits `n=2` as the degenerate double-root case; the **divergence
theorem** supplies the *constant* `A` by matching the spherical flux to the unit mass of `\delta`; and
**convolution** lifts the single point-source solution to the response for an arbitrary source `f`. The ODE
knows the shape, Gauss's theorem knows the size, and translation-invariance knows how to superpose.
