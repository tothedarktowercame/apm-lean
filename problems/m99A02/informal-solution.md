<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m99A02: A power of a logarithm just barely lands in H¹ (a Bertrand-integral borderline)

## Why It's Hard

This is a razor's-edge Sobolev membership question, and it is engineered to sit *just inside* the
boundary. The companion fact (problem m94A03) is that `\log|x| \notin H^1` in two dimensions: its gradient
`1/|x|` produces the divergent integral `\int dr/r`. Here `f(x) = -\big(\log|x|\big)^{1/3} = \big(\log\tfrac{1}{|x|}\big)^{1/3}`
is a *fractional power* of that same logarithm, which blows up at the origin only like
`(\log\tfrac1{|x|})^{1/3}` — far milder. The difficulty is that the `L^2`-membership of `f` is never in
doubt (any sub-polynomial singularity survives the `r\,dr` weight), so the entire question turns on the
gradient, and there the answer hinges on whether a delicate **Bertrand integral**
`\int_0^{1/2} \dfrac{dr}{r\,(\log\frac1r)^{4/3}}` converges — which it does, but only because the exponent
`4/3` exceeds `1` by a hair.

A second subtlety: one must confirm that the *distributional* gradient equals the pointwise (classical)
gradient, i.e. that no Dirac mass hides at the origin. That requires checking the singularity is mild
enough for the boundary flux in an integration by parts to vanish.

## The Key Insight

In polar coordinates (`n=2`, `dx = r\,dr\,d\theta`), with `f = (\log\frac1r)^{1/3}`:

$$f'(r) = -\frac{1}{3r}\Big(\log\tfrac1r\Big)^{-2/3}, \qquad |\nabla f| = |f'(r)| = \frac{1}{3r\,(\log\frac1r)^{2/3}}.$$

The gradient energy is therefore

$$\int_\Omega |\nabla f|^2\,dx = \frac{2\pi}{9}\int_0^{1/2} \frac{dr}{r\,(\log\frac1r)^{4/3}}
\ \overset{u = \log\frac1r}{=}\ \frac{2\pi}{9}\int_{\log 2}^{\infty} \frac{du}{u^{4/3}} < \infty,$$

a convergent `p`-integral at infinity with `p = \tfrac43 > 1`. So `\nabla f \in L^2`, and (with the trivial
`L^2`-bound on `f`) **`f \in H^1(\Omega)`**. The `1/3` power is exactly what converts the fatal log-exponent
`1` (the `\log|x|` case, `\int du/u`) into the survivable `4/3`. Because the singularity is so mild
(`f(r)\cdot r \to 0`), the distributional derivatives are simply the classical ones — no delta.

## Complete Proof

Let `\Omega = \{|x| < \tfrac12\} \subset \mathbb R^2`, `r = |x|`, and
`f(x) = -(\log|x|)^{1/3}`. On `\Omega`, `r < 1` so `\log r < 0`, and the real cube root gives
`(\log r)^{1/3} = -(\log\frac1r)^{1/3}`; hence

$$f = -(\log r)^{1/3} = \Big(\log\tfrac1r\Big)^{1/3} = (-\log r)^{1/3} > 0,$$

which `\to +\infty` as `r \to 0`, but only at the slow rate `(\log\frac1r)^{1/3}`.

### Step 1 — `f \in L^2(\Omega)`

$$\int_\Omega f^2\,dx = 2\pi \int_0^{1/2} \Big(\log\tfrac1r\Big)^{2/3} r\,dr < \infty,$$

because `(\log\frac1r)^{2/3}` grows slower than any negative power of `r`, while the factor `r` (from the
area element) makes the integrand integrable near `0`. So `f \in L^2`.

### Step 2 — The classical gradient and its `L^2` norm

Away from the origin, `f = (-\log r)^{1/3}` is smooth, with

$$f'(r) = \frac13(-\log r)^{-2/3}\cdot\Big(-\frac1r\Big) = -\frac{1}{3r}(-\log r)^{-2/3},
\qquad \nabla f = f'(r)\,\frac{x}{r} = -\frac{x}{3|x|^2}\,(-\log|x|)^{-2/3}.$$

Hence `|\nabla f|^2 = \dfrac{1}{9\,r^2\,(\log\frac1r)^{4/3}}`, and

$$\int_\Omega |\nabla f|^2\,dx = 2\pi\int_0^{1/2} \frac{1}{9 r^2 (\log\frac1r)^{4/3}}\,r\,dr
= \frac{2\pi}{9}\int_0^{1/2} \frac{dr}{r\,(\log\frac1r)^{4/3}}.$$

Substitute `u = \log\frac1r = -\log r`, so `du = -\frac{dr}{r}`; as `r: 0 \to \tfrac12`, `u: \infty \to \log 2`:

$$\int_0^{1/2} \frac{dr}{r\,(\log\frac1r)^{4/3}} = \int_{\log 2}^{\infty} \frac{du}{u^{4/3}}
= \Big[-3u^{-1/3}\Big]_{\log 2}^{\infty} = 3(\log 2)^{-1/3} < \infty,$$

since the exponent `4/3 > 1`. Therefore

$$\int_\Omega |\nabla f|^2\,dx = \frac{2\pi}{9}\cdot 3(\log 2)^{-1/3} = \frac{2\pi}{3}\,(\log 2)^{-1/3} < \infty,$$

so the classical gradient is in `L^2(\Omega)`.

### Step 3 — The classical gradient *is* the distributional gradient (no delta)

`f \in L^1_{loc}` (Step 1) and `\nabla f \in L^1_{loc}` (indeed `L^2`, Step 2), so the only question is
whether a singular term appears at `0`. Integrate by parts on `\Omega \setminus B(0,\varepsilon)` against a
test function `\varphi`: the interior terms reproduce `-\int \nabla f\cdot \varphi`, and the boundary term
over `\{|x| = \varepsilon\}` is bounded by

$$\Big|\int_{|x|=\varepsilon} f\,\varphi\,\nu_i\,dS\Big| \le \|\varphi\|_\infty \cdot f(\varepsilon)\cdot 2\pi\varepsilon
= C\,\varepsilon\,\Big(\log\tfrac1\varepsilon\Big)^{1/3} \xrightarrow[\varepsilon\to0]{} 0,$$

since `\varepsilon(\log\frac1\varepsilon)^{1/3} \to 0`. Hence no Dirac mass is produced, and the
distributional first-order derivatives equal the classical ones:

$$\boxed{\ \frac{\partial f}{\partial x_i} = -\frac{x_i}{3\,|x|^2}\,\big(-\log|x|\big)^{-2/3}
= -\frac{x_i}{3\,|x|^2\,(\log\frac1{|x|})^{2/3}}, \qquad i = 1, 2,\ }$$

which are honest `L^2(\Omega)` functions (Step 2).

### Conclusion

`f \in L^2(\Omega)` and `\nabla f \in L^2(\Omega)`, so

$$\boxed{\ f \in H^1(\Omega).\ }\qquad\blacksquare$$

**Remark.** This is the fractional-power refinement of the classic threshold `\log|x| \notin H^1(\mathbb R^2)`.
For `f = (\log\frac1r)^s`, `|\nabla f|^2 \sim r^{-2}(\log\frac1r)^{2s-2}`, and the energy integral becomes the
**Bertrand integral** `\int_0 \frac{dr}{r(\log\frac1r)^{2-2s}}`, which converges iff `2 - 2s > 1`, i.e.
`s < \tfrac12`. The pure logarithm is `s = 1` (divergent); here `s = \tfrac13 < \tfrac12`, comfortably inside
— the exponent works out to `2 - 2s = \tfrac43 > 1`. The `1/3` power is precisely what tames the
log-singularity enough to belong to `H^1`, and the borderline is the half-power `s = \tfrac12`.
