<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m96J05: exp of a difference-quotient operator converges to the shift, via Fourier multipliers

# (e^{d/dx} is translation by one)

## Why It's Hard

The object `\exp(D_\epsilon)` is the exponential of an *operator* — an infinite series
`\sum_k D_\epsilon^k/k!` of compositions of difference quotients — and asking it to converge to the
unit-shift `Tf(x) = f(x+1)` looks daunting if attacked directly in physical space. Each power
`D_\epsilon^k` is a `(2k{+}1)`-point finite-difference stencil, and summing the exponential series of
stencils by hand is hopeless. Worse, `D_\epsilon` is unbounded-ish (`\|D_\epsilon\| = 1/|\epsilon| \to \infty`),
so naive estimates blow up as `\epsilon \to 0`.

The resolution is to recognize that `D_\epsilon` and `T` are both **translation-invariant** operators, so
the Fourier transform diagonalizes them simultaneously into multiplication by a *symbol* (a function of the
frequency `\xi`). Then `\exp` of the operator becomes `\exp` of the symbol — an ordinary scalar
exponential — and the whole problem collapses to a pointwise limit of symbols plus dominated convergence.
The conceptual punchline is the classical identity `e^{d/dx} = (\text{shift by }1)`: since `D_\epsilon` is
the symmetric-difference approximation of `d/dx`, `\exp(D_\epsilon)` approximates `e^{d/dx} = T`.

## The Key Insight

Under the Fourier transform, translation by `a` becomes multiplication by `e^{ia\xi}`, so

$$\widehat{D_\epsilon f}(\xi) = \frac{e^{i\epsilon\xi} - e^{-i\epsilon\xi}}{2\epsilon}\,\hat f(\xi)
= \frac{i\sin(\epsilon\xi)}{\epsilon}\,\hat f(\xi).$$

`D_\epsilon` is therefore the **Fourier multiplier** with symbol `m_\epsilon(\xi) = i\sin(\epsilon\xi)/\epsilon`,
and `\exp(D_\epsilon)` is multiplication by `\exp(m_\epsilon(\xi)) = \exp\!\big(i\sin(\epsilon\xi)/\epsilon\big)`.
Two facts finish everything:

- **Pointwise limit:** `\sin(\epsilon\xi)/\epsilon \to \xi`, so `\exp(m_\epsilon(\xi)) \to e^{i\xi}` — and
  `e^{i\xi}` is exactly the symbol of the unit shift `T`.
- **Uniform bound:** `m_\epsilon(\xi)` is `i` times a *real* number, so `|\exp(m_\epsilon(\xi))| = 1`; hence
  `|\exp(m_\epsilon(\xi)) - e^{i\xi}| \le 2`, giving the dominating function `4|\hat f|^2 \in L^1`.

Plancherel converts `L^2`-convergence of the operators into `L^2`-convergence of the symbols times
`\hat f`, and dominated convergence does the rest.

## Complete Proof

Use the Fourier transform `\hat f(\xi) = \int_{\mathbb R} f(x)e^{-i\xi x}\,dx`, a (scaled) isometry of
`L^2(\mathbb R)` by Plancherel: `\|g\|_{L^2} = c\,\|\hat g\|_{L^2}` for a fixed constant `c`. Recall that
translation transforms as `\widehat{f(\cdot + a)}(\xi) = e^{ia\xi}\hat f(\xi)`.

**Step 1 — `D_\epsilon` as a Fourier multiplier.** Since `D_\epsilon f(x) = \tfrac{1}{2\epsilon}\big(f(x+\epsilon) - f(x-\epsilon)\big)`,

$$\widehat{D_\epsilon f}(\xi) = \frac{e^{i\epsilon\xi} - e^{-i\epsilon\xi}}{2\epsilon}\,\hat f(\xi)
= \frac{i\sin(\epsilon\xi)}{\epsilon}\,\hat f(\xi) =: m_\epsilon(\xi)\,\hat f(\xi).$$

The symbol `m_\epsilon(\xi) = i\sin(\epsilon\xi)/\epsilon` is bounded, `|m_\epsilon(\xi)| \le 1/|\epsilon|`,
so `D_\epsilon` is bounded with `\|D_\epsilon\| = \sup_\xi |m_\epsilon(\xi)| = 1/|\epsilon| < \infty`.

**Step 2 — `\exp(D_\epsilon)` as a Fourier multiplier.** Since `D_\epsilon` is bounded, the exponential
series `\exp(D_\epsilon) = \sum_{k=0}^\infty D_\epsilon^k/k!` converges in operator norm. The Fourier
transform is a unitary equivalence carrying `D_\epsilon` to multiplication by `m_\epsilon`, hence
`D_\epsilon^k` to multiplication by `m_\epsilon^k`, and `\exp(D_\epsilon)` to multiplication by
`\sum_k m_\epsilon^k/k! = \exp(m_\epsilon)`. Therefore

$$\widehat{\exp(D_\epsilon)f}(\xi) = \exp\!\big(m_\epsilon(\xi)\big)\,\hat f(\xi)
= \exp\!\Big(\frac{i\sin(\epsilon\xi)}{\epsilon}\Big)\,\hat f(\xi).$$

**Step 3 — The target `T`.** `Tf(x) = f(x+1)` has `\widehat{Tf}(\xi) = e^{i\xi}\hat f(\xi)`, the multiplier
with symbol `e^{i\xi}`.

**Step 4 — Reduce to the symbols and apply dominated convergence.** By Plancherel,

$$\big\|\exp(D_\epsilon)f - Tf\big\|_{L^2}^2 = c^2 \int_{\mathbb R}
\Big|\exp\!\Big(\tfrac{i\sin(\epsilon\xi)}{\epsilon}\Big) - e^{i\xi}\Big|^2\,|\hat f(\xi)|^2\,d\xi.$$

Examine the integrand `g_\epsilon(\xi) = \big|\exp(i\sin(\epsilon\xi)/\epsilon) - e^{i\xi}\big|^2\,|\hat f(\xi)|^2`:

- *Pointwise convergence.* For each fixed `\xi`, `\dfrac{\sin(\epsilon\xi)}{\epsilon} = \xi\,\dfrac{\sin(\epsilon\xi)}{\epsilon\xi} \to \xi`
  as `\epsilon \to 0`. By continuity of `\exp`, `\exp(i\sin(\epsilon\xi)/\epsilon) \to e^{i\xi}`, so
  `g_\epsilon(\xi) \to 0`.
- *Domination.* Because `\sin(\epsilon\xi)/\epsilon` is real, `\big|\exp(i\sin(\epsilon\xi)/\epsilon)\big| = 1`,
  and `|e^{i\xi}| = 1`, so `\big|\exp(i\sin(\epsilon\xi)/\epsilon) - e^{i\xi}\big| \le 2`. Hence
  `g_\epsilon(\xi) \le 4\,|\hat f(\xi)|^2`, and `4|\hat f|^2 \in L^1(\mathbb R)` since `\hat f \in L^2`.

By the **dominated convergence theorem**, `\int g_\epsilon(\xi)\,d\xi \to 0` as `\epsilon \to 0`. Therefore

$$\big\|\exp(D_\epsilon)f - Tf\big\|_{L^2}^2 = c^2 \int g_\epsilon \to 0,$$

i.e.

$$\boxed{\ \exp(D_\epsilon)f \xrightarrow[\ \epsilon\to 0\ ]{L^2(\mathbb R)} Tf, \qquad Tf(x) = f(x+1).\ }\qquad\blacksquare$$

**Remark.** The result is the rigorous, `L^2` form of the operator identity `e^{\,d/dx} = (\text{shift by }1)`:
formally `e^{a\,d/dx}f(x) = \sum_k \tfrac{a^k}{k!}f^{(k)}(x) = f(x+a)` is Taylor's theorem read as an operator
exponential. Here `D_\epsilon` is the symmetric-difference approximation to `d/dx` (its symbol
`i\sin(\epsilon\xi)/\epsilon \to i\xi`, the symbol of `d/dx`), so `\exp(D_\epsilon) \to \exp(d/dx) = T`. The
Fourier transform is what makes this airtight: it simultaneously diagonalizes every translation-invariant
operator into multiplication by its symbol, turning a frightening operator exponential into the scalar
exponential `\exp(i\sin(\epsilon\xi)/\epsilon)`, whose modulus-`1` boundedness is exactly the uniform control
needed for dominated convergence.
