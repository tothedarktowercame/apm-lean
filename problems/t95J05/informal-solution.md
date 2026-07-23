<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t95J05: A 3-form descends to ℝP³ (antipodal invariance) and integrates to −π² via Stokes

## Why It's Hard

The problem links three ideas — descent through a covering, orientability of `\mathbb{RP}^3`, and Stokes —
and each has a parity subtlety that is easy to get backwards:

- **(a)** A form `i^*\omega` on `S^3` descends to `\mathbb{RP}^3=S^3/\{\pm1\}` **iff it is invariant under the
  antipodal map** `a:x\mapsto-x` (the deck transformation). The check is delicate because invariance is a
  product of two odd things: the coefficient `x_2^3-4x_1` is **odd** under `x\mapsto-x` (it negates), and the
  3-form `dx_2\wedge dx_3\wedge dx_4` is also **odd** (three sign flips give `(-1)^3=-1`). Odd `\times` odd =
  **even**, so `a^*\omega=\omega` and the form descends — but had the coefficient been *even*, the form would
  *not* descend. Tracking these two signs correctly is the crux.
- **(b)** Integrating over `\mathbb{RP}^3` presupposes it is **orientable**, which holds because `\dim S^3=3`
  is odd (the antipodal map on `S^3` has degree `(-1)^{3+1}=+1`, orientation-preserving). The integral then
  relates to `\int_{S^3}i^*\omega` by the **degree-2 cover** (a factor of `\tfrac12`), and Stokes converts
  that to a ball integral of `d\omega`. Missing the `\tfrac12`, or the orientability, derails it.

## The Key Insight

- **(a)** `a^*\omega = (\underbrace{-1}_{\text{coeff odd}})(\underbrace{-1}_{\text{3-form odd}})\,\omega =
  \omega`, so `i^*\omega` is antipodally invariant and descends to a unique `\eta` on `\mathbb{RP}^3`
  (uniqueness because `\pi` is a local diffeomorphism, so `\pi^*` is injective).
- **(b)** With `\pi` an orientation-preserving double cover, `\int_{S^3}\pi^*\eta = 2\int_{\mathbb{RP}^3}\eta`,
  so
  $$
  \int_{\mathbb{RP}^3}\eta = \tfrac12\int_{S^3} i^*\omega = \tfrac12\int_{B^4} d\omega,
  $$
  and `d\omega = -4\,dx_1\wedge dx_2\wedge dx_3\wedge dx_4`, giving `\tfrac12\cdot(-4)\operatorname{vol}(B^4) =
  -2\operatorname{vol}(B^4) = -2\cdot\tfrac{\pi^2}{2} = -\pi^2`.

## Complete Proof

Here `\omega=(x_2^3-4x_1)\,dx_2\wedge dx_3\wedge dx_4\in\Omega^3(\mathbb R^4)`, `i:S^3\hookrightarrow\mathbb
R^4` is inclusion, `\pi:S^3\to\mathbb{RP}^3` is the antipodal quotient (a smooth double cover), and `a:\mathbb
R^4\to\mathbb R^4`, `a(x)=-x`, restricts to the antipodal map of `S^3`, the nontrivial deck transformation of
`\pi`.

### (a) Existence and uniqueness of `\eta`

**`\omega` is antipodally invariant.** Compute `a^*\omega` (pull back by `x\mapsto-x`): each `x_j\mapsto-x_j`,
so
$$
\text{coefficient: } \ (x_2^3-4x_1)\ \longmapsto\ (-x_2)^3-4(-x_1) = -x_2^3+4x_1 = -(x_2^3-4x_1),
$$
$$
\text{3-form: } \ dx_2\wedge dx_3\wedge dx_4\ \longmapsto\ (-dx_2)\wedge(-dx_3)\wedge(-dx_4) = (-1)^3\,dx_2\wedge dx_3\wedge dx_4 = -\,dx_2\wedge dx_3\wedge dx_4 .
$$
Multiplying the two,
$$
a^*\omega = (-1)(-1)\,(x_2^3-4x_1)\,dx_2\wedge dx_3\wedge dx_4 = \omega .
$$
Since `a` maps `S^3` to `S^3` and `i\circ a = a\circ i`, pulling back the inclusion,
$$
a^*(i^*\omega) = i^*(a^*\omega) = i^*\omega .
$$
So `i^*\omega` is invariant under the deck transformation `a` of the covering `\pi`.

**Descent (existence).** A differential form on the total space of a covering descends to the base iff it is
invariant under all deck transformations. The deck group of `\pi:S^3\to\mathbb{RP}^3` is `\{\mathrm{id},a\}`,
and `i^*\omega` is invariant under both; hence there is a `3`-form `\eta\in\Omega^3(\mathbb{RP}^3)` with
`\pi^*\eta = i^*\omega`. (Concretely, on a small evenly-covered set `U\subset\mathbb{RP}^3` with local section
`s`, set `\eta|_U = s^*(i^*\omega)`; invariance makes this independent of which sheet `s` chooses.)

**Uniqueness.** `\pi` is a surjective local diffeomorphism, so `\pi^*` is injective on forms: if
`\pi^*\eta_1=\pi^*\eta_2=i^*\omega`, then at any `[x]\in\mathbb{RP}^3`, applying a local inverse of `\pi`
gives `\eta_1=\eta_2` at `[x]`. Hence `\eta` is unique. ∎

### (b) `\int_{\mathbb{RP}^3}\eta = -\pi^2`

**`\mathbb{RP}^3` is orientable and `\pi` is an orientation-preserving double cover.** Because `\dim S^3=3` is
odd, the antipodal map `a` of `S^3` has degree `(-1)^{3+1}=+1`, i.e. it is orientation-preserving; therefore
`\mathbb{RP}^3 = S^3/\{\pm1\}` is orientable, with the orientation for which `\pi` is an
orientation-preserving `2`-sheeted covering. For such a cover, integration multiplies by the number of
sheets:
$$
\int_{S^3} \pi^*\eta = 2\int_{\mathbb{RP}^3}\eta \quad\Longrightarrow\quad \int_{\mathbb{RP}^3}\eta = \tfrac12\int_{S^3}\pi^*\eta = \tfrac12\int_{S^3} i^*\omega .
$$

**Stokes on the ball.** `S^3=\partial B^4` with the induced (outward) orientation, so
$$
\int_{S^3} i^*\omega = \int_{\partial B^4}\omega = \int_{B^4} d\omega .
$$
Compute `d\omega`:
$$
d\omega = d(x_2^3-4x_1)\wedge dx_2\wedge dx_3\wedge dx_4 = (3x_2^2\,dx_2 - 4\,dx_1)\wedge dx_2\wedge dx_3\wedge dx_4 .
$$
The `3x_2^2\,dx_2` term wedges to `0` (repeated `dx_2`), leaving
$$
d\omega = -4\,dx_1\wedge dx_2\wedge dx_3\wedge dx_4 = -4\,dV,
$$
the standard volume form scaled by `-4`. Hence, using `\operatorname{vol}(B^4)=\dfrac{\pi^2}{2}`,
$$
\int_{S^3} i^*\omega = \int_{B^4}(-4)\,dV = -4\operatorname{vol}(B^4) = -4\cdot\frac{\pi^2}{2} = -2\pi^2 .
$$

**Conclusion.**
$$
\int_{\mathbb{RP}^3}\eta = \tfrac12\int_{S^3} i^*\omega = \tfrac12\,(-2\pi^2) = \boxed{-\pi^2}.
$$
(The sign depends on the chosen orientation of `\mathbb{RP}^3`; with the opposite orientation the value is
`+\pi^2`. The magnitude `\pi^2` is intrinsic.) ∎

**Remark.** *(The hint's "`\operatorname{vol}B^4=\pi^4/2`" should read `\pi^2/2`, the standard value
`\pi^{n/2}/\Gamma(\tfrac n2+1)` at `n=4`.)* The two parts hinge on the parity of the dimension `3`. In part
(a), antipodal invariance survives because the coefficient and the `3`-form are **each** odd, so their
product is even — a 3-form's volume factor flips sign under `x\mapsto-x` exactly `(-1)^3` times, which the odd
coefficient compensates. In part (b), the *odd*-dimensionality of `S^3` is what makes the antipodal map
orientation-preserving and `\mathbb{RP}^3` orientable, so the integral is even defined; the double cover
contributes the factor `\tfrac12`, and Stokes reduces everything to the divergence-like constant
`d\omega=-4\,dV` integrated over the ball. (On the even-dimensional `S^2\to\mathbb{RP}^2`, by contrast,
`\mathbb{RP}^2` is non-orientable and no such top-form integral exists.)
