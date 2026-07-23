<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t01J06: A 2-form on S², its nonzero period, and when it extends to a closed form

## Why It's Hard

The three parts are a single story about **one cohomology class**, `[i^*\omega] \in H^2_{dR}(S^2) \cong
\mathbb R`, told through its period `\int_{S^2} i^*\omega`. The difficulty is recognizing that this number
controls everything downstream:

- **(a)** is a Stokes computation, but one must notice that `S^2` is a *closed* surface bounding the ball, so
  `\int_{S^2}\omega = \int_B d\omega` turns a surface integral into a trivial volume integral — and that the
  constant `3` contributes nothing (`d(3\,dx\wedge dy) = 0`).
- **(b)** asks for a *closed* extension to `\mathbb R^3`, and the trap is to think the obvious `\eta = \omega`
  works — it does satisfy `i^*\eta = i^*\omega`, but `\omega` is **not closed**. The real question is whether
  *any* closed form restricts correctly, and the obstruction is cohomological: `H^2(\mathbb R^3) = 0` forces
  every closed 2-form on `\mathbb R^3` to be exact, hence to have period `0` over the closed surface `S^2` —
  but the period is `\tfrac{4\pi}{3} \ne 0`. Seeing that *the nonzero period is the obstruction* is the crux.
- **(c)** flips the outcome by changing the ambient space: `S^2 \times S^1` retracts onto `S^2` (the
  projection is a left inverse of `j`), so `H^2` is *big enough* to carry the class, and pulling `i^*\omega`
  back along the projection works. The contrast between (b) and (c) is the whole point: extension is possible
  iff the target's `H^2` can receive the nonzero class.

## The Key Insight

Integration over the closed surface `S^2` reads off the de Rham class `[i^*\omega] \in H^2(S^2)\cong\mathbb R`,
and `\int_{S^2} i^*\omega = \tfrac{4\pi}{3} \ne 0`, so `[i^*\omega] \ne 0`.

- **(a)** Stokes: `\int_{S^2}\omega = \int_B d\omega`, and `d\omega = dx\wedge dy\wedge dz`, so the integral
  is `\operatorname{vol}(B) = \tfrac{4\pi}{3}`.
- **(b)** A closed 2-form on the contractible `\mathbb R^3` is exact, hence has period `0` over the closed
  `S^2`; but any `\eta` with `i^*\eta = i^*\omega` would have period `\tfrac{4\pi}{3}\ne 0`. **No such closed
  `\eta` exists.**
- **(c)** The projection `\pi_1 : S^2\times S^1 \to S^2` satisfies `\pi_1\circ j = \mathrm{id}_{S^2}`, so
  `\zeta := \pi_1^*(i^*\omega)` is closed (pullback of a closed form) and `j^*\zeta = i^*\omega`. **It exists.**

## Complete Proof

Here `\omega = (z+3)\,dx\wedge dy` on `\mathbb R^3`, `S^2 = \{x^2+y^2+z^2=1\}` with the standard (outward-normal)
orientation as the boundary of the closed unit ball `B`, and `i : S^2 \hookrightarrow \mathbb R^3` the
inclusion. Write `i^*\omega` for the restriction (we abbreviate `\int_{S^2}\omega := \int_{S^2} i^*\omega`).

### (a) `\int_{S^2}\omega = \tfrac{4\pi}{3}`

Compute the exterior derivative:
$$
d\omega = d\big[(z+3)\,dx\wedge dy\big] = \frac{\partial (z+3)}{\partial z}\, dz\wedge dx\wedge dy = dz\wedge dx\wedge dy = dx\wedge dy\wedge dz,
$$
the standard volume form (the constant `3` differentiates to `0`; `dz\wedge dx\wedge dy = dx\wedge dy\wedge dz`
by two transpositions). Since `S^2 = \partial B` with the boundary orientation, **Stokes' theorem** gives
$$
\int_{S^2}\omega = \int_{\partial B}\omega = \int_B d\omega = \int_B dx\wedge dy\wedge dz = \operatorname{vol}(B) = \frac{4}{3}\pi .
$$
$$
\boxed{\ \int_{S^2}\omega = \tfrac{4\pi}{3}.\ }
$$

### (b) `i^*\omega` is closed; no closed `\eta` on `\mathbb R^3` restricts to it

**`i^*\omega` is closed.** `i^*\omega` is a `2`-form on the `2`-manifold `S^2`. Its differential `d(i^*\omega)`
is a `3`-form on `S^2`, but `\Lambda^3(T_q^*S^2) = 0` since `\dim S^2 = 2` — every `3`-form on a `2`-manifold
is identically zero. Hence `d(i^*\omega) = 0`: `i^*\omega` is closed. (Equivalently, `d\,i^*\omega = i^*d\omega`
is the pullback of a `3`-form to a `2`-manifold, hence `0`.)

**No closed extension exists.** Suppose, for contradiction, that `\eta` is a **closed** `2`-form on `\mathbb
R^3` with `i^*\eta = i^*\omega`. Because `\mathbb R^3` is contractible, `H^2_{dR}(\mathbb R^3) = 0`, so every
closed `2`-form on `\mathbb R^3` is **exact**: `\eta = d\beta` for some `1`-form `\beta`. Then, since `S^2` is
a closed surface (`\partial S^2 = \varnothing`), Stokes gives
$$
\int_{S^2} i^*\eta = \int_{S^2} \eta = \int_{S^2} d\beta = \int_{\partial S^2}\beta = 0 .
$$
But the integral depends only on the restriction `i^*\eta = i^*\omega`, so
$$
0 = \int_{S^2} i^*\eta = \int_{S^2} i^*\omega = \frac{4\pi}{3} \ne 0,
$$
a contradiction. Therefore **no closed `2`-form `\eta` on `\mathbb R^3` satisfies `i^*\eta = i^*\omega`.** ∎

*(Note the naïve choice `\eta = \omega` fails not because `i^*\omega \ne i^*\omega` but because `\omega` is
not closed: `d\omega = dx\wedge dy\wedge dz \ne 0`.)*

### (c) A closed `\zeta` on `S^2 \times S^1` with `j^*\zeta = i^*\omega` exists

Let `\pi_1 : S^2 \times S^1 \to S^2` be the projection onto the first factor, and recall `j : S^2 \to S^2
\times S^1`, `j(q) = (q,p)`. These satisfy
$$
\pi_1 \circ j = \mathrm{id}_{S^2}, \qquad \text{since } \pi_1(j(q)) = \pi_1(q,p) = q .
$$
Define
$$
\boxed{\ \zeta := \pi_1^*\big(i^*\omega\big) \ } \qquad\text{a 2-form on } S^2 \times S^1 .
$$

**`\zeta` is closed.** Pullback commutes with `d`, and `i^*\omega` is closed by part (b), so
$$
d\zeta = d\,\pi_1^*(i^*\omega) = \pi_1^*\big(d(i^*\omega)\big) = \pi_1^*(0) = 0 .
$$

**`\zeta` restricts correctly.** Using functoriality of pullback and `\pi_1\circ j = \mathrm{id}`,
$$
j^*\zeta = j^*\pi_1^*(i^*\omega) = (\pi_1 \circ j)^*(i^*\omega) = \mathrm{id}_{S^2}^*(i^*\omega) = i^*\omega .
$$

Thus `\zeta = \pi_1^*(i^*\omega)` is a closed `2`-form on `S^2\times S^1` with `j^*\zeta = i^*\omega`, as
required. ∎

**Remark.** The trichotomy is governed by where the nonzero class `[i^*\omega] \in H^2(S^2)\cong\mathbb R`
(period `\tfrac{4\pi}{3}`) can live. A map `g : S^2 \to M` admits a closed `\eta` on `M` with `g^*\eta =
i^*\omega` iff `[i^*\omega]` lies in the image of `g^* : H^2(M)\to H^2(S^2)`. For `g = i : S^2 \to \mathbb
R^3`, `H^2(\mathbb R^3) = 0`, so the image is `0` and the nonzero class cannot be hit — part (b). For `g = j
: S^2 \to S^2\times S^1`, the existence of the retraction `\pi_1` (with `\pi_1\circ j = \mathrm{id}`) forces
`j^*` to be **surjective** on cohomology (it has the right inverse `\pi_1^*`), so *every* class on `S^2`,
including `[i^*\omega]`, is hit — part (c). The whole problem is the statement that integration over a closed
surface is a cohomological invariant, and that a nonzero period obstructs extension to any space with
vanishing `H^2`.
