<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t91A05: No smooth retraction of the disk onto its boundary circle

## Why It's Hard

The claim is a non-existence statement — no smooth `g : B^2 \to \partial B^2` restricts to the identity on
the boundary — and one cannot rule out every conceivable map by hand. The difficulty is to find an
*invariant* that such a retraction would have to respect and then derive a contradiction. The retraction
would, in effect, let you detect the nontrivial loop `\partial B^2 = S^1` from inside the *contractible* disk
`B^2` — which is impossible, but "impossible" must be made precise.

The clean smooth route packages this as a **period obstruction**: the circle carries a closed `1`-form with
nonzero integral (the angle form `d\theta`, `\int_{S^1} d\theta = 2\pi`), representing the nontrivial class
in `H^1_{\mathrm{dR}}(S^1)`. Pulling it back by `g` and applying Stokes turns the boundary integral into a
volume integral of its exterior derivative — which vanishes, because the disk is contractible and the
pulled-back form is closed. Meanwhile the retraction condition forces the boundary integral to be `2\pi`.
The whole proof is recognizing that the disk cannot support the circle's nonzero period.

## The Key Insight

Let `\omega = d\theta` be the angle `1`-form on `S^1 = \partial B^2`, which is **closed** and has
`\int_{S^1}\omega = 2\pi \ne 0`. If `g : B^2 \to S^1` is a smooth retraction (`g|_{\partial B^2} = \mathrm{id}`):

- `g^*\omega` is closed on `B^2`, since `d(g^*\omega) = g^*(d\omega) = g^*(0) = 0` (`d\omega = 0` because
  `\omega` is a `1`-form on the `1`-manifold `S^1`, so its exterior derivative is a `2`-form on `S^1`, hence `0`).
- By **Stokes**, `\displaystyle\int_{\partial B^2} g^*\omega = \int_{B^2} d(g^*\omega) = 0`.
- But `g|_{\partial B^2} = \mathrm{id}`, so on the boundary `g^*\omega` restricts to `\omega`, giving
  `\displaystyle\int_{\partial B^2} g^*\omega = \int_{S^1}\omega = 2\pi`.

Thus `2\pi = 0`, a contradiction — no such `g` exists.

## Complete Proof

Suppose, for contradiction, that there is a smooth map `g : B^2 \to \partial B^2 = S^1` with
`g|_{\partial B^2} = \mathrm{id}_{\partial B^2}`.

**Step 1 — A closed `1`-form with nonzero period on `S^1`.** Let `\omega = d\theta` be the standard angle
`1`-form on `S^1` (in coordinates `(\cos\theta, \sin\theta)`, `\omega = -y\,dx + x\,dy` restricted to `S^1`).
It is a smooth `1`-form with

$$\int_{S^1}\omega = 2\pi.$$

It is closed: `\omega` is a `1`-form on the `1`-dimensional manifold `S^1`, so `d\omega` is a `2`-form on
`S^1`, and every `2`-form on a `1`-manifold is zero; hence `d\omega = 0`.

**Step 2 — The pullback `g^*\omega` is closed on `B^2`.** Pullback commutes with the exterior derivative, so

$$d(g^*\omega) = g^*(d\omega) = g^*(0) = 0.$$

Thus `g^*\omega` is a closed smooth `1`-form on the disk `B^2`.

**Step 3 — Stokes makes the boundary integral vanish.** `B^2` is a compact oriented `2`-manifold with
boundary `\partial B^2`, so Stokes' theorem gives

$$\int_{\partial B^2} g^*\omega = \int_{B^2} d(g^*\omega) = \int_{B^2} 0 = 0. \tag{1}$$

**Step 4 — The retraction condition makes it `2\pi`.** Let `i : \partial B^2 \hookrightarrow B^2` be the
inclusion. Pullback is functorial, and `g \circ i = g|_{\partial B^2} = \mathrm{id}_{\partial B^2}`, so

$$\int_{\partial B^2} g^*\omega = \int_{\partial B^2} i^*(g^*\omega) = \int_{\partial B^2} (g\circ i)^*\omega
= \int_{\partial B^2} \mathrm{id}^*\omega = \int_{S^1}\omega = 2\pi. \tag{2}$$

**Step 5 — Contradiction.** Comparing (1) and (2), `0 = 2\pi`, which is absurd. Therefore no smooth map
`g : B^2 \to \partial B^2` with `g|_{\partial B^2} = \mathrm{id}` exists.

$$\boxed{\ \text{There is no smooth retraction } B^2 \to \partial B^2.\ }\qquad\blacksquare$$

**Remark.** The obstruction is a *period*: the circle's class `[d\theta] \ne 0` in `H^1_{\mathrm{dR}}(S^1) \cong \mathbb R`,
which the contractible disk (`H^1_{\mathrm{dR}}(B^2) = 0`) cannot accommodate. A retraction would pull the
nonzero period back to a closed form on `B^2`, but on the disk every closed `1`-form is exact and integrates
to zero around the boundary. The same proof in the topological/PL category replaces de Rham cohomology by
the fundamental group: `r \circ j = \mathrm{id}` on `\partial B^2` would give `r_* \circ j_* = \mathrm{id}` on
`\pi_1(S^1) = \mathbb Z`, but `j_*` factors through `\pi_1(B^2) = 0`, forcing `\mathrm{id}_{\mathbb Z} = 0` —
the same contradiction, with "nonzero period" replaced by "nontrivial loop." This `2`-dimensional No
Retraction theorem is equivalent to the Brouwer fixed-point theorem for `B^2`.
