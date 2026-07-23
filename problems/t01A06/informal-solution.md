<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t01A06: A torus flux integral as enclosed volume, and why ambient closed 1-forms have no periods

## Why It's Hard

Part (a) bundles a genuine computation inside a distraction. The `2`-form `\omega = x\,dy\wedge dz - d(yx\,dz)`
contains an **exact** summand `d(yx\,dz)`, and the temptation is to expand it and grind through a surface
parametrization of the torus. The clean route recognizes that the exact piece *integrates to zero over a
closed surface* (Stokes), and that the remaining `\int_T x\,dy\wedge dz` is, by the divergence theorem, the
**volume enclosed** by `T` — turning an awkward surface integral into a volume one had better know how to
compute (Pappus).

Part (b) is a trap baited by topology. The torus `T` has nontrivial first cohomology (`H^1(T) = \mathbb R^2`),
so it *does* carry closed `1`-forms with nonzero periods, and one is tempted to write down `d\theta`. But the
form `\eta` is required to live on the **ambient** `\mathbf A^3 = \mathbb R^3`, which is contractible — and on
a contractible space every closed `1`-form is *exact*. Recognizing that the ambient simple-connectivity, not
the torus's own topology, controls the answer is the whole point: the obstruction one would need (a
closed-but-not-exact form on `\mathbb R^3`) does not exist.

## The Key Insight

**(a)** Over the closed surface `T = \partial V` (`V` the solid torus it bounds):

- the exact part vanishes: `\int_T d(yx\,dz) = \int_{\partial T}(yx\,dz) = 0` since `\partial T = \varnothing`;
- the rest is the enclosed volume: `\int_T x\,dy\wedge dz = \int_V d(x\,dy\wedge dz) = \int_V dx\wedge dy\wedge dz = \operatorname{Vol}(V)`.

So `\int_T \omega = \operatorname{Vol}(V) = 2\pi^2 R r^2` (Pappus: `\pi r^2 \cdot 2\pi R`).

**(b)** No such `\eta, \gamma` exist. `\mathbb R^3` is contractible, so `H^1_{\mathrm{dR}}(\mathbb R^3) = 0`:
every closed `1`-form on `\mathbb R^3` is `\eta = dg`. Then for any loop `\gamma : S^1 \to T \subset \mathbb R^3`,

$$\int_{S^1} \gamma^*\eta = \int_{S^1} \gamma^*(dg) = \int_{S^1} d(g\circ\gamma) = 0,$$

since `g\circ\gamma` is a function on the closed curve `S^1`. Every period vanishes.

## Complete Proof

`\mathbf A^3 = \mathbb R^3` with coordinates `x, y, z`. The torus `T` (tube radius `r`, center-circle radius
`R`, `R > r > 0`) is the boundary, oriented outward, of the compact solid region `V` it encloses.

### (a) `\int_T \omega`

Write `\omega = x\,dy\wedge dz - d(yx\,dz)`.

**The exact term drops out.** `T` is a closed surface (a compact `2`-manifold without boundary), so by
Stokes' theorem applied to the `1`-form `yx\,dz`,

$$\int_T d(yx\,dz) = \int_{\partial T} yx\,dz = 0 \qquad (\partial T = \varnothing).$$

**The remaining term is the enclosed volume.** Since `T = \partial V` with the boundary orientation, Stokes'
theorem (the divergence theorem) gives

$$\int_T x\,dy\wedge dz = \int_V d\big(x\,dy\wedge dz\big) = \int_V dx\wedge dy\wedge dz = \int_V dV = \operatorname{Vol}(V),$$

because `d(x\,dy\wedge dz) = dx\wedge dy\wedge dz` is the standard volume form. By Pappus's theorem, the solid
torus has volume (cross-sectional area `\pi r^2`) `\times` (distance `2\pi R` travelled by its centroid):

$$\operatorname{Vol}(V) = \pi r^2 \cdot 2\pi R = 2\pi^2 R r^2.$$

Therefore

$$\boxed{\ \int_T \omega = 2\pi^2 R r^2.\ }$$

### (b) Non-existence of a closed `\eta` on `\mathbb R^3` with a nonzero period on `T`

**Claim.** There is *no* closed `1`-form `\eta` on `\mathbb R^3` and smooth `\gamma : S^1 \to T` with
`\int_{S^1}\gamma^*\eta \ne 0`.

**Proof.** `\mathbb R^3` is contractible, so by the Poincaré lemma `H^1_{\mathrm{dR}}(\mathbb R^3) = 0`: every
**closed** `1`-form on `\mathbb R^3` is **exact**. Hence `\eta = dg` for some smooth `g : \mathbb R^3 \to \mathbb R`.
For any smooth `\gamma : S^1 \to T \subset \mathbb R^3`, pullback commutes with `d`, so
`\gamma^*\eta = \gamma^*(dg) = d(g \circ \gamma)`, and by Stokes on the closed curve `S^1` (or the fundamental
theorem of calculus around the loop),

$$\int_{S^1} \gamma^*\eta = \int_{S^1} d(g \circ \gamma) = 0.$$

So **every** period vanishes; no pair `(\eta, \gamma)` with nonzero integral can exist. ∎

**Remark.** Part (b) is exactly a test of *where* the form lives. The torus itself has `H^1(T) = \mathbb R^2 \ne 0`,
so on `T` there are closed non-exact `1`-forms with nonzero periods — e.g. the angle forms `d\theta_1, d\theta_2`,
and `\int_{S^1}\gamma^* d\theta_i = 2\pi` for a generating loop `\gamma`. But such forms do **not** extend to
closed `1`-forms on the ambient `\mathbb R^3`; the requirement that `\eta` be closed on all of contractible
`\mathbb R^3` forces it exact and annihilates every period. The ambient simple-connectivity overrides the
torus's own topology. (Compare part (a): there the exact ambiguity `d(yx\,dz)` was likewise invisible —
exact forms integrate to zero over closed cycles, whether `1`-cycles in (b) or the `2`-cycle `T` in (a).)
