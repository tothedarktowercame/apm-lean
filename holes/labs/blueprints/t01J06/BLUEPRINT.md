# t01J06 repair and blueprint

## Triage: unfaithful

The registered statement does not encode the word “closed” in part (c).
Its old conclusion asks for a pointwise family `zeta` equal to
`apm_t01J06_projectionPullback alpha`; `Refute.lean` proves this conclusion
for every `alpha` and `p` by `rfl`, without smoothness or closedness.  This is
exactly the defect identified by `holes/labs/statement-registry/triage-1.md`.

`RevisedMain.lean` makes the smallest semantic repair: part (c) now says that
there is an ambient two-form `Z` on an open neighbourhood `W` of the embedded
`S² × S¹`, smooth on `W`, with `extDeriv Z = 0` on `W`, whose tangent
restriction pulls back along `j(q)=(q,p)` to `alpha`.  Parts (a) and (b) are
unchanged.  The neighbourhood formulation is the registry grader's suggested
way to express a smooth closed manifold form using Mathlib's available
ambient differential-form API.

The grader's counterexample no longer applies: the canonical pointwise
projection family alone supplies none of `W`, `Z`, smoothness, or closedness.
The repair is true.  On `(E3 \ {0}) × E2`, radially retract the first factor
to `S²`, pull back `alpha`, and then restrict to `S² × S¹`.  On the sphere the
radial map has identity derivative on tangent vectors, so the `j`-pullback is
`alpha`; pullback preserves closedness.

## Lemmas

### `apm_t01J06_orientedCoefficient_eq`

Statement: for the specified `omega` and its restriction `alpha`, the custom
outward-oriented coefficient is `(z+3)z` at every point of the unit sphere.

Sketch: substitute `halpha` and `homega`; expand orthogonal projection onto
`span(q)⊥` as `e_i - ⟪q,e_i⟫q`; use `‖q‖=1`, alternating bilinearity, and ring
normalization.  This is local coordinate algebra, estimated 50–120 lines.

Dependencies: none.  Check: at the north and south poles the formula gives
`4` and `2`, respectively, agreeing with direct evaluation on the outward
oriented tangent basis; at the equator it gives zero.

### `apm_t01J06_sphere_moments` — LIBRARY

Statement: the coordinate and coordinate-square functions are integrable for
the intrinsic `μH[2]`, their integrals are `0` and `4π/3` respectively.

Sketch: oddness under coordinate reflection gives the first moment.  Import
`ConstructionTargets.IntrinsicSphereSecondMoments`: its sorry-free
`square_moment` reduces the square moment to one third of sphere mass.  The
remaining missing shared result is the Euclidean Hausdorff normalization
`unitSphere_euclideanHausdorff_mass_two`, already registered by the topology
loop for t01J06/t02A05.  Estimated 100–180 consumer lines after that program.

Dependencies: none at the blueprint interface.  Check: symmetry forces all
three square moments equal and their pointwise sum is `1`, so each is one
third of area; normalized unit-sphere area is `4π`.

### `apm_t01J06_closed_extension_integral_zero` — LIBRARY

Statement: a globally smooth closed ambient 2-form on `E3` has zero custom
sphere integral when `alpha` is its restriction.

Sketch: specialized Stokes on the unit ball, or Poincaré lemma on contractible
`E3` followed by integration of an exact form over the closed sphere.  Mathlib
currently has `extDeriv_pullback` but no global manifold-form integration/
Stokes theorem connecting it to this frozen Hausdorff coefficient integral;
the solve loop explicitly stopped at this boundary.  This is a genuine
300+-line library foundation, not a small consumer lemma.

Dependencies: none at the blueprint interface.  Check: constant closed
2-forms have opposite/cancelling flux through antipodal patches; exactness on
`R³` gives the general hand proof.  No degenerate zero-radius sphere occurs
because the radius is fixed at `1`.

### `apm_t01J06_exists_closed_product_extension` — LIBRARY

Statement: for every `p`, the repaired closed product extension exists.

Sketch: let `W=(E3\{0})×E2`, let `r(x,y)=x/‖x‖`, and take the ambient
pullback along `r` of the sphere restriction.  Prove smoothness of radial
normalization off zero, closedness via `extDeriv_pullback` (equivalently, the
rank-two target makes the exterior derivative vanish), and the tangent
identity at unit vectors.  Estimated 180–300 lines; it is marked LIBRARY
because it develops the missing ambient representative rather than merely
assembling the frozen theorem.  The closest sorry-free reusable development
is `ConstructionTargets/t94A10Closure.lean`, especially its radial calculus
and `solidAngleAmbient_closed`, though this lemma needs the `(z+3)dx∧dy`
restriction rather than that file's solid-angle form.

Dependencies: none at the blueprint interface.  Check: `W` contains every
product point since a unit sphere point is nonzero.  For tangent `v` at unit
`q`, `D(x/‖x‖)_q(v)=v`, so the repaired pullback condition is exactly the
given `halpha`.  The construction works for every `p`, including both poles
of the circle.

## Dependency layers

- Layer 1 (parallel): `orientedCoefficient_eq`, `sphere_moments`,
  `closed_extension_integral_zero`, `exists_closed_product_extension`.
- Layer 2: the sorry-free proof of `apm_t01j06` already in `Blueprint.lean`.

No lemma is given another lemma's conclusion as hidden core content.  The
four interfaces are independent; the final theorem is the only join point.

## Verification

Compiled individually with `systemd-run --user --scope -q -p MemoryMax=12G
lake env lean`:

- `RevisedMain.lean`: compiles (only its intended theorem `sorry`).
- `Refute.lean`: compiles without `sorry`.
- `Blueprint.lean`: compiles; its main theorem has no `sorry` and reaches
  `sorryAx` only through the four named lemmas.

Output of `#print axioms apm_t01j06`:

```text
'apm_t01j06' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

## Statement repair and re-split (claude-14, 2026-11-01)

**The registered statement is false as written.** `apm_t01J06_sphereIntegral` integrates against Mathlib's
raw `μH[2]`, which has no normalising constant. On Euclidean space it is `4/π` times area (isodiametric
inequality), so the raw integral is `(4/π)(4π/3) = 16/3`, not `4π/3`. t02A05 hit the same point and uses
`μHE[2]`. The repair is that one token in `apm_t01J06_sphereIntegral` and in `apm_t01J06_sphere_moments`.
It does not narrow anything: `μHE[2]` is surface area, which is what the printed integral means. The
repaired statement needs re-admission to the registry by an outside grader before landing.

The mass `μHE[2](S²) = 4π` is in the new `ConstructionTargets/EuclideanHausdorffSphereMass.lean`, moved
unchanged from t02A05. The earlier note that the normalisation was missing is superseded.

Stokes route, avoiding integration theory on manifolds: restricted form to flux (`_orientedCoefficient_flux`),
closed means divergence-free (`_closed_divergence_free`), divergence-free means curl (`_divergenceFree_isCurl`,
cone formula), and the flux of a curl is a sum of rotation derivatives, each zero because `μHE[2]` is rotation
invariant (`_rotation_derivative_integral`, `_curl_flux_zero`). Only `_curl_flux_zero` needs another leaf
(rotation), and `_closed_extension_integral_zero` needs the rest.

Checks: `rotField` is `e k × q` in all three axes, and `q · curl A = ∑ k, ∇(A k) · (e k × q)` by hand.
`F 1 = -eta(e 0, e 2)` matches the sign in `extDeriv_apply`. Flux at `omega`: `F 2 = z + 3`, so the coefficient
is `(z + 3) z`, agreeing with `_orientedCoefficient_eq`.

