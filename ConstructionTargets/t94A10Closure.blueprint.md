# Blueprint: close t94A10 by radial calculus and a periodic Stokes square

Audit: `~/notes/closer/t94a10-report.md`, covering
`apm_t94A10_bridge_solidAngle_closed` and
`apm_t94A10_bridge_solidAngle_not_exact`.  Route: `t94A10` in
`holes/labs/topology-routes/routes-2.md` (`periodic-stokes-square`).

The formalisation uses Mathlib's `extDeriv_apply`, `extDeriv_pullback`,
`Filter.EventuallyEq.extDeriv_eq`,
`MeasureTheory.integral2_divergence_prod_of_hasFDerivWithinAt_off_countable`,
and one-variable trigonometric integral lemmas.  The ambient representation is
`EuclideanSpace ℝ (Fin 3)`; forms are bundled continuous alternating maps, as
in the frozen file.  Parameter rectangles use ordinary `ℝ × ℝ` coordinates,
with latitude first and longitude second.  No manifold integration is used.

### B1. The determinant form and radial scalar

lean: `ConstructionTargets.T94A10Closure.solidAngleAmbient` : an explicit
ambient two-form `E3 → E3 [⋀^Fin 2]→L[ℝ] ℝ` whose value at nonzero `x` is
`det(x,v₀,v₁) / ‖x‖^3`

uses: `Matrix.detRowAlternating`, coordinate projections, norm calculus

status: planned

Bundle the numerator as the three-dimensional determinant with first row
`x`.  Define the scalar coefficient to be `‖x‖⁻³` away from zero (its value at
zero is irrelevant).  Prove the coordinate expansion and equality with the
frozen square-root denominator using `EuclideanSpace.real_norm_sq_eq`.

### B2. Derivative identities away from zero

lean: `ConstructionTargets.T94A10Closure.hasFDerivAt_radialInvCube` : for
`x ≠ 0`, the derivative of `x ↦ ‖x‖⁻³` sends `u` to
`-3 * ‖x‖⁻⁵ * inner x u`

uses: Mathlib derivatives of norm-square, `Real.sqrt`, inverse, and powers

status: planned

Work locally where the squared norm is positive.  Differentiate the
coordinate norm-square, square root, cube and inverse in that order.  Record
nonzero denominators explicitly; normalize the resulting scalar identity by
`field_simp` and `ring`.

### B3. The ambient solid-angle form is closed off the origin

lean: `ConstructionTargets.T94A10Closure.solidAngleAmbient_closed` : for
`x ≠ 0`, `DifferentiableAt ℝ solidAngleAmbient x` and
`extDeriv solidAngleAmbient x = 0`

uses: B1, B2, Mathlib `extDeriv_apply`

status: planned

Apply `extDeriv_apply` to three tangent vectors.  The derivative of the
determinant-linear numerator contributes `3 * ‖x‖⁻³ * det(u,v,w)`.  The three
coefficient-derivative terms reduce, by the three-dimensional Laplace
identity, to `Df(x) * det(u,v,w)`; B2 gives
`Df(x) = -3 * ‖x‖⁻³`.  Prove the coordinate identity by `fin_cases`, clear the
nonzero denominator, and `ring`.

### B4. Frozen closedness adapter

lean: `ConstructionTargets.T94A10Closure.bridge_solidAngle_closed` : the
exact type of `apm_t94A10_bridge_solidAngle_closed`

uses: B1, B3, frozen `apm_t94a10_ambientExtension_apply_of_isOmega`

status: planned

At each punctured point, show the arbitrary extension is eventually equal to
B1 on a ball avoiding zero.  Transfer differentiability and `extDeriv` by
locality, then apply B3.  This supplies both conjuncts of frozen `IsClosed`.

### B5. Spherical rectangle and its derivatives

lean: `ConstructionTargets.T94A10Closure.sphereParam` : the map
`Φ(s,t) = (sin s*cos t, sin s*sin t, cos s)` together with its two partial
derivatives, periodicity in `t`, unit norm, and nonvanishing

uses: elementary trigonometric identities and smoothness

status: planned

State the identities on all of `ℝ × ℝ`.  The norm certificate makes every
image point punctured.  Also record that the longitude derivative vanishes
at `s=0,π`; these are the polar-edge cancellations used by B8.

### B6. Pullback coefficient of the solid-angle form

lean: `ConstructionTargets.T94A10Closure.solidAngle_pullback_sphereParam` :
for a form satisfying the frozen solid-angle formula,
`omega (Φ(s,t)) (![∂s Φ, ∂t Φ]) = sin s`

uses: B1, B5

status: planned

Substitute the two derivatives into the determinant numerator.  Use unit norm
to replace the denominator by one, expand the three coordinates, and finish
with `ring_nf` plus `sin_sq_add_cos_sq`.

### B7. Pullback of an exact form is an exact parameter-plane form

lean: `ConstructionTargets.T94A10Closure.exact_sphereParam_identity` : from
`extDeriv etaAmbient = omega` on punctured space, obtain on the rectangle the
two-variable curl identity whose left side is `sin s`

uses: B5, B6, Mathlib `extDeriv_pullback`

status: planned

Pull back the ambient one-form along `Φ`.  Smoothness of B5 and the frozen
differentiability hypothesis discharge the chain-rule assumptions.  Evaluate
`extDeriv_pullback` on the standard ordered basis `(e_s,e_t)`; orientation is
latitude then longitude, matching the positive `sin s` in B6.

### B8. Periodic-square Green cancellation

lean: `ConstructionTargets.T94A10Closure.sphericalRectangle_curl_integral_zero` :
the double integral of the B7 curl over `[0,π] × [0,2π]` is zero

uses: B5, B7,
`MeasureTheory.integral2_divergence_prod_of_hasFDerivWithinAt_off_countable`

status: planned

Apply the rectangle Green theorem to the two pulled-back coefficient
functions.  Longitude-edge terms cancel using `Φ(s,t+2π)=Φ(s,t)` and equality
of its derivatives.  Latitude-edge terms vanish because `∂t Φ=0` at both
poles.  Supply differentiability, integrability, and the empty (hence
countable) exceptional set explicitly.

### B9. The spherical coefficient has nonzero integral

lean: `ConstructionTargets.T94A10Closure.integral_sin_rectangle` :
`∫ s in 0..π, ∫ t in 0..2*π, sin s = 4*π`

uses: `intervalIntegral.integral_sin`, integral of a constant, `Real.pi_pos`

status: planned

Evaluate the longitude integral first, then the latitude integral.  Normalize
the endpoints and prove `4*π ≠ 0` from positivity of π.

### B10. Frozen non-exactness adapter

lean: `ConstructionTargets.T94A10Closure.bridge_solidAngle_not_exact` : the
exact type of `apm_t94A10_bridge_solidAngle_not_exact`

uses: B6, B7, B8, B9

status: planned

Assume a frozen primitive.  B7 identifies the pulled-back curl with `sin s`;
B8 makes its rectangle integral zero, while B9 makes it `4π ≠ 0`.  Contradict
these equalities and discharge the frozen negated existential.

### B11. Frozen theorem assembly

lean: proof of `apm_t94a10`

uses: B4, B10

status: planned

Apply the two bridge adapters to the supplied `omega` and `homega`, returning
the conjunction in the registered theorem's existing order.

Formalisation order: B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11.  B1--B4
and B5--B9 may advance independently; B10 joins the second branch and B11 is
the final adapter.
