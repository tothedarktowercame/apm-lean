# Blueprint: close t96A07 by explicit derivative calculations

Audit: `~/notes/closer/audits/t96A07.md`, steps
`t96A07_descendedSphereMap`, `t96A07_not_transverse_axis`,
`t96A07_horizontal_levels_regular`, and final assembly.

This blueprint builds on
`RealProjectiveSmoothTarget.rpSmoothAtlas`,
`sphereProjectionEvenMapSmoothDescent`, and the stored local-diffeomorphism
field of `SmoothAtlas`.  It uses the frozen definitions `T96A07.sphereMap`,
`axis`, `plane`, and `Transverse` without changing them.

### B1. Antipodal invariance of the quadratic sphere map

lean: `ConstructionTargets.T96A07Closure.sphereMap_antipodal` :
`∀ p : Sphere 2, T96A07.sphereMap (sphereAntipodalN 2 p) = T96A07.sphereMap p`

uses: frozen coordinate definitions

status: planned

Expand `sphereMap`, `sphereAntipodalN`, and the three `Fin 3` coordinates.
Each coordinate is a product of two negated entries, so `(-x)*(-y)=x*y`.

### B2. Smoothness of the quadratic sphere map

lean: `ConstructionTargets.T96A07Closure.sphereMap_contMDiff` :
`ContMDiff (𝓡 2) (𝓡 3) ∞ T96A07.sphereMap`

uses: Mathlib smoothness of coordinate projections, multiplication, and
restriction to `Sphere 2`

status: planned

View the map as the restriction of the polynomial map
`(x₀,x₁,x₂) ↦ (x₁*x₂,x₀*x₂,x₀*x₁)` and prove smoothness coordinatewise.

### B3. Descend the sphere map to the frozen RP² atlas

lean: `ConstructionTargets.T96A07Closure.descendedSphereMap` : with
`rpSmoothAtlas.charts` and `.smooth`, an `f : Space ℝ 2 → E 3` satisfying
the projection equation and `ContMDiff (𝓡 2) (𝓡 3) ∞ f`

uses: B1, B2,
`RealProjectiveSmoothTarget.sphereProjectionEvenMapSmoothDescent`

status: planned

Apply smooth even descent with `m=3` and retain its witness and both fields.

### B4. Ambient derivative formula for the quadratic map

lean: `ConstructionTargets.T96A07Closure.sphereMapAmbient_fderiv` : the
Fréchet derivative at `p` sends `v` to
`![v 1*p 2+p 1*v 2, v 0*p 2+p 0*v 2, v 0*p 1+p 0*v 1]`

uses: polynomial derivative rules

status: planned

Differentiate each coordinate product and identify the resulting continuous
linear map by extensionality on `Fin 3`.

### B5. Sphere derivative at the first coordinate point

lean: `ConstructionTargets.T96A07Closure.sphereMap_mfderiv_e0_range` : the
range of `mfderiv ... T96A07.sphereMap e0` is the `yz` coordinate plane

uses: B4, the sphere tangent chart at `e0 = ![1,0,0]`

status: planned

Here `e0` is the explicit sphere point `![1,0,0]`.  The tangent constraint
gives `v₀=0`; B4 then gives derivative `(0,v₂,v₁)`, and the chosen sphere
chart expresses the two free tangent coordinates.  Prove both range
inclusions to obtain equality with the `yz` plane.

### B6. Transfer the derivative through smooth descent

lean: `ConstructionTargets.T96A07Closure.descended_mfderiv_range_at_e0` : for
the B3 witness, the derivative range at `sphereProjection 2 e0` equals the
B5 range

uses: B3, B5, `rpSmoothAtlas.quotient_localDiffeomorph e0`, chain rule

status: planned

Differentiate the B3 projection equation locally.  The projection derivative
is an isomorphism because the stored branch is a local diffeomorphism, so
composition with it does not change the image subspace.

### B7. Failure of transversality to the z-axis

lean: `ConstructionTargets.T96A07Closure.descended_not_transverse_axis` :
`¬ T96A07.Transverse f T96A07.axis` for the B3 witness

uses: B6

status: planned

Use the incident pair `sphereProjection 2 e0, 0`.  The descended value and
axis value are zero.  The axis derivative has z-axis range, already contained
in the B6 `yz` plane; their supremum misses the x-coordinate, hence is not top.

### B8. Derivative of a horizontal-plane parametrization

lean: `ConstructionTargets.T96A07Closure.plane_fderiv_range` :
`LinearMap.range (fderiv ℝ (T96A07.plane z) q).toLinearMap` is the horizontal
coordinate plane

uses: frozen `plane`

status: planned

Differentiate the affine inclusion `(u,v) ↦ (u,v,z)` and characterize its
range by vanishing third coordinate.

### B9. Vertical component of the sphere derivative

lean: `ConstructionTargets.T96A07Closure.sphereMap_vertical_surjective` : if
`sphereMap p = plane z q`, `0 < z`, and `z < 1/2`, then the third-coordinate functional
on the range of `mfderiv ... sphereMap p` is surjective

uses: B4

status: planned

Incidence gives `p₀*p₁=z`, hence both factors are nonzero.  The strict upper
bound excludes the sole constrained critical level `1/2`.  Solve the tangent
constraint together with `p₁*v₀+p₀*v₁=1`, splitting on `p₂=0`; in that case
`p₀² ≠ p₁²`, while for `p₂ ≠ 0` the third tangent coordinate absorbs the
sphere constraint.

### B10. Horizontal-level transversality

lean: `ConstructionTargets.T96A07Closure.sphereMap_transverse_plane` :
`0 < z → z < 1/2 → T96A07.Transverse T96A07.sphereMap (T96A07.plane z)`

uses: B8, B9

status: planned

At an incident pair, B8 supplies every horizontal vector and B9 supplies a
range vector with vertical coordinate one.  Decompose an arbitrary target
vector into those parts to prove the supremum of ranges is top.

### B11. Attainment of every level between zero and one half

lean: `ConstructionTargets.T96A07Closure.sphereMap_level_attained` :
`0 < z → z < 1/2 → ∃ p : Sphere 2, T96A07.sphereMap p 2 = z`

uses: real square-root identities

status: planned

Take ambient coordinates `(sqrt z, sqrt z, sqrt (1-2*z))`.  The inequalities
make the radicals valid, their squared norm is one, and the third output
coordinate is `sqrt z * sqrt z = z`.

### B12. Infinitely many transverse attained levels

lean: `ConstructionTargets.T96A07Closure.horizontal_levels_infinite` :
the frozen set of transverse, attained horizontal levels is infinite

uses: B10, B11

status: planned

Show the infinite interval `Set.Ioo 0 (1/2)` is contained in the frozen set,
then apply `Set.Infinite.mono`.

### B13. Frozen theorem adapter

lean: proof of `apm_t96a07`

uses: B3, B7, B12

status: planned

Choose `rpSmoothAtlas`, install its two instances, choose the B3 descended
map, and return its projection equation, smoothness, B7, and B12 in the
frozen conjunction order.

Formalization order: B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12,
B13.
