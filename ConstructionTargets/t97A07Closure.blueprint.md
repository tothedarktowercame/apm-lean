# Critical values of a compact smooth manifold map

This blueprint follows `~/notes/closer/audits/t97A07.md` and the t97A07 route
in `holes/labs/topology-routes/routes-3.md`.  It covers the five remaining
steps: stability of surjective linear maps, openness of regular points,
existence of a critical value in positive target dimension, local openness at
a regular point, and the connected-complement argument.  Its final node
supplies the sole placeholder in `problems/t97A07/lean/Main.lean`.  The shared
area is `regular-points-open`.

The construction builds on Mathlib
`ContinuousLinearMap.exists_right_inverse_of_surjective`, continuity of
continuous-linear-map composition, openness of the invertible continuous
linear maps, `contMDiffAt_iff`, `mfderiv_comp`,
`IsLocalMax.fderiv_eq_zero`, `IsCompact.exists_isMaxOn`,
`HasStrictFDerivAt.map_nhds_eq_of_surj`, and
`Set.Countable.isConnected_compl_of_one_lt_rank`.  Manifold calculations use
Mathlib's extended charts and tangent coordinate changes; no derivative with
varying source or target fibers is treated as a map into one fixed operator
space without first transporting it through these charts.

### B1. Openness of surjective finite-dimensional continuous linear maps

lean: `t97A07Closure.isOpen_setOf_surjective_clm` : for finite-dimensional
real normed spaces `E` and `F`,
`IsOpen {L : E →L[ℝ] F | Function.Surjective L}`.

uses: Mathlib `ContinuousLinearMap.exists_right_inverse_of_surjective`,
continuity of `ContinuousLinearMap.comp`, and openness of the units in the
Banach algebra `F →L[ℝ] F`

status: proved

Fix a surjective `L` and choose a continuous right inverse `R`, so
`L.comp R = id`.  The map `L' ↦ L'.comp R` is continuous.  The invertible
operators form an open neighbourhood of `id`, so its preimage is an open
neighbourhood of `L`.  If `L'.comp R` is invertible, then
`R ∘ (L'.comp R)⁻¹` is a right inverse of `L'`; hence every operator in
that neighbourhood is surjective.  The two inclusions in the neighbourhood
criterion prove openness.  Finite dimensionality of the target is used
exactly to obtain the continuous right inverse.

### B2. Fixed-chart continuity of the manifold derivative

lean: `t97A07Closure.continuousAt_coordinate_mfderiv` : under the manifold
hypotheses used by t97A07 and `hf : ContMDiff I I' ∞ f`, for every `x`, the
continuous-linear-map-valued derivative of
`extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm`, expressed in the fixed
model spaces, is continuous at `extChartAt I x x`; on the chart source it is
the coordinate transport of `mfderiv I I' f`.

uses: Mathlib `contMDiffAt_iff`, `ContDiff.continuous_fderiv`,
`mfderiv_comp`, and the derivative equivalences of `extChartAt`

status: proved

Compiled progress: `coordinate_fderivWithin_eq_inTangentCoordinates_mfderiv_self`
now identifies the fixed-coordinate derivative with the transported manifold
derivative at their common chart centre.  It remains to extend this equality
to a neighbourhood contained in the fixed source and target charts.

Use `hf.contMDiffAt` and unfold `contMDiffAt_iff` in the fixed source and
target charts at `x`.  The resulting representative is smooth and therefore
has continuous first derivative near the chart centre.  On a smaller chart
neighbourhood, the chain rule identifies that derivative with `mfderiv f y`
pre- and post-composed with the continuous linear equivalences supplied by
the source and target chart transitions.  Record both the continuity and this
equality explicitly; B3 uses the equality to preserve surjectivity rather than
comparing tangent maps whose fibers vary with `y`.

Compiled progress: `continuousWithinAt_coordinate_fderivWithin` extracts from
`hf.contMDiffAt` the continuity, within the model-with-corners range, of the
fixed-chart representative's `fderivWithin` at the chart centre.
`coordinate_fderivWithin_eq_mfderiv` identifies its value at that centre
exactly with `mfderiv`; this follows from Mathlib's definition after proving
manifold differentiability, and does not identify tangent fibers at distinct
points.  `inTangentCoordinates_mfderiv_eq_chart_factors` now gives the nearby
chart-transport equality explicitly: in the common source and target charts,
the coordinate form of `mfderiv f y` is the target chart derivative composed
with `mfderiv f y` and the inverse source chart derivative.  Remaining in B2
is to identify this transported map with the fixed representative's
`fderivWithin` on a common smaller chart neighbourhood.
`continuousAt_inTangentCoordinates_mfderiv` also records directly that this
transported derivative varies continuously at the base point, using Mathlib's
`ContMDiffAt.mfderiv_const`.  Thus B3 may use the transported formulation
without treating derivatives in distinct tangent fibers as one operator-valued
function; the fixed-representative equality remains to connect the two B2
formulations.
`eventually_mem_fixed_chart_sources` supplies one neighbourhood on which both
the source point and its image lie in the fixed source and target charts; on
this neighbourhood `inTangentCoordinates_mfderiv_eq_chart_factors` applies
uniformly.  The remaining equality proof can therefore work under these two
explicit membership hypotheses.
`eventually_inTangentCoordinates_mfderiv_eq_chart_factors` packages that
uniform application as one eventual equality, so the next step can compare
the fixed representative directly with this three-factor expression.
`inTangentCoordinates_mfderiv_self_eq_sourceChartFactor` evaluates the
transported family at its centre through the target-chart identity: the
remaining expression is `mfderiv f x` followed by the inverse source-chart
derivative.  Normalizing this last chart factor is now the exact centre-level
boundary before the smaller-neighbourhood equality.

`mfderiv_chartAt_symm_self_eq_id` normalizes that source-chart factor: for
the Euclidean model with corners, the inverse chart derivative at the chart
centre is the identity.
The corollary `inTangentCoordinates_mfderiv_self_eq_mfderiv` therefore
identifies the transported family with `mfderiv f x` at the centre.  The
remaining B2 step is the equality with the fixed-coordinate derivative on a
smaller chart neighbourhood.

`coordinate_fderivWithin_eq_chart_factors_self` identifies the fixed
coordinate derivative at the centre with the same explicit three-factor
formula used by the nearby transported family.  It remains to extend this
identification to a smaller common chart neighbourhood.

`exists_nhds_chart_factor_agreement` now chooses one neighbourhood on which
both fixed chart memberships and the transported three-factor formula hold,
and records the fixed-coordinate equality at its centre in the same packet.
The remaining B2 step is the pointwise identification of the fixed
representative derivative with that transported family throughout this
neighbourhood.

`continuousAt_inTangentCoordinates_mfderiv_and_self` packages the
coordinate-safe formulation needed for that comparison: the transported
family is continuous at `x` and its value at `x` is literally `mfderiv f x`.
The fixed representative has chart-coordinate domain, so the remaining
pointwise statement must precompose it with the fixed source chart rather
than identify functions with different domains.

`continuousAt_coordinate_fderivWithin_comp_extChartAt` performs that domain
bridge: the fixed representative's derivative, evaluated after the fixed
source chart, is continuous at `x`.  This uses the exact image-filter identity
for the extended chart, so the model-with-corners range restriction is
preserved.  It remains to prove that this precomposed family agrees pointwise
near `x` with the transported manifold derivative.

`coordinate_fderivWithin_comp_extChartAt_eq_inTangentCoordinates` proves that
pointwise agreement whenever the point and its image lie in the two fixed
chart sources.  Two applications of the manifold chain rule reduce the fixed
representative derivative to the target-chart derivative, `mfderiv f y`, and
the inverse source-chart derivative; the extended-chart inverse law supplies
the exact intermediate points.  The remaining B2 step is to package this
equality with `eventually_mem_fixed_chart_sources` and the two continuity
theorems into the declared `continuousAt_coordinate_mfderiv` interface.

`eventually_coordinate_fderivWithin_comp_extChartAt_eq_inTangentCoordinates`
packages the pointwise comparison on the common chart neighbourhood.
`continuousAt_coordinate_mfderiv` is the completed B2 interface: it records
continuity of both fixed-coordinate presentations, their eventual equality,
and the transported family's value `mfderiv f x` at the centre.

### B3. Regular points are open

lean: `t97A07Closure.isOpen_regularPoints` : under the t97A07 manifold
hypotheses and `hf : ContMDiff I I' ∞ f`,
`IsOpen {x | Function.Surjective (mfderiv I I' f x)}`.

uses: B1, B2

status: proved

At a regular point `x`, use B2 to move every nearby derivative into the
fixed model spaces.  The chart derivative factors on both sides are
continuous linear equivalences, so the transported derivative at `x` is
surjective.  B1 gives an operator neighbourhood consisting of surjective
maps; B2 pulls it back to a neighbourhood of `x`.  Shrink within the common
chart sources and use invariance of surjectivity under composition with the
chart equivalences to conclude that every point of this neighbourhood is
regular.

The compiled proof uses `continuousAt_coordinate_mfderiv` to pull B1's open
surjective-operator set back to a neighbourhood of each regular point.
`surjective_mfderiv_of_surjective_inTangentCoordinates` supplies the needed
pointwise descent: after expanding the transported derivative, injectivity of
the target chart derivative cancels that factor, while the inverse-source
factor supplies a preimage.  Intersecting with the common chart-source
neighbourhood therefore makes every nearby manifold derivative surjective.

### B4. Compactness of the critical-value set

lean: `t97A07Closure.isCompact_criticalValues` : under exactly the topology,
compactness, charted-space, manifold, and smoothness hypotheses of
`apm_t97a07`, `IsCompact (T97A07.criticalValues (m := m) f)`.

uses: B3, Mathlib `IsClosed.isCompact`, `IsCompact.image`, and
`ContMDiff.continuous`

status: proved

The critical points are the complement of B3's open regular-point set, hence
closed and compact in the compact source.  Smoothness makes `f` continuous,
so their image is compact.  Unfold `T97A07.criticalValues` and prove that this
image is exactly the frozen existential set; this node performs the only
set-extensionality conversion needed by later nodes.

Compiled progress: `isCompact_image_criticalPoints` proves the reusable core:
the critical-point set is closed by B3, compact in the compact source, and
has compact image under the continuous smooth map.  The remaining B4 adapter
in the problem module identifies this image with `T97A07.criticalValues`;
keeping that conversion there avoids an import cycle.

`isCompact_criticalValues` in the problem module now performs that exact
set-extensional conversion and completes B4.

### B5. A coordinate maximum is critical

lean: `t97A07Closure.not_surjective_mfderiv_of_isMaxOn_coordinate` : if
`0 < n`, `i : Fin n`, and `x` maximizes `fun z ↦ f z i` on the whole
manifold, then
`¬ Function.Surjective (mfderiv 𝒘(ℝ, E m) 𝒘(ℝ, E n) f x)`.

uses: B2, Mathlib `IsLocalMax.fderiv_eq_zero`, `contMDiffAt_iff`,
`mfderiv_comp`, and the extended-chart derivative equivalences

status: proved

Compiled progress: `not_surjective_of_coordinate_eq_zero` proves the final
linear-algebra step: a map whose `i`th coordinate vanishes on its entire
range cannot hit the `i`th Euclidean basis vector.  The remaining B5 work is
to transfer the global coordinate maximum into the fixed source chart and
prove that the derivative of that scalar chart representative is zero.

Transfer the global maximum to a local maximum of the scalar-valued fixed
chart representative `z ↦ (f ((extChartAt _ x).symm z)) i`.  Its Fréchet
derivative at the chart centre is zero.  The chain rule identifies this
derivative with the `i`th coordinate functional after `mfderiv f x` and the
invertible source-chart derivative.  If `mfderiv f x` were surjective, choose
a tangent vector mapping to the `i`th Euclidean basis vector; the displayed
zero derivative would evaluate both to zero and to one.  This contradiction
proves criticality.  The hypothesis `0 < n` is used only to choose `i`.

Compiled progress: `isLocalMax_coordinate_comp_extChartAt_symm` performs the
maximum transfer to the fixed extended source chart, and
`fderiv_coordinate_comp_extChartAt_symm_eq_zero` applies Fermat's theorem at
the chart centre.  B5 now remains only the chain-rule identification of this
zero scalar derivative with the selected coordinate of `mfderiv f x`.

`fderiv_coordinate_comp_extChartAt_symm_apply` supplies that chain-rule
identity through the canonical tangent-space identification, and
`not_surjective_mfderiv_of_isMaxOn_coordinate` combines it with Fermat and the
coordinate-range obstruction.  This completes B5.

### B6. Positive-dimensional targets have a critical value

lean: `t97A07Closure.criticalValues_nonempty_of_pos` : under the exact
t97A07 hypotheses, `0 < n → (T97A07.criticalValues (m := m) f).Nonempty`.

uses: B5, Mathlib `IsCompact.exists_isMaxOn`

status: planned

Choose `i : Fin n`.  Compactness and nonemptiness of `X` give a maximizer of
the continuous scalar function `fun x ↦ f x i`.  B5 makes that point
critical; its image, together with the defining equality, witnesses
membership in `criticalValues`.  Connectedness is not needed for this node.

### B7. A regular point maps onto a neighbourhood

lean: `t97A07Closure.range_mem_nhds_of_regular` : under the t97A07 manifold
hypotheses, if `hf : ContMDiff I I' ∞ f` and
`Function.Surjective (mfderiv I I' f x)`, then
`Set.range f ∈ 𝒩 (f x)`.

uses: B2, Mathlib `HasStrictFDerivAt.map_nhds_eq_of_surj`, chart inverse laws,
and the derivative equivalences of `extChartAt`

status: planned

In the fixed charts of B2, smoothness supplies a strict derivative at the
chart centre.  The coordinate derivative is surjective because it is
`mfderiv f x` composed with source and target continuous linear
equivalences.  Apply `map_nhds_eq_of_surj` to the representative.  Shrink the
resulting source neighbourhood into the source chart and transport the
target neighbourhood back through the target chart.  The chart inverse laws
show every resulting target point is literally `f y` for some `y`, yielding
`range f ∈ 𝒩 (f x)` rather than only a neighbourhood statement about
the chart representative.

### B8. Finitely many critical values force constancy in target dimension above one

lean: `t97A07Closure.criticalValues_infinite_of_one_lt_of_nonconstant` :
under the exact t97A07 hypotheses,
`1 < n → (∃ x y, f x ≠ f y) →
  (T97A07.criticalValues (m := m) f).Infinite`.

uses: B4, B7, Mathlib
`Set.Countable.isConnected_compl_of_one_lt_rank`, connectedness of continuous
images, compact sets being closed and bounded in Euclidean space, and
connected sets having no nontrivial clopen subset

status: planned

Assume the critical-value set `C` is finite.  Then `Cᶜ` is connected because
`1 < n` gives `1 < Module.rank ℝ (E n)`.  If `range f ⊆ C`, the connected
range of the connected source is a finite connected set and hence a
singleton, contradicting the two unequal values.  Otherwise
`range f ∩ Cᶜ` is nonempty.  It is relatively closed in `Cᶜ` because
`range f` is compact and therefore closed.  It is relatively open because
every one of its points has a preimage `x` whose value is not critical, so
`mfderiv f x` is surjective and B7 supplies a neighbourhood contained in the
range.  Connectedness makes `range f ∩ Cᶜ = Cᶜ`.  The left side is bounded,
whereas the complement of a finite set in the nontrivial Euclidean space
`E n` is unbounded, a contradiction.

### B9. Frozen theorem adapter

lean: `apm_t97a07` : exactly the declaration already present in
`problems/t97A07/lean/Main.lean`.

uses: B4, B6, B8, local theorem `T97A07.criticalValues_zero`

status: planned

Assemble the four conjuncts in their frozen order.  Apply B4 for compactness,
B6 for positive-dimensional nonemptiness, the already compiled
`criticalValues_zero` for `n = 0`, and B8 for infinitude under nonconstancy.
No registered statement or definition changes, and no additional case split
is required.
