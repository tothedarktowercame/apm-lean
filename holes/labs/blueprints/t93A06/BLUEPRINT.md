# Blueprint for t93A06

## Triage

Verdict: **true and faithful**.  No repair is needed.  The registered theorem
uses the coordinatewise quotient `ℝ² → (ℝ/ℤ)²`, asks for exactly the unique
descended smooth two-form, records the integral `1/4`, records nonexactness on
the torus, and gives the explicit primitive and four-edge integral requested by
the source.

I first checked the usual degeneracies.  The ambient plane and torus are
nonempty, the lattice period is fixed to the nonzero real number `1`, and the
coefficient is not the zero function (for example at `(1/4,0)` it is `1`).
The claimed integral is therefore not invalidated by a zero-space or empty-
domain case.  At all four integer vertices the coefficient vanishes, but this
does not affect its positive integral.  The orientation of the listed boundary
is positive: its spanning vectors are `(1,0)` and `(1,1)`, whose determinant is
`1`.  The registered theorem had already been graded faithful, and neither the
solve-loop records nor the topology audit supplied a counterexample.

The definitions are imported unchanged from the sorry-free
`ConstructionTargets.TorusFormTargets`: `Plane`, `Torus`, `projection`,
`SmoothAtlas`, `sourceForm`, `primitive`, `torusIntegral`, and
`parallelogramIntegral`.  I also searched every sorry-free module in
`ConstructionTargets/` for `torus`, `AddCircle`, `exteriorDerivative`, and
`torusIntegral`.  There is substantial torus homotopy/homology infrastructure,
but no existing quotient smooth atlas, differential-form descent, or Stokes
theorem at this interface.  In particular, none of the available
polygon-surface, cover, or torus fundamental-group modules closes either
LIBRARY obligation below.

## Remaining lemmas

### `t93A06_torusAtlas_aux_quotient_charts` — LIBRARY

**Statement.** There is a `ChartedSpace Plane Torus` for which the actual map
`projection : Plane → Torus` is an `IsLocalDiffeomorph`.

**Proof plan.** For a lift `a : Plane`, restrict `projection` to the open box
`Set.pi Set.univ (fun i ↦ Set.Ioo (a i - 1/4) (a i + 1/4))`.  Prove injectivity
with `AddCircle.coe_eq_zero_iff` (the difference is an integer of absolute
value `< 1`), and prove openness using the quotient-map/open-map API for
`QuotientAddGroup.mk`.  Turn the restriction into an
`OpenPartialHomeomorph`; use these maps as the atlas in `ChartedSpace.mk`.
On an overlap, equality in the quotient gives an integer vector `k`; on each
connected box component the transition is `x ↦ x + k`.  Discharge smoothness
with `contDiff_const.add contDiff_id` / `ContDiff.contDiffOn`, and build the
pointwise local diffeomorphism using `LocalDiffeomorph` and
`IsLocalDiffeomorphAt` constructors.  The closest worked model is
`apm_t00j01_klein_local_chart`, especially its `Set.InjOn`, `IsOpenMap`, and
`Equiv.Set.imageOfInjOn`/`toHomeomorphOfContinuousOpen` steps.  Useful Mathlib
facts include `QuotientAddGroup.mk_surjective`, `AddCircle.coe_sub`,
`AddCircle.coe_eq_zero_iff`, `ChartedSpace.mk`, `isOpen_Ioo`, and
`IsOpenMap.restrict`.

**Expected size.** 120–150 lines after factoring the coordinate arguments as
local `have`s.  It is independent of the manifold-coverage seat below.

**Truth check.** Width `1/2` is strictly below the period `1`, so no two points
of a box differ by a nonzero lattice vector.  Boxes are nonempty at every
lift, including representatives lying on a conventional fundamental-square
boundary; charts are centered at the lift, so there is no endpoint case.
Dimension is fixed at `Fin 2`, and the translation derivative is the identity,
so there is no sign convention.

### `t93A06_torusAtlas_aux_manifold_of_localDiffeomorph` — LIBRARY

**Statement.** For an arbitrary candidate `charts`, if the surjective
`projection` is locally a diffeomorphism, then those charts make `Torus` an
`IsManifold`.

**Proof plan.** At `z : Torus`, choose `x` with `projection x = z` using
`t93A06_periodic_form_descent_aux_projection_surjective`'s two-line argument
(or directly, coordinatewise `QuotientAddGroup.mk_surjective`).  Apply
`hlocal x`; its local diffeomorphism supplies a chart neighborhood of `z` and
the required model-range condition.  Transfer the source-plane manifold
property across that local diffeomorphism.  Search/use the Mathlib lemmas
around `IsLocalDiffeomorphAt.isManifold` and
`IsManifold.of_surjective`; if the packaged theorem is absent, unfold
`IsManifold` and use the target/source and `range` fields of the local
diffeomorphism.

**Expected size.** 30–70 lines.  Independent: `charts` and the local-
diffeomorphism conclusion are explicit hypotheses, so this lemma's axioms do
not include the chart-construction sorry.

**Truth check.** Surjectivity prevents a vacuous target point.  The source is
the nonempty two-dimensional plane, and every target point has a chosen lift.

### `t93A06_torusAtlas` — assembly (sorry-free)

Obtains `charts, hlocal` from the chart-construction leaf, applies the manifold
leaf with `hlocal` as an explicit argument, and fills the two fields of
`SmoothAtlas`.  This is deliberately only structure assembly.

### `t93A06_projection_fibers`

**Statement.** Two points of `Plane` have the same projection iff their
coordinates differ by integers.

**Why true.** Apply the equality criterion in `AddCircle 1` coordinatewise.
Function extensionality proves the forward projection equality, and finite
choice over `Fin 2` collects the two integer witnesses in the reverse
direction.

**Expected size.** 40–80 lines.

**Dependencies.** Definitions only.

**Truth check.** For `x=y`, choose the zero integer vector.  For the nontrivial
test `y=x+![2,-3]`, quotient equality holds in both coordinates.  A half-
integer displacement fails, as required.

### `t93A06_periodic_form_descent_aux_set_descent`

**Statement.** Given an atlas, the fibre characterization, and periodicity of
`sourceForm` as explicit hypotheses, there is a (not yet asserted smooth) form
on `Torus` whose pullback by `projection` is `sourceForm`.

**Proof plan.** For `z : Torus`, choose a lift `x` using
`t93A06_periodic_form_descent_aux_projection_surjective`.  Since
`atlas.quotient_localDiffeomorph` makes `mfderiv projection x` a continuous
linear equivalence, define the value at `z` by composing `sourceForm x` with
the inverse derivative.  Use `Classical.choose` (or quotient lifting) to make
this a global function.  If `y` is another lift, `hfib` writes it as
`x + k`; `hperiodic` identifies the source covectors.  The remaining derivative
identity follows because `projection` is a continuous group quotient and
integer translation has derivative the identity.  Useful Mathlib lemmas are
`IsLocalDiffeomorph.mfderivToContinuousLinearEquiv`,
`ContinuousLinearEquiv.apply_symm_apply`, `mfderiv_comp`,
`HasMFDerivAt.mfderiv`, `QuotientAddGroup.mk_surjective`, and the
`ContMDiff`/derivative lemmas for `QuotientAddGroup.mk` available through the
local-diffeomorphism hypothesis.  A robust alternative is to compare both
candidate values after composing with the invertible derivative and use
`ContinuousAlternatingMap.ext`.

**Expected size.** 70–130 lines.  Independent of the smoothness leaf: its only
nondefinition inputs are `hfib` and `hperiodic`.

**Truth check.** Every torus point has a lift.  Fibres are nonempty and two
lifts differ by an integer vector, including points represented on a
fundamental-domain boundary.  The derivative is invertible at every lift, so
the transported covector is defined even where the scalar coefficient is
zero.  This is genuine existence, not merely a restatement of `hperiodic`.

### `t93A06_periodic_form_descent_aux_smooth_of_pullback`

**Statement.** For any form on the torus, if its pullback is `sourceForm` and
`sourceForm` is smooth as a Euclidean covector field, then the form is smooth
in every chart of the supplied quotient atlas.

**Proof plan.** Fix `e ∈ atlas Plane Torus` and a point of `e.target`.
Choose the corresponding torus point and a lift.  Apply
`atlas.quotient_localDiffeomorph` at that lift and use its
`localInverse`; after shrinking to the intersection with `e.source`, the
inverse is a smooth local section of `projection`.  Rewrite `inChart form e`
locally by `hpull` as `sourceForm` composed with this section and with the
appropriate derivatives.  Smoothness follows from `hsource`, smoothness of
the chart transition, and smoothness of `mfderiv` for the local diffeomorphism.
Patch the pointwise neighborhoods with `contDiffOn_iff_contDiffAt` (or
`ContDiffOn.of_locally`).  Relevant API is in
`Mathlib/Geometry/Manifold/LocalDiffeomorph`: `IsLocalDiffeomorph.localInverse`,
`localInverse_mem_source`, `right_inv`, `contMDiffOn_localInverse`, and
`mfderivToContinuousLinearEquiv`; also use `mem_atlas_iff`/
`writtenInExtChartAt` transition smoothness, `mfderiv_comp`, and
`ContDiffOn.contDiffAt`.

**Expected size.** 100–150 lines.  Independent of set-level descent because
`form`, `hsource`, and `hpull` are all explicit hypotheses.

**Truth check.** Smoothness is local and projection has a local inverse at
every lift; surjectivity rules out uncovered torus points.  Zeros of
`sourceForm` cause no issue because the argument uses invertibility of the
projection derivative, not division by the coefficient.  The assertion is
for every atlas chart, not only a preferred quotient chart.

### `t93A06_periodic_form_descent` — assembly (sorry-free)

Obtains a form and its pullback equality from the set-descent leaf, applies
the smoothness leaf using the already proved source-smoothness lemma, and gets
uniqueness from the already proved pullback-injectivity lemma.  The smoothness
hypothesis on a competing form is intentionally unused: injectivity is the
stronger statement.

### `t93A06_torusIntegral_quarter`

**Statement.** For any atlas and any form whose pullback is `sourceForm`, the
defined fundamental-square integral is `1/4`.

**Why true.** Rewrite by the pullback hypothesis.  The integrand on the basis
vectors is
`sin²(2πx) cos²(2πy)`.  Fubini separates it, and the two standard one-period
integrals are both `1/2` (use the double-angle identities and the fundamental
theorem of calculus).

**Expected size.** 70–130 lines.

**Dependencies.** Definitions and the supplied pullback equality only; it is
independent of descent.

**Truth check.** Both factors are nonnegative and have average `1/2` over one
period, so their product has average `1/4`.  Reversing the basis-vector order
would change the determinant sign, but the definition uses `(e₀,e₁)`, the
positive order.

### Exactness/integral split

The former 300–500 line LIBRARY leaf is split into the following parallel
leaves.  `t93A06_pulledCoeff atlas η i x` is the coefficient of
`projection*η` on the constant coordinate vector `eᵢ`.

#### `t93A06_exact_integral_aux_pullback_d` — 100–150 lines, independent

Proves naturality `projection*(dη) = d(projection*η)`.  Unfold `pullback`,
`exteriorDerivative`, and `inChart`; use the atlas compatibility of
`chartAt Plane (projection x)` with the global identity chart on `Plane`,
`atlas.quotient_localDiffeomorph`, `mfderiv_comp`, and the chain rule for
`fderiv`.  Useful APIs are `HasMFDerivAt.mfderiv`,
`IsLocalDiffeomorph.mfderivToContinuousLinearEquiv`, `extDeriv`,
`fderiv_comp`, and `ContinuousAlternatingMap.compContinuousLinearMap`.
This is the riskiest leaf: the local `exteriorDerivative` definition has no
packaged naturality theorem, so its chart-change calculation must be exposed.

#### `t93A06_exact_integral_aux_coeff_smooth` — 60–110 lines, independent

From `IsSmooth η`, proves the two one-variable coefficient slices are `C¹`.
Use a local inverse of `projection` and rewrite the pulled-back coefficient in
the relevant torus chart.  APIs: `IsLocalDiffeomorph.localInverse`,
`contMDiffOn_localInverse`, `mfderiv_comp`, `ContDiff.comp`, and
`ContDiff.of_le`.  The statement supplies exactly the regularity required by
the FTC leaves and does not depend on naturality.

#### `t93A06_exact_integral_aux_square_formula` — 80–140 lines, independent

Given naturality explicitly, unfolds `torusIntegral`, `exteriorDerivative`,
`extDeriv`, and the determinant on `(e₀,e₁)` to obtain
`∫∫ ∂x Q - ∫∫ ∂y P`.  Use `Matrix.det_fin_two`,
`ContinuousAlternatingMap.alternating`, `intervalIntegral.integral_sub`, and
the coordinate `fderiv`/`deriv` lemmas.  Sign check: for `P dx + Q dy`, the
positive basis `(e₀,e₁)` gives `∂x Q - ∂y P`, not its negative.

#### `t93A06_exact_integral_aux_ftc_x` — 25–50 lines, independent

Applies the one-dimensional FTC to `x ↦ Q x y`, pointwise in `y`, then
rewrites under the outer integral.  Prefer
`intervalIntegral.integral_deriv_eq_sub'`; alternatively produce
`HasDerivAt` from `ContDiff.differentiable` and use
`intervalIntegral.integral_eq_sub_of_hasDerivAt`.  `ContDiff` supplies both
continuity of the derivative and interval integrability.

#### `t93A06_exact_integral_aux_ftc_y` — 25–50 lines, independent

The same argument for `y ↦ P x y`.  It is deliberately separate so both FTC
seats can land in parallel.

#### `t93A06_exact_integral_aux_periodic` — 40–80 lines, independent

Proves opposite-edge equality of pulled-back coefficients.  The base points
have equal projections by `AddCircle.coe_add_intCast`/`AddCircle.coe_one`, and
the derivatives of projection at integer translates agree.  Unfold
`t93A06_pulledCoeff` and `pullback`; use `projection`'s coordinate definition,
`mfderiv` congruence, and extensionality.  Boundary points are harmless:
`0` and `1` are literally the same `AddCircle 1` point, while the unrestricted
other coordinate agrees on both sides.

#### `t93A06_exact_integral_aux_boundary_cancel` — 5–15 lines, independent

Rewrite both integrands to zero using the two periodicity hypotheses and
`simp`.  This small leaf makes the cancellation/sign endpoint explicit.

#### `t93A06_not_exact_of_integral_quarter` — assembly, sorry-free

Destructs exactness as `form = dη`, applies naturality and the square formula,
uses the two FTC identities and periodic cancellation, and contradicts
`torusIntegral form = 1/4` by `linarith`.  Every preceding conclusion is
passed explicitly, so no new leaf's axioms include another leaf's `sorry`.
The zero and constant primitives yield zero on both sides; there is no empty
domain or dimension-zero case (`Plane = Fin 2 → ℝ`, square `[0,1]²`).

### `t93A06_primitive_calculus`

**Statement.** The explicit plane one-form `primitive` is smooth and its
exterior derivative is `sourceForm`.

**Why true.** In the global identity chart, smoothness follows from smoothness
of coordinate projections, sine, cosine, products, and scalar multiplication.
Differentiate
`x/2 - sin(4πx)/(8π)` in `x`; its derivative is
`(1-cos(4πx))/2 = sin²(2πx)`.  The unwanted `y` derivative wedges with `dy`
and vanishes.

**Expected size.** 90–150 lines.

**Dependencies.** Definitions only.

**Truth check.** At `x=0`, both the derivative and `sin²(2πx)` are zero; at
`x=1/4`, both are one.  `Real.pi_ne_zero` validates all denominators.

### `t93A06_primitive_parallelogramIntegral`

**Statement.** Direct evaluation of `primitive` on the four printed oriented
segments is `1/4`.

**Why true.** Unfold `segmentIntegral`.  The two horizontal edges contribute
zero because the covector is a multiple of `dy`.  Parametrize the slanted
edges, simplify their opposite orientations, and evaluate the remaining
one-variable trigonometric integrals.  Equivalently, after the same explicit
calculation, Green's theorem over `(s,t) ↦ (s+t,t)` has Jacobian one and gives
the separated integral `1/4`.

**Expected size.** 80–140 lines.

**Dependencies.** Definitions only; it deliberately does not depend on the
exterior-derivative lemma.

**Truth check.** The vertex order is counterclockwise and the affine
parametrization has determinant `1`.  Reversing the four vertices would give
`-1/4`, confirming that the orientation sign in the statement is meaningful.

## Dependency layers

* **Layer 1 (all parallel):** `t93A06_torusAtlas`,
  `t93A06_projection_fibers`, `t93A06_torusIntegral_quarter`,
  `t93A06_not_exact_of_integral_quarter`,
  `t93A06_primitive_calculus`, and
  `t93A06_primitive_parallelogramIntegral`.
* **Layer 2 (also independently compilable because prerequisites are explicit
  hypotheses):** `t93A06_periodic_form_descent`.
* **Layer 3 (sorry-free assembly):** `apm_t93a06` combines all seven results.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t93A06/Blueprint.lean
```

The final output of `#print axioms apm_t93a06` was:

```text
'apm_t93a06' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The seven warnings identifying `sorry` are exactly the seven top-level
obligations above.  The main theorem has no direct `sorry`.
