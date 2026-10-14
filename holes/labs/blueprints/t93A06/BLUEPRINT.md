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

### `t93A06_periodic_form_descent`

**Statement.** Given a quotient atlas and the independently supplied fibre
characterization, there is a unique smooth torus two-form pulling back to
`sourceForm`.

**Why true.** The scalar coefficient has period one in each coordinate, since
adding an integer changes each trigonometric argument by an integral multiple
of `2π`; the constant area form is translation invariant.  Define the form in
each local inverse chart by transporting `sourceForm`.  Fibre invariance makes
the definition independent of the lift, local smoothness follows from the
explicit coefficient, and surjectivity plus local invertibility of projection
makes pullback injective, giving uniqueness.

**Expected size.** 180–300 lines.

**Dependencies.** It takes the conclusions of `t93A06_torusAtlas` and
`t93A06_projection_fibers` as hypotheses, so its seat can compile in parallel.

**Truth check.** Translation by each basis vector `(1,0)` and `(0,1)` leaves
the coefficient and determinant covector unchanged.  The same argument then
handles every integer vector.  The form is nonzero at the lift `(1/4,0)`, so
the construction is not accidentally the zero form.

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

### `t93A06_not_exact_of_integral_quarter` — LIBRARY

**Statement.** A smooth torus two-form whose fundamental-square integral is
`1/4` is not exact.

**Why true.** If `form = dη`, naturality of exterior derivative identifies its
pullback with `d(projection*η)`.  That pulled-back one-form is periodic on
opposite sides of the square.  Stokes/Green on the square expresses the
integral as four boundary integrals; opposite edges cancel, so it is zero,
contradicting `1/4 ≠ 0`.

**Expected size.** 300–500 lines with the current low-level `Form`,
`IsSmooth`, and `exteriorDerivative` definitions.  This is marked LIBRARY
because the missing ingredient is the general chart calculus/naturality and
Stokes interface identified by the audit (`manifoldForm_smooth_calculus`), not
a problem-specific algebraic trick.  The closest sorry-free files are
`ConstructionTargets.ManifoldFormTargets` (the definitions) and
`ConstructionTargets.ExteriorDerivativeSimplexCalculus` (Euclidean simplex
calculus), but neither supplies the required torus exact-integral theorem.

**Dependencies.** It receives an atlas, smoothness, and the nonzero integral
as hypotheses.  It can therefore be developed independently of the atlas,
descent, and integral seats.

**Truth check.** For an exact periodic one-form `P dx + Q dy`, Green's theorem
gives the four edge terms; period one makes the top/bottom and left/right pairs
cancel.  The check includes the constant and zero primitives, both of which
give integral zero.  Since `(1/4 : ℝ) ≠ 0`, the stated conclusion follows.

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
