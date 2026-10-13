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

### `t93A06_torusAtlas` — LIBRARY

**Statement.** `SmoothAtlas` is nonempty: there is a charted structure on
`(AddCircle 1)²` making it a smooth two-manifold and making the actual
coordinate quotient projection a local diffeomorphism.

**Why true.** Give each circle the standard quotient charts obtained by
choosing a lift on an interval shorter than one, take product charts, and use
the local lift as the inverse of `projection`.  Transition maps differ by
locally constant integer translations and hence are smooth.  This is the exact
`SmoothAtlas` interface already requested by the topology worklist under
`torusAtlas`.

**Expected size.** 300–600 lines.  This is intentionally one LIBRARY program,
not several fake short lemmas; the atlas, manifold proof, and local-
diffeomorphism certificate share the same chart construction.

**Dependencies.** Definitions only.

**Truth check.** On each factor, the quotient map restricted to
`(a-1/2,a+1/2)` is injective and has a continuous inverse onto its image.  The
product of two such neighborhoods supplies the required local inverse at every
point; there is no endpoint case because the chart center can be moved.

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
