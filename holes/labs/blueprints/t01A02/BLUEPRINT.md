# Blueprint for t01A02

## Triage

Verdict: **true and faithful**.  The registered Lean theorem uses the concrete
torus `Circle × Circle`, the coordinatewise squaring cover, integral singular
`H₂`, and exactly the non-surjectivity and factorization hypotheses in
`problem.md`.

I tried the relevant degeneracies.  A constant map is nonsurjective and its
`H₂` map is zero; if its value is `(1,1)`, it factors through the squaring
cover and has that value as a fixed point.  Coordinate maps such as
`(z,w) ↦ (z²,1)` are nonsurjective and have zero top-dimensional degree.
The cover itself is surjective, so it does not accidentally satisfy the
non-surjectivity hypothesis of part (c).  There is no empty-space or zero-space
degeneracy because `Circle × Circle` is fixed and inhabited.  These checks
agree with the informal degree/Lefschetz argument and with the batch note that
the statement was graded faithful.

The concrete cover/deck-action theorem is already proved in the sorry-free
`ConstructionTargets.TorusSquareDeckAction`.  The once-punctured torus `H₂`
calculation and the factor-through-zero adapter are already proved in the
sorry-free `ConstructionTargets.T01A02PuncturedTorusH2`; the blueprint imports
and uses them.  I also searched all sorry-free `ConstructionTargets` files for
`T01A02`, `Torus`, and `Lefschetz`.  `RationalLefschetz` defines only an
interface and supplies no fixed-point theorem.  No existing module supplies
the remaining integer-lift/planar-surjectivity result.

## Remaining lemmas

### `apm_t01A02_punctured_H2_isZero`

**Statement in words.** The integral second singular homology of the torus
with any one point removed is zero.

**Why true.** The banked theorem
`ConstructionTargets.T01A02PuncturedTorus.puncturedTorus_H2_isZero` proves this
for the fixed puncture `(-1,-1)`.  Coordinatewise multiplication by constants
in `Circle` is a homeomorphism carrying an arbitrary `q` to that point.
Restrict it with `Homeomorph.subtypeCongr`, apply the homology functor to the
resulting `TopCat` isomorphism, and transport `IsZero` across that isomorphism.
The relevant banked theorem and `H2map_eq_zero_of_factor` were checked by
compiling the import and the downstream adapter in `Blueprint.lean`.

**Expected size.** 30–60 lines.

**Dependencies.** Definitions and
`ConstructionTargets.T01A02PuncturedTorusH2` only.

**Truth check.** At the banked puncture this is exactly the compiled theorem.
Multiplication on each circle has an explicit inverse, so no special point
(including `(1,1)` and `(-1,-1)`) is exceptional.

### Fixed-point split: important correction

Factorization through coordinatewise squaring makes every entry of the
winding matrix even.  Consequently
`det (I - 2A) = 1 - 2 tr(A) + 4 det(A)` is odd, hence nonzero, for *every*
integer `2 × 2` matrix `A`.  Thus the hypotheses imply a fixed point outright;
the surjectivity disjunct in the registered statement is not needed.  The
earlier sketch's case split on `det A` was therefore unnecessary (and its
claim that fixed-point-freeness forces invertibility had the logical direction
backwards).

The following five leaves expose the actual foundations.  Each leaf takes any
conclusion of an earlier leaf as an explicit hypothesis, so all five can be
worked on independently.

#### `apm_t01A02_evenLift_of_factorsThroughSquare`

**Statement.** A factorization `f = cover ∘ g` gives a continuous lift
`F : ℝ × ℝ → ℝ × ℝ` representing `f`, with both deck-translation increments
equal to `2π` times even integer column vectors.

**Proof route / Mathlib tools.** First lift `g ∘ apm_t01A02_torusExp`
coordinatewise through `Circle.exp`.  The intended lifting tool is
`IsCoveringMap.existsUnique_continuousMap_lifts` from
`Mathlib.Topology.Homotopy.Lifting`; alternatively apply the corresponding
one-dimensional lift twice.  Use `Circle.exp.continuous`, `Circle.exp_add`,
`Circle.exp_eq_exp`, connectedness of `ℝ × ℝ`, and discreteness of `ℤ` to show
each deck increment is constant.  Squaring doubles those increments, producing
the displayed even matrix.  `Circle.exp_eq_one` handles period normalization.

**Estimated size.** 100–150 lines.  **Independent:** yes; only definitions and
`hlift`.

**Truth checks.** A constant `g` yields `a=b=c=d=0`.  No basepoint value is
prescribed, so there is no false normalization requirement.  The period is
`2π`, matching `Circle.exp_eq_exp`, including negative winding numbers.

#### `apm_t01A02_evenLift_error_bounded`

**Statement.** Given the explicit equivariance equations in
`apm_t01A02_IsEvenLift`, subtracting the associated linear map leaves a
globally bounded function.

**Proof route / Mathlib tools.** Define the error, prove invariance under the
two `2π` translations by `ring_nf`/`norm_num`, reduce arbitrary coordinates to
a fundamental square using `Int.floor`, and bound the norm there.  Useful
compactness lemmas are `isCompact_Icc`, `IsCompact.image_of_continuousOn`,
`IsCompact.isBounded`, or `IsCompact.exists_bound_of_continuousOn`.

**Estimated size.** 80–140 lines.  **Independent:** yes; `hF` is an explicit
hypothesis rather than a reference to the lift lemma.

**Truth checks.** Zero winding gives bounded `F` itself.  Boundary points of
the closed fundamental square cause no issue because the error is periodic.
The bound is existential and need not be nonnegative.

#### `apm_t01A02_even_matrix_fixedPoint_det_ne_zero`

**Statement.** The integer determinant of `I - 2A` is nonzero.

**Proof route / Mathlib tools.** Show the expression is congruent to `1`
modulo `2`; `omega` should close after exposing the expression, or use
`Int.not_even_one` plus `ring`.  This is exactly
`1 - 2(a+d) + 4(ad-bc)`.

**Estimated size.** 15–30 lines.  **Independent:** completely.

**Truth checks.** This covers singular `A`, including the zero matrix.  Signs
of the off-diagonal terms agree with `det (I - 2A)`; their product is `4bc`.

#### Second-level split of planar Brouwer

`apm_t01A02_planar_fixedPoint_of_bounded_affine_error` is now a sorry-free
two-line assembly.  The disk is the subtype
`Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1`, and its boundary is the
corresponding `Metric.sphere`.  The following seven leaves are mutually
independent: whenever an assembly needs another leaf's result, it receives
that result as an explicit hypothesis.

##### `apm_t01A02_bounded_affine_error_reduces_to_disk`

**Statement.** The bounded-error hypotheses and nonzero determinant produce a
continuous disk self-map whose fixed point yields a fixed point of `F`.

**Proof route / Mathlib tools.** Let `L = I - 2A`, put
`e(x) = F(x)-2A x`, and use the explicit inverse of the two-by-two matrix
`L`.  Boundedness of `e` bounds `L⁻¹e`; choose a positive radius at least that
bound and conjugate the resulting closed-radius-ball self-map by scalar
rescaling.  Useful tools: `Matrix.det_fin_two`, `Matrix.mulVec`,
`Matrix.mulVecLin`, `Matrix.inv_def`, `Continuous.matrix_mulVec`,
`ContinuousMap.restrict`, `Metric.mem_closedBall`, and `norm_smul`.

**Estimated size.** 90–140 lines.  **Independent:** yes.

**Truth checks.** The existential bound is automatically nonnegative by
evaluating it at `0`; nevertheless choose radius `max 1 (...)`, so division by
zero is impossible.  With `A=0` this is just the bounded-map case.  The fixed
point implication (rather than a claimed fixed point) prevents this leaf from
hiding Brouwer.

##### `apm_t01A02_disk_ray_hits_boundary_unique`

**Statement.** For distinct disk points `x,y`, exactly one `t ≥ 0` satisfies
`‖x+t(x-y)‖=1`.

**Proof route / Mathlib tools.** Square the norm and solve
`‖x-y‖²t² + 2⟪x,x-y⟫t + (‖x‖²-1)=0`.  The leading coefficient is positive;
the constant coefficient is nonpositive.  Existence can also use the
intermediate value theorem plus coercivity, and uniqueness follows from strict
increase on the outward ray.  Useful tools: `real_inner_self_eq_norm_sq`,
`norm_sq`, `sq_sqrt`, `Real.sqrt_nonneg`, `inner_sub_left`, Cauchy--Schwarz,
`intermediate_value_Icc`, and `nlinarith`.

**Estimated size.** 70–120 lines.  **Independent:** yes.

**Truth checks.** If `x` is already on the boundary, the unique parameter is
`0`.  If `x=0`, the positive root is `1/‖y‖`; distinctness ensures the
quadratic is not degenerate.  The ray points away from `y`, not toward it.

##### `apm_t01A02_continuous_boundary_hit_of_no_fixedPoint`

**Statement.** Given uniqueness of the ray parameter pointwise, a continuous
fixed-point-free disk map has a continuous boundary-hit map, together with its
ray characterization.

**Proof route / Mathlib tools.** Use the positive quadratic root
`(-b + sqrt (b²-a*c))/a` (with a consistent factor-of-two convention).
Continuity follows since `‖x-g x‖²>0`; then package the norm-one value as a
subtype.  Useful tools: `Continuous.inner`, `Continuous.norm`,
`Continuous.sqrt`, `Continuous.div`, `continuous_subtype_mk`, and the supplied
uniqueness hypothesis to identify the formula's root.

**Estimated size.** 80–130 lines.  **Independent:** yes; ray existence and
uniqueness is an explicit hypothesis.

**Truth checks.** The denominator never vanishes because `g x ≠ x`.  The
discriminant is nonnegative for disk points.  No choice-continuity principle is
assumed: continuity comes from the explicit formula.

##### `apm_t01A02_boundary_ray_parameter_eq_zero`

**Statement.** If `‖x‖=1`, `‖y‖≤1`, `t≥0`, and
`‖x+t(x-y)‖=1`, then `t=0`.

**Proof route / Mathlib tools.** Expand squared norms and use
`⟪x,y⟫≤‖x‖‖y‖≤1`; every nonzero outward displacement strictly increases the
norm.  Use `real_inner_le_norm`, `real_inner_self_eq_norm_sq`, and `nlinarith`.

**Estimated size.** 25–45 lines.  **Independent:** yes.

**Truth checks.** Equality cases such as `y=-x` still force `t=0`.  The
`x ≠ y` hypothesis is essential: if `x=y`, the sphere equation holds for every
`t`.  The retraction assembly obtains distinctness from `g x ≠ x`.

##### `apm_t01A02_disk_H1_isZero`

**Statement.** Integral `H₁` of the closed disk is zero.

**Proof route / Mathlib tools.** Install
`Metric.contractibleSpace_closedBall (by norm_num)` and apply
`ConstructionTargets.CoefficientContractiblePair.higher_zero ℤ _ 1`.

**Estimated size.** 10–20 lines.  **Independent:** yes.

##### `apm_t01A02_diskBoundary_H1_not_isZero`

**Statement.** Integral `H₁` of the boundary sphere is nonzero.

**Proof route / Mathlib tools.** The boundary is definitionally the
one-sphere used by `ConstructionTargets.SphereHomology`; use
`sphereModuleTopHomologyIsoInt 1` and transport nonzeroness from
`ModuleCat.of ℤ ℤ` (witness `1`).  `CoefficientFirstReflection.topIso ℤ 0`
is an alternative coordinate.

**Estimated size.** 20–35 lines.  **Independent:** yes.

##### `apm_t01A02_no_disk_boundary_retraction`

**Statement.** Explicit disk-H1 vanishing and boundary-H1 nonvanishing rule
out a strict retraction.  Both homology facts are explicit hypotheses.

**Proof route / Mathlib tools.** Define boundary inclusion `i`; functoriality
and `i ≫ r = 𝟙` give `H₁(i) ≫ H₁(r)=𝟙`.  The source of `H₁(r)` is zero, hence
the composite and identity are zero, making boundary H1 zero.  Use
`Functor.map_comp`, `Functor.map_id`, `IsZero.eq_of_src`, and
`IsZero.iff_id_eq_zero`.

**Estimated size.** 35–60 lines.  **Independent:** yes.

`apm_t01A02_disk_retraction_of_no_fixedPoint`,
`apm_t01A02_disk_fixedPoint`, and the original planar lemma are sorry-free
assemblies.  The retraction assembly threads `g x ≠ x` into the boundary-sign
leaf and uses only the explicit boundary-hit hypothesis.

#### `apm_t01A02_fixedPoint_of_lift_fixedPoint`

**Statement.** A planar fixed point descends through the representing equation
to a torus fixed point.

**Proof route / Mathlib tools.** Choose the planar fixed point, choose
`apm_t01A02_torusExp x` downstairs, rewrite with `hrep` and `hfix`.

**Estimated size.** 5–15 lines.  **Independent:** yes; both needed facts are
explicit hypotheses.

**Truth checks.** No injectivity of the exponential is claimed or needed.

## Proved assembly

`apm_t01A02_H2map_eq_zero` chooses a missed point, factors `f` through its
complement, and applies the banked factor-through-zero theorem plus the first
lemma.  `apm_t01A02_covering_group` is proved entirely from the banked deck
action.  The final theorem resolves the fixed-point/surjective dichotomy using
the given non-surjectivity hypothesis.  The main theorem has no direct
`sorry`.

## Dependency layers

* **Layer 1 (parallel):** the original four non-Brouwer leaves plus the seven
  new Brouwer leaves above (their inputs are explicit hypotheses), independently
  of `apm_t01A02_punctured_H2_isZero`.
* **Layer 2 (sorry-free assembly):**
  `apm_t01A02_fixedPoint_or_surjective_of_lift` selects the fixed-point
  disjunct and composes the five leaves.
* **Layer 3 (already compiled):** the final conjunction.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t01A02/Blueprint.lean
```

The output of `#print axioms apm_t01a02` was:

```text
'apm_t01a02' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The eleven warnings identifying `sorry` are exactly the four original
fixed-point leaves and the seven new Brouwer leaves.  The former LIBRARY
theorem and all intermediate Brouwer/retraction steps are now sorry-free
assemblies.  The punctured-torus lemma remains proved and unchanged.
