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

#### `apm_t01A02_planar_fixedPoint_of_bounded_affine_error` (LIBRARY)

**Statement.** If a continuous `F : ℝ² → ℝ²` differs boundedly from `2A`,
and `I - 2A` is nonsingular, then `F` has a fixed point.

**Proof route.** Apply Brouwer to a sufficiently large closed ball after
rewriting the equation as `(I - 2A)x = error(x)`.  The inverse linear map sends
the bounded error into a fixed ball.  Mathlib has the finite-dimensional
linear algebra needed (`Matrix.det_ne_zero`, `LinearMap.inverse`, operator-norm
bounds, compact/convex closed balls), but the search found no ready-made
Brouwer fixed-point theorem.  Therefore this one leaf remains honestly
**LIBRARY**: it needs a 2-dimensional Brouwer/degree foundation rather than an
adapter disguised as a small lemma.

**Estimated size.** 150–300 lines if Brouwer must be developed/imported; about
60–100 lines if a suitable existing fixed-point theorem is located.
**Independent:** yes; continuity, boundedness, and determinant are explicit
hypotheses.

**Truth checks.** The bound may be negative only when the domain is impossible;
since the domain is inhabited, the hypothesis itself forces `C ≥ 0`.  Constant
errors and `A=0` reduce to the obvious constant-map fixed point.  Nonsingularity
is essential: translation by a nonzero constant is a bounded perturbation of
the identity and has no fixed point.

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

* **Layer 1 (parallel):** the five fixed-point leaves above (their inputs are
  explicit hypotheses), independently of `apm_t01A02_punctured_H2_isZero`.
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

The five warnings identifying `sorry` are exactly the five fixed-point leaves.
The former LIBRARY theorem is now a sorry-free assembly.  The punctured-torus
lemma remains proved and unchanged.
