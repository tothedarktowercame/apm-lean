# Blueprint for t02A05

## Triage

Verdict: **true and faithful**.  No statement repair is needed.

The source asks for the outward flux through unit spheres.  The registered
statement represents the given two-form explicitly, uses the radial outward
unit normal and tangent projections, and integrates against normalized
Euclidean Hausdorff measure `μHE[2]`.  Its conclusion says exactly that the
minimum is `44π/15` and that the minimizing centers are the whole line
`c 0 = 1`, `c 1 = 2`, with no restriction on `c 2`.

I tried the relevant degeneracies.  The sphere radius is fixed at one, so no
empty/zero-radius case is present.  The third center coordinate cancels from
the translated linear term, agreeing with the claimed line of minimizers.  At
`c = (1,2,z)` the centered flux density has moments
`mass * (1/5 + 1/5 + 1/3) = mass * 11/15`; normalized sphere mass `4π` gives
`44π/15`.  Moving the first two center coordinates adds
`4π ((c 0-1)^2 + (c 1-2)^2)`, which is nonnegative and vanishes exactly on
that line.

The old topology STOP was not a counterexample: it concerned the absence of a
numerical theorem for raw `μH[2]`.  The registered integral uses normalized
`μHE[2]`.  Mathlib provides
`Measure.euclideanHausdorffMeasure_def`,
`EuclideanSpace.euclideanHausdorffMeasure_eq_volume`, and isometry invariance;
the remaining job is the subtype/coarea-style sphere-mass calculation and the
scalar transport to the already compiled raw moments.

The sorry-free files `ConstructionTargets/IntrinsicSphereFinite.lean`,
`IntrinsicSphereSecondMoments.lean`, and
`IntrinsicSphereFourthMoments.lean` were checked for placeholders.  In
particular, `ConstructionTargets.IntrinsicSphereFourthMoments.unitFlux_moment`
is banked and has the exact shifted cubic/linear raw-Hausdorff moment needed
here.

## Definitions

`apm_t02a05_radialFlux c x` is the ordinary dot product of the radial normal
`x-c` with the vector field represented by the two-form.  It isolates the
measure/translation calculation from the point-dependent tangent projections.
All other definitions are copied unchanged from `Main.lean`.

## Remaining lemmas

### `apm_t02a05_orientedCoefficient_eq_radialFlux`

**Statement in words.** At every point of the unit sphere, the alternating
coefficient evaluated on the projected coordinate vectors equals the ordinary
radial flux density.

**Why true.** Put `n = q-c`.  Sphere membership gives `‖n‖ = 1`.  Projection
onto `(span {n})ᗮ` is `eᵢ - nᵢ n`; establish this from the characterizing
properties of `Submodule.orthogonalProjection`.  Substitute these three
projections into `homega`.  Alternation/determinant expansion makes all terms
parallel to `n` cancel, leaving
`n₀(q₀-1)^3 + n₁(q₁-2)^3 + n₂(q₂-3)`.

**Expected size.** 60–110 lines.

**Dependencies.** Definitions only.  It is independent of both measure
lemmas.

**Truth check.** For `q-c = e₀`, the projections are `0,e₁,e₂`, and the
registered oriented coefficient reduces directly to `(q 0-1)^3`, exactly the
radial flux.  The same check works for `e₁` and `e₂`; the determinant identity
then gives the general unit normal case.

### `apm_t02a05_euclideanHausdorff_unitSphere_mass`

**Statement in words.** The total normalized two-dimensional Euclidean
Hausdorff measure of the unit sphere in `ℝ³` is `4π`.

**Why true.** Use `μHE[2] = volume` on the two-dimensional tangent model via
`EuclideanSpace.euclideanHausdorffMeasure_eq_volume`, cover the sphere by the
standard upper/lower graph charts (the equator is null), and apply the area
formula/radial graph Jacobian.  Equivalently, derive the sphere mass from the
polar decomposition of three-dimensional volume, identifying its angular
measure with the restriction of `μHE[2]`.  This is the one genuinely analytic
normalization seam; it must not be replaced by the false raw equation
`μH[2](sphere) = 4π`.

**Expected size.** 90–150 lines.

**Dependencies.** Definitions and Mathlib only.  It is independent of the
projection and flux-transport lemmas.

**Truth check.** The classical graph integral is
`2 * ∫_{x²+y²<1} 1/sqrt(1-x²-y²) dx dy = 4π`.  The value also has the correct
radius-two scaling (`16π`) under `euclideanHausdorffMeasure_smul₀`.

### `apm_t02a05_radialFlux_integral`

**Statement in words.** Assuming the normalized centered unit-sphere mass is
`4π`, the integral of the explicit radial flux over a unit sphere centered at
`c` is the required quadratic expression.

**Why true.** Transport `q` to `x=q-c` using
`IsometryEquiv.vaddConst` and
`IsometryEquiv.measurePreserving_euclideanHausdorffMeasure`.  Rewrite
`μHE[2]` with `Measure.euclideanHausdorffMeasure_def`; after distributing the
scalar, apply
`ConstructionTargets.IntrinsicSphereFourthMoments.unitFlux_moment`.  That
theorem gives raw mass times
`11/15 + (c 0-1)^2 + (c 1-2)^2`.  Convert the scalar-times-raw-mass factor to
the assumed normalized mass `4π` and finish by ring arithmetic.

The mass conclusion is deliberately an argument, not a dependency hidden in
the proof, so a separate seat can prove this lemma at the same time as the
mass lemma.

**Expected size.** 80–140 lines.

**Dependencies.** Definitions, the banked `unitFlux_moment`, and the stated
`hmass` hypothesis.  No dependency on the preceding two blueprint lemmas.

**Truth check.** At `c=(1,2,3)`, `unitFlux_moment` gives the factor `11/15`,
so the hypothesis produces `44π/15`.  Expanding a shift in the first
coordinate adds exactly `4π(c 0-1)^2`; all odd cross terms vanish by the
banked reflection lemmas.

## Assembly

`apm_t02A05_bridge_1` is sorry-free: integral congruence uses the pointwise
projection lemma, then the transport lemma is instantiated with the mass
lemma.  The final theorem is also sorry-free and applies the already compiled
`apm_t02a05_quadratic_minimum` to each center.

## Dependency layers

* **Layer 1 (parallel):**
  `apm_t02a05_orientedCoefficient_eq_radialFlux`,
  `apm_t02a05_euclideanHausdorff_unitSphere_mass`, and
  `apm_t02a05_radialFlux_integral` (the latter receives the mass equality as a
  hypothesis).
* **Layer 2 (already compiled assembly):** `apm_t02A05_bridge_1` and
  `apm_t02a05` after the three Layer 1 lemmas are supplied.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t02A05/Blueprint.lean
```

The three warnings identify exactly the three Layer 1 lemmas.  The output of
`#print axioms apm_t02a05` is:

```text
'apm_t02a05' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

Thus `sorryAx` reaches the registered theorem only through the named blueprint
lemmas; neither bridge assembly nor final optimization contains a `sorry`.
