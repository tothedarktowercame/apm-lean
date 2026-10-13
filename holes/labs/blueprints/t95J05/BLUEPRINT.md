# Blueprint for t95J05

## Triage and repair

Verdict: **the registered statement is false, and the one-token measure repair is faithful**.

The source asks for the ordinary oriented integral of a differential form over
`ℝP³`.  Upstairs on the unit `S³`, that uses conventional Euclidean surface
measure.  The old definition

```lean
(1 / 2 : ℝ) * ∫ x, η.1 x ∂Measure.hausdorffMeasure 3
```

instead used Mathlib's raw, diameter-power Hausdorff measure.  In dimension
three this is `(6/π)` times Euclidean surface measure.  The density has
Euclidean surface integral `-2π²`, so the old quotient integral is `-6π`, not
`-π²`.  This is the counterexample identified by the statement-registry
grader.  It is also consistent with the topology-loop reduction
`IntrinsicSphereSecondMoments.projective_density_moment`, which says that the
raw density integral is minus the raw total mass.

`RevisedMain.lean` makes the smallest warranted change: it replaces
`Measure.hausdorffMeasure 3` by `μHE[3]` in `t95J05Integral`.  No mathematical
hypothesis or conclusion changes.  This is exactly conventional Euclidean
Hausdorff measure and therefore expresses the surface integral in
`problem.md`.  The grader's counterexample no longer applies: `μHE[3](S³) =
2π²`, hence the density integral is `-2π²`, and division by the double-cover
degree gives `-π²`.

The informal source's hint `vol B⁴ = π⁴/2` is itself a typo; its solution uses
the correct `π²/2`.  This does not require a Lean hypothesis.

I did not include `Refute.lean`: a genuinely unconditional compiled refutation
of the old theorem would itself require the missing numerical theorem for raw
Hausdorff mass.  The normalization calculation above is the exact hand
counterexample, not an assumption smuggled into the repaired theorem.

Degenerate checks: the sphere has fixed radius one and is nonempty; there is no
zero-radius case.  The antipodal action negates both the odd coefficient and
the normal factor, so the density is invariant.  At the coordinate poles
`±e₀` its value is `-4`, consistently on both representatives.  The odd mixed
term vanishes under reflection of coordinate zero, while the four square
moments sum to total mass.

The imported files `ConstructionTargets/IntrinsicSphereFinite.lean` and
`ConstructionTargets/IntrinsicSphereSecondMoments.lean` contain no `sorry`.
Their raw symmetry and integrability work is reused rather than reproved.

## Definitions and already proved steps

All definitions preceding the theorem are copied from `Main.lean`, except for
the repaired measure.  Antipodal invariance, existence and uniqueness of the
represented form, and the pointwise density expansion retain their compiled
proofs.  The quotient representation makes descent and uniqueness elementary;
it does not assume the integral result.

## Remaining lemmas

### `t95J05_euclideanHausdorff_unitSphere_mass` — LIBRARY

**Statement in words.** The normalized three-dimensional Euclidean Hausdorff
mass of the unit sphere in `ℝ⁴` is `2π²`.

**Why true.** Cover `S³` by its upper and lower graph charts over the unit
three-ball; the equator is `μHE[3]`-null.  Transport normalized Euclidean
Hausdorff measure through the graph charts, whose density is
`1 / sqrt (1-‖x‖²)`, and evaluate the radial ball integral.  Equivalently, a
proved polar/coarea comparison with four-dimensional volume and
`vol(B⁴)=π²/2` gives the same value.  Relevant Mathlib APIs are
`Measure.euclideanHausdorffMeasure_def` and
`EuclideanSpace.euclideanHausdorffMeasure_eq_volume`.

This is the large missing library result.  The closest sorry-free construction
files are `ConstructionTargets/SphereCapNullEquatorMeasureAssembly.lean`,
`SphereCapHausdorffTransport.lean`, and `SphereCapGraphDensity.lean`.  The
two-dimensional analogue, including all chart assembly and scalar conversion,
is compiled in `holes/labs/blueprints/t02A05/Blueprint.lean`; the required
program is its dimension-three generalization (Euclidean `S³` surface-mass
normalization).

**Expected size.** 120–220 lines using the existing cap infrastructure; mark
as a shared LIBRARY program rather than splitting the coarea argument into
fake consumer lemmas.

**Dependencies.** Mathlib and the cited sphere-cap construction targets only.

**Truth check.** The classical formula
`area(S³)=4·vol(B⁴)=4·(π²/2)=2π²`; radius scaling predicts `2π² r³`, including
zero at `r=0` and the stated value at `r=1`.

### `t95J05_inclusionPullback_integral`

**Statement in words.** Assuming only the preceding numerical normalized mass
equality, the repaired sphere integral of the explicit density is `-2π²`.

**Why true.** Rewrite the density with
`t95J05InclusionPullback_expand`, expand `μHE[3]` as its scalar multiple of
raw `μH[3]`, and apply the sorry-free theorem
`ConstructionTargets.IntrinsicSphereSecondMoments.projective_density_moment`.
That theorem already proves the mixed moment is zero and each coordinate
square contributes one quarter of raw mass.  Associativity of scalar
multiplication converts “minus raw mass” to “minus normalized mass”; use the
supplied `hmass` and ring normalization.

The mass conclusion is deliberately passed as a hypothesis.  This lets a
lemma seat prove the scalar/moment adapter in parallel with the LIBRARY seat,
without assuming its own conclusion.

**Expected size.** 30–50 lines.

**Dependencies.** The definitions, the stated `hmass` hypothesis, and
`ConstructionTargets.IntrinsicSphereSecondMoments.projective_density_moment`.

**Truth check.** Reflection in coordinate zero negates `x₁³x₀`, so that term
integrates to zero.  Permutation symmetry gives
`∫x₀² = mass/4`; multiplying by `-4` gives exactly `-mass`, hence `-2π²` under
the hypothesis.

## Assembly and dependency layers

The main theorem has no `sorry`.  It uses the already proved unique descent,
rewrites by the pullback equality, applies the integral lemma to the mass
lemma, and finishes the factor `1/2` by `ring`.

* **Layer 1 (parallel):**
  `t95J05_euclideanHausdorff_unitSphere_mass` (LIBRARY) and
  `t95J05_inclusionPullback_integral` (given the mass equality as a hypothesis).
* **Layer 2 (already compiled):** `apm_t95j05` assembly.

## Compilation and axioms

Both files compiled with the required 12 GiB systemd scope.  The output of
`#print axioms apm_t95j05` is:

```text
'apm_t95j05' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

Thus `sorryAx` reaches the repaired theorem only through the two named
top-level lemmas.
