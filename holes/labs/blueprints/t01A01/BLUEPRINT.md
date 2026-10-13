# Blueprint for t01A01

## Triage

Verdict: **true and faithful**.  The registered type uses the quotient-topology
`Projectivization ℝ (Fin 3 → ℝ)` for `RP²`, assumes exactly that the continuous
self-map is not surjective, asserts pointwise triviality of every based induced
fundamental-group map, and asserts a free null-homotopy.  These are the two
conclusions in `problem.md`.

I first checked the usual degeneracies.  `RP²` is nonempty, so the empty-domain
shortcut is unavailable.  A constant map is nonsurjective and satisfies both
conclusions.  The identity map is surjective, so it is not a counterexample.
For a general nonsurjective map, choosing a missed point makes the codomain a
punctured `RP²`, which deformation retracts to `RP¹ ≃ S¹`.  A map from `RP²`
to the circle induces a homomorphism `Z/2 → Z`, hence the zero homomorphism;
lifting to `ℝ` then gives the null-homotopy.  This is also the hand proof that
establishes the registered conclusion.

The solve-loop and topology ledgers record no counterexample.  They agree that
the statement is faithful and that the stalled boundary is construction of the
punctured-projective-plane geometry in Lean, not a defect in the theorem.

## Reused, already proved declarations

`apm_t01A01_factor_through_complement` selects a missed point and packages the
map with subtype codomain.  `apm_t01A01_nullhomotopic_of_factor` composes a
null-homotopy of this factor with the subtype inclusion.  Both are copied from
the current compiled `Main.lean` and contain no `sorry`.

The blueprint imports the sorry-free modules
`ConstructionTargets.ProjectiveSpaceTopology`,
`ProjectiveQuotientDescent`, `RealProjectiveSmoothTarget`,
`SimplyConnectedOpenCover`, `CircleUniversalCover`, and
`ComponentRealLiftAssembly`.  They supply the existing quotient, sphere,
circle-cover, lifting, and component-assembly infrastructure, but do not supply
the missing punctured-`RP²` retraction.

## Remaining lemmas

### `apm_t01A01_punctured_homotopyEquiv_projectiveLine` — LIBRARY

**Statement.** The complement of any `q : RP²` is homotopy equivalent to
`RP¹ = Projectivization ℝ (Fin 2 → ℝ)`.

**Proof route (120–150 lines).** Choose a nonzero representative of `q`, extend
its normalized vector to an orthogonal basis, and conjugate by the resulting
linear isometry so that `q` is the last coordinate line.  On nonzero vectors
not on that line, contract the last coordinate linearly to zero while retaining
the first two coordinates.  Descend the endpoint map with
`ProjectiveQuotientDescent.projectiveHomogeneousMapDescent` and the homotopy with
`ProjectiveQuotientDescent.projectiveHomogeneousHomotopyDescent`; their proofs
already use `projectiveQuotientMap_isOpen` and
`projectiveQuotientMap_prod_interval_isOpenQuotient`.  Package the inclusion,
projection, and descended homotopies as `ContinuousMap.HomotopyEquiv`.

**Truth/edge checks.** The first-two-coordinate vector is nonzero precisely
because the deleted point is the last coordinate line, so normalization has no
zero denominator.  At time zero the descended map is the identity and at time
one it lands on the projective line.  Scalar multiples give scalar multiples
at every time, including negative scalars, so quotient descent is well-defined.
The construction also works at points already on the core and fixes them.

### `apm_t01A01_projectiveLine_map_nullhomotopic` — LIBRARY

**Statement.** Every continuous `RP² → RP¹` map is freely null-homotopic.

**Proof route (120–150 lines).** Identify `RP¹` with `Circle` (the angle-doubling
map on the unit circle is invariant under antipodes).  Pull the map back along
`RealProjectiveSmoothTarget.sphereProjection 2`.  Use
`SimplyConnectedOpenCover.simplyConnectedSpace_sphere_of_pole` and
`CircleUniversalCover.circleCover_isCoveringMap` to obtain a real lift.  Compare
the lift at antipodal points using `CircleUniversalCover.circleCover_eq_iff` and
`period_integer_unique`.  Connectedness makes the integer difference constant;
applying the antipodal involution twice makes it its own negative, hence zero.
Descend the invariant lift with
`ProjectiveQuotientDescent.projectiveHomogeneousMapDescent`, contract it linearly
in `ℝ`, and use `ComponentRealLiftAssembly.nullhomotopic_of_component_lifts` (or
its `classical_component_lifts_nullhomotopic` wrapper).

**Truth/edge checks.** The only homomorphism `Z/2 → Z` is zero.  The integer
obtained from antipodal lift comparison cannot be a nonzero two-torsion integer.
No basepoint choice is hidden: the result is a free homotopy.  Constant maps
lift constantly and reduce to reflexivity.  `RP²` and `RP¹` are nonempty, so the
chosen endpoint exists.

### `apm_t01A01_nullhomotopic_of_target_homotopyEquiv` — LIBRARY

**Statement.** If `e : Y ≃ₕ Z` and `e ∘ g` is homotopic to a constant, then
`g : X → Y` is homotopic to a constant.

**Proof route (30–50 lines).** Postcompose the supplied homotopy with
`e.invFun`, using `ContinuousMap.Homotopic.comp`, and concatenate it with
`e.left_inv` precomposed by `g`.  Simplify both composites and choose
`e.invFun p` as the constant value.  Useful APIs are
`ContinuousMap.Homotopic.comp`, `.trans`, `.refl`, and
`ContinuousMap.HomotopyEquiv.left_inv`.

**Truth/edge checks.** This is valid for empty `X` as well as nonempty `X`; no
point of `X` is selected.  It does not assume that a homotopy equivalence is a
homeomorphism.  The conclusion's constant is explicitly the inverse image of
the supplied constant point.

### `apm_t01A01_punctured_factor_nullhomotopic` — assembly

Obtain the punctured-target homotopy equivalence, apply the independent
projective-line lemma to `e.toFun.comp g`, and invoke the abstract transport
lemma.  This proof is sorry-free.  The three LIBRARY leaves are mutually
independent: the transport leaf receives both `e` and the null-homotopy as
explicit hypotheses, and neither geometric leaf mentions the other.

### `apm_t01A01_piOne_trivial_of_nullhomotopic`

**Statement in words.** For arbitrary topological spaces, a continuous map
freely homotopic to a constant sends every fundamental-group element, at every
basepoint, to the identity.

**Why true.** Use
`FundamentalGroupoidFunctor.homotopicMapsNatIso` on the homotopy.  Naturality
identifies the two induced loop morphisms up to conjugation by the component of
the natural isomorphism.  The constant map sends every loop to the constant
loop, hence to `1`; conjugating `1` still gives `1`.  Quotient induction on the
fundamental-group element is an alternative direct proof.

**Expected size.** 30–60 lines.

**Dependencies.** Only Mathlib; independent of the LIBRARY lemma.

**Truth check.** For `γ = 1`, both sides reduce to `1`.  If `X` is empty the
universal quantification over `x` is vacuous.  If `f` itself is constant, the
claim follows directly because every composed loop is constant.  Free rather
than pointed homotopy only introduces conjugation, which cannot change the
identity.

## Assembly

After factorization, the LIBRARY lemma supplies a null-homotopy in the punctured
codomain.  The proved descent lemma turns this into a null-homotopy of `f` in
`RP²`.  The generic fundamental-group lemma supplies the first conjunct, and
the same homotopy supplies the second.  The main theorem contains no `sorry`.

## Dependency layers

* **Layer 1 (parallel):**
  `apm_t01A01_punctured_factor_nullhomotopic` (LIBRARY),
  `apm_t01A01_piOne_trivial_of_nullhomotopic`.
* **Layer 2 (already compiled):** factor/descent and the final theorem assembly,
  after the two Layer 1 lemmas are supplied.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t01A01/Blueprint.lean
```

The two warnings are exactly the two top-level Layer 1 lemmas.  The final output
of `#print axioms apm_t01a01` is:

```text
'apm_t01a01' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```
