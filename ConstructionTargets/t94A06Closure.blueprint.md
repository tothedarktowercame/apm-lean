# Blueprint for t94A06

## Triage and repair

Verdict: **the registered statement is false; the repaired statement is true and
faithful**.

The source says that `X` is a smooth manifold in the standard
finite-dimensional sense.  The Lean statement allowed an arbitrary normed
model space `E`.  This is a genuine strengthening, not merely missing library
data: Sard's theorem fails on infinite-dimensional Hilbert manifolds.

A counterexample is supplied by Kupka's smooth map `k : ℓ² → ℝ` whose set
of critical values contains `[0,1]`.  Take

`X = ℓ² × ℓ²` and `f(x,y) = (k(x), k(y), 0)`.

For every translation parameter in `-([0,1] × [0,1])`, the translated map
meets the z-axis at a point where neither normal coordinate has a surjective
differential.  The bad set therefore has positive two-dimensional measure,
contradicting the almost-everywhere conclusion.  This is the counterexample
recorded by the statement-registry grader.  A compiled `Refute.lean` is not
included because the required Kupka map and its analytic construction are not
formalized in Mathlib; encoding its existence as an axiom would not constitute
a Lean refutation.

`RevisedMain.lean` makes the smallest repair: it adds
`[FiniteDimensional ℝ E]` and changes nothing else in the theorem.  This is
exactly the finite-dimensional convention used by `problem.md`, and it blocks
the counterexample because `ℓ²` is infinite-dimensional.  No hypothesis
carries any transversality or regular-value content.

I also checked the principal degeneracies.  If `X` is empty, every slice is
vacuously transverse.  If `E` has dimension zero or less than two, Sard still
says that the image of the normal-coordinate map is null, so almost every
translation misses the axis.  Constant `f` has exactly one bad normal
translation, again a null set.  Parameters on coordinate axes introduce no
special endpoint because the parameter space is all of `ℝ²`.

## Definitions and reduction

`apm_t94a06_normalPart f` is the map formed from coordinates zero and one of
`f`.  The identity

`family f s x ∈ zAxis  ⇔  normalPart f x = -s`

reduces the result to regular values of `normalPart f`.  Surjectivity of its
derivative is equivalent to the image of `df` plus the z-axis direction being
all of `ℝ³`.  Translation does not change the derivative; the latter fact is
already proved in `apm_t94a06_mfderiv_family`.

## Remaining lemmas

### `apm_t94a06_ae_regularValue_normalPart` (LIBRARY)

**Statement in words.** For a smooth map from a second-countable manifold with
finite-dimensional model space into `ℝ³`, almost every value in `ℝ²` is a
regular value of its first-two-coordinate map.

**Why true.** The coordinate projection is continuous linear, hence the normal
part is smooth.  Apply the manifold-with-corners Morse–Sard theorem in local
charts.  Each chart's critical image is null by finite-dimensional Euclidean
Morse–Sard; second countability supplies a countable chart cover, and a
countable union of null sets is null.  Boundary charts cause no new issue:
extend the smooth chart representative to an open neighborhood as provided by
the `ContMDiff` definition and apply Sard there.

The closest existing sorry-free infrastructure is the large family of
`ConstructionTargets/Sard*.lean` Euclidean nullity components.  It does not yet
export the required general manifold-with-corners theorem.  Likewise,
`ConstructionTargets/IncidenceParameterProjection.lean` proves the regularity
equivalence for self-model, boundaryless incidence manifolds, so it cannot
directly discharge this statement.  This lemma is therefore deliberately a
single **LIBRARY** obligation rather than a fictitious split of the Sard
program.

**Expected size.** 300+ lines (library program).

**Dependencies.** Definitions only.

**Truth check.** For a constant map the critical-value set is a singleton; for
zero-dimensional or one-dimensional source it is contained in the image,
which has planar measure zero.  The Kupka counterexample is excluded exactly
by `FiniteDimensional ℝ E`.

### `apm_t94a06_transverse_ae_of_regularValues`

**Statement in words.** Given the almost-everywhere regular-value conclusion
for the normal part, almost every normal translation is transverse to the
z-axis.

**Why true.** Negation `s ↦ -s` preserves planar null sets.  For a good value
`-s`, take an inverse-image point of the z-axis.  Use
`apm_t94a06_mfderiv_family`, compute the derivative of the coordinate
projection, and lift the two coordinate basis vectors through the assumed
surjective derivative.  Together with `EuclideanSpace.single 2 1`, these span
all three standard basis directions, proving the submodule supremum is `⊤`.

**Expected size.** 80–150 lines.

**Dependencies.** It receives the conclusion of
`apm_t94a06_ae_regularValue_normalPart` as an explicit hypothesis, so its seat
can run independently; it also uses the proved derivative-translation lemma.

**Truth check.** For `f(x) = (x₀,x₁,x₂)` the normal derivative is
surjective everywhere and every translated slice is transverse.  For constant
`f`, all parameters except the single one making the translated normal
coordinates zero miss the axis, so the implication handles the vacuous fibers
correctly.

## Dependency layers

* **Layer 1 (parallel):** the LIBRARY Morse–Sard program
  `apm_t94a06_ae_regularValue_normalPart`, and the adapter
  `apm_t94a06_transverse_ae_of_regularValues` proved from its conclusion as a
  hypothesis.
* **Layer 2 (already compiled):** `apm_t94a06` applies the two lemmas and pairs
  the result with `apm_t94a06_family_zero`.

There are **two admitted lemmas**.  The final theorem contains no direct
`sorry`.

## Compilation and axioms

Both Lean files compile with the prescribed single-file command.  The final
output of `#print axioms apm_t94a06` is:

```text
'apm_t94a06' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The `sorryAx` dependency enters only through the two top-level lemmas above.
