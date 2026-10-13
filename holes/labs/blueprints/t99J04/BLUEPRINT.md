# Blueprint for t99J04

## Triage

Verdict: **true and faithful**.

The registered theorem says exactly the two claims in `problem.md`: independent
differentials of `n` scalar functions on an `n`-manifold give local
coordinates, and a smooth map from a nonempty compact manifold to a connected
manifold is surjective when every derivative is invertible.  The source has a
typo (“`X` in an `n`-dimensional manifold”) which the registered statement
correctly reads as “`X` is an `n`-dimensional manifold.”  The explicit
`Nonempty X` in part (b) is necessary: the empty compact manifold would
otherwise map to a nonempty connected manifold without being surjective.

Degenerate checks:

* For `n = 0`, `Fin n` is empty, so linear independence is vacuous.  Both the
  model tangent space and `EuclideanSpace ℝ (Fin 0)` are zero-dimensional, and
  the unique derivative is bijective.  The local inverse theorem therefore
  still gives the claimed zero-dimensional local chart.
* A constant map in positive dimension has zero derivative and cannot satisfy
  the bijectivity/independence hypotheses.  In dimension zero it is locally a
  diffeomorphism, as required.
* Compactness alone does not make the image all of `Y`; connectedness and the
  open image supplied by local invertibility are both genuinely used.

The topology worklist and `~/notes/closer/audits/t99J04.md` agree that the
statement is faithful.  They identify the same missing API boundary as this
blueprint: Mathlib has the Banach-space inverse theorem but not the converse
manifold theorem `ContMDiffAt + bijective mfderiv → IsLocalDiffeomorphAt`.

## Reused completed work

Three declarations from the solve-loop file are copied with their compiled
proofs:

* `apm_t99J04_dualCoordinates_bijective` upgrades `n` independent covectors
  on an `n`-dimensional space to a bijective coordinate linear map;
* `apm_t99J04_surjective_of_isLocalDiffeomorph` proves the open-and-closed
  compactness argument; and
* `apm_t99J04_surjective_of_bijective_mfderiv_of_localIFT` packages the whole
  second conjunct once the local inverse theorem is available.

No sorry-free `ConstructionTargets` module supplies the remaining manifold
inverse theorem.  `ConstructionTargets/t99J04Closure.blueprint.md` is only a
program description, not an importable implementation, so the blueprint uses
the same theorem form expected by that closure program.

## Remaining lemmas

### `apm_t99J04_bridge_local_inverse_function` — LIBRARY

**Statement in words.** On finite-dimensional complete real normed model
spaces, a smooth manifold map with bijective manifold derivative at a point is
a local diffeomorphism there.

**Why true.** Pass to `writtenInExtChartAt`.  The self-model `mfderiv` formula
identifies its Fréchet derivative with the given derivative up to the chart
linear equivalences.  Apply `ContDiffAt.toOpenPartialHomeomorph`, shrink to a
neighborhood on which the forward map is smooth, use
`OpenPartialHomeomorph.contDiffAt_symm` for the inverse, and package the
chart-conjugated local equivalence as one `PartialDiffeomorph`.  The detailed
route is recorded in `holes/labs/topology-routes/reroute-t99J04.md`; Mathlib's
`Geometry.Manifold.LocalDiffeomorph` explicitly leaves this converse as a
TODO.

**Expected size.** 200–350 lines.  This is marked LIBRARY because it is the
substantial missing Mathlib-level construction, not a problem-specific
adapter.  It is the principal target of the `t99J04Closure` program.

**Dependencies.** Definitions only; independent of the two coordinate-map
lemmas.

**Truth check.** For `X = Y = ℝ` and `f = id`, the derivative is the identity
and the identity local diffeomorphism witnesses the conclusion.  A constant
positive-dimensional map fails the bijectivity hypothesis.  In dimension zero
the unique linear map is bijective and manifolds are locally discrete, so the
conclusion remains correct.

### `apm_t99J04_coordinateMap_contMDiff`

**Statement in words.** A finite tuple of smooth real-valued functions is a
smooth map into the Euclidean `WithLp` model.

**Why true.** First apply `contMDiff_pi_space` to the map
`p ↦ fun i ↦ f i p`.  Then compose with the continuous linear equivalence
between `(Fin n → ℝ)` and its `WithLp 2` copy (`WithLp.linearEquiv` and its
continuous-linear packaging in `Mathlib.Analysis.Normed.Lp.PiLp`).

**Expected size.** 30–60 lines.

**Dependencies.** Definitions only.

**Truth check.** For `n = 0` this is the unique map to the one-point vector
space and is smooth.  For `n = 1` it is just the given scalar function through
a continuous linear equivalence.

### `apm_t99J04_bridge_coordinateMap_mfderiv_bijective`

**Statement in words.** Assuming the coordinate map is smooth, linear
independence of its scalar component derivatives makes its manifold derivative
bijective.

**Why true.** Compute the `mfderiv` componentwise using the derivative rule
for a finite Pi-valued map, then transport through `WithLp.toLp`.  For `n > 0`,
identify the component covectors with the family in the hypothesis and invoke
the already proved `apm_t99J04_dualCoordinates_bijective`.  Handle `n = 0`
separately: source and target tangent/model spaces have finrank zero, so the
derivative is bijective.  The `hcoord` hypothesis is deliberately the
conclusion of the preceding lemma, allowing this seat to assume that interface
and proceed independently.

**Expected size.** 100–200 lines.

**Dependencies.** The proved dual-coordinate lemma and the *statement* of
`apm_t99J04_coordinateMap_contMDiff`, supplied as the explicit `hcoord`
hypothesis.

**Truth check.** For the standard coordinates `f i p = p i`, the derivative
is the identity.  For `n = 0`, both spaces have one element and the unique map
is bijective.  Duplicated positive-dimensional coordinates fail linear
independence, so the statement does not assert a false conclusion there.

## Dependency layers

* **Layer 1 (all seats may run in parallel):**
  `apm_t99J04_bridge_local_inverse_function` (LIBRARY),
  `apm_t99J04_coordinateMap_contMDiff`, and
  `apm_t99J04_bridge_coordinateMap_mfderiv_bijective`.  The third theorem
  receives the smoothness conclusion as an explicit hypothesis, so it does not
  need the preceding theorem's proof in its seat file.
* **Layer 2 (already compiled, no seat):** the main theorem applies coordinate
  smoothness and derivative bijectivity to the LIBRARY inverse theorem for
  part (a), and applies the same inverse theorem followed by the completed
  compact-open-closed argument for part (b).

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t99J04/Blueprint.lean
```

The final output of `#print axioms apm_t99j04` was:

```text
'apm_t99j04' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The three warnings are exactly the three top-level lemmas listed above.  The
main theorem contains no `sorry`; its `sorryAx` dependency is inherited only
through those lemmas.
