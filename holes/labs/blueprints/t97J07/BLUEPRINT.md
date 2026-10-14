# Blueprint for t97J07

## Triage and repair

Verdict: **unfaithful (repair required), but not refuted**.

The registered theorem correctly describes the fixed locus, chart maps,
derivatives, determinant signs, component contributions, and the arithmetic
identity `2 + 1 = 3`.  It does not state part (c) of `problem.md`:

> Use this to compute the Euler characteristic of \(\mathbb{CP}^2\).

In particular, the old last conjunct mentions no topology, homology, or Euler
characteristic; replacing every preceding geometric definition by unrelated
data with the same two integer values would leave that conjunct unchanged.
This is an omission rather than a false proposition, so there is no
`Refute.lean`.

The repair follows the statement-registry recommendation.  It gives
`T97J07CP2` the explicit quotient topology already defined by
`ConstructionTargets.ProjectiveSpaceTopology.Space ℂ 2` (definitionally the
same underlying projectivization), imports
`ConstructionTargets.RationalLefschetz`, and adds the final conjunct

```lean
ConstructionTargets.RationalLefschetz.HasEulerCharacteristic T97J07CP2 3
```

This predicate is the finite alternating trace of the identity on actual
rational singular homology.  Thus it cannot be satisfied merely through a
default trace on infinite-dimensional modules.  Together with the immediately
preceding local-contribution equality, it says the computed total and the
Euler characteristic both equal 3.  No hypothesis was added.

The registry supplied no counterexample to check because its objection was
missing content.  I did check the usual degeneracies: projective space has no
zero-vector point; the repeated eigenvalue 1 produces a whole projective line,
not two isolated coordinate points; and the eigenvalue 3 produces a point
outside that line.  The determinant values are positive and nonzero, so neither
index is accidentally the zero branch.  All of these checks agree with the
compiled elementary lemmas copied into `Blueprint.lean`.

No matching t97J07 entry was present in the canonical topology worklists or
audit directory at the time of inspection.  The solve-loop's remaining
recorded obstruction is the fixed-set classification already isolated below.

## Reused compiled work

All definitions and all elementary results from `Main.lean` are copied with
their complete proofs: the two affine chart identities, exclusion of the
isolated point from the line, both derivative calculations, both determinant
calculations, both indices, the line contribution, and the total
`2 + 1 = 3`.  None needs a lemma seat.

## Remaining lemmas

### `t97J07_fixed_set`

**Statement in words.** The fixed points of the projectivization of
`diag(1,1,3)` are precisely the projective line with third coordinate zero
together with the third coordinate axis.

**Why true.** For a fixed projective class `p`, use
`Projectivization.mk_rep`, `Projectivization.map_mk`, and
`Projectivization.mk_eq_mk_iff'` to obtain a nonzero scalar relating
`t97J07Linear p.rep` to `p.rep`.  Inspect coordinates 0, 1, and 2.  If the
third coordinate is zero, the point is in `t97J07FixedLine`.  Otherwise the
scalar is forced to be 3, and the first two coordinates vanish, after which
`mk_eq_mk_iff'` identifies the class with
`t97J07IsolatedPoint`.  Conversely, points on the line and the isolated
point are fixed by direct projective equality.

**Expected size.** 40–90 lines.

**Dependencies.** Definitions only; no other sorry lemma.

**Truth check.** Hand calculation of the eigenvectors gives
`z₂ = 0` for eigenvalue 1 and `z₀ = z₁ = 0` for eigenvalue 3.  The zero
vector cannot represent a projective point.  The already proved
`t97J07IsolatedPoint_not_mem` checks that the two pieces do not collapse.

### `t97J07_cp2RationalHomologyData_exists` — LIBRARY

**Statement in words.** For the literal quotient-topological `CP²`, rational
singular homology is finite-dimensional in every degree, vanishes above degree
4, is zero in degrees 1 and 3, and is linearly equivalent to `ℚ` in degrees
0, 2, and 4.

**Why true.** Use the CW filtration
\(\mathbb{CP}^0\subset\mathbb{CP}^1\subset\mathbb{CP}^2\), with one cell in
each real dimension 0, 2, and 4.  For an implementation using present
repository foundations, construct the filtration by the last homogeneous
coordinate, identify each relative pair with `(D^(2n), S^(2n-1))`, and apply
the pair long exact sequence and excision.  Relevant declarations include
`Projectivization.mk_rep`, `Projectivization.mk_eq_mk_iff'`,
`ConstructionTargets.SingularHomologyConcrete.singularPairHomology_exact_subspace`,
`singularPairHomology_exact_absolute`, `singularPairHomology_exact_relative`,
and the excision comparison in `ConstructionTargets.SingularExcision`.

Mathlib does not currently provide this projective-space homology computation.
`ProjectiveSpaceTopology` supplies the exact quotient space and
`RationalLefschetz` supplies the honest Euler-characteristic predicate, but
the cellular/singular comparison is absent.  This is deliberately the one
marked LIBRARY obligation rather than several small statements that each hide
the same missing foundation.

**Expected size.** 300+ lines / topology construction program.  It is the one
knowingly over-seat-sized leaf, as required for a genuinely missing large
foundation.

**Dependencies.** Definitions only at statement level; no other sorry lemma.
Its eventual proof will likely need imports of the concrete homology and
excision targets named above.

**Truth check.** The standard CW decomposition has exactly one cell in
dimensions 0, 2, and 4 and none in odd dimensions.  For boundary sanity, it
gives 1 for `CP⁰` and 2 for `CP¹`, agreeing with a point and a 2-sphere.

### `t97J07_eulerCharacteristic_of_homologyData`

**Statement in words.** Any supplied `T97J07CP2RationalHomologyData`
certificate implies that `CP²` has rational Euler characteristic 3.

**Why true.** Unfold `RationalLefschetz.HasEulerCharacteristic` and
`HasLefschetzNumber`, choose bound 4, and install
`h.finiteDimensional k` locally.  Functoriality sends `ContinuousMap.id` to
the identity; use `CategoryTheory.Functor.map_id` (often `simp` after
unfolding `RationalLefschetz.induced`).  In degrees 1 and 3 use the trace-zero
lemma for a subsingleton module.  In degrees 0, 2, and 4 transport trace across
`h.zeroEquiv`, `h.twoEquiv`, and `h.fourEquiv`, using `LinearMap.trace_id` and
trace invariance under linear equivalence.  Then `norm_num` evaluates the
five-term alternating sum.

**Expected size.** 50–120 lines.

**Dependencies.** The homology result is an explicit hypothesis, so this leaf
is independent of `t97J07_cp2RationalHomologyData_exists` and `t97J07_fixed_set`.

**Truth and degeneracy checks.** The bound is inclusive: `range (4 + 1)`
contains 0 through 4, while `h.vanishesAbove` handles strictly larger degrees.
Odd degrees contribute zero; all surviving degrees are even and have sign
`+1`.  Explicit finite-dimensionality prevents the default trace on an
infinite-dimensional space from making the claim vacuous.

### `t97J07_eulerCharacteristic` (assembly)

This is sorry-free and applies
`t97J07_eulerCharacteristic_of_homologyData` to
`t97J07_cp2RationalHomologyData_exists`.

## Assembly and dependency layers

- **Layer 1 (parallel):** `t97J07_fixed_set`, the LIBRARY leaf
  `t97J07_cp2RationalHomologyData_exists`, and the hypothesis-driven algebra leaf
  `t97J07_eulerCharacteristic_of_homologyData`.
- **Layer 2 (sorry-free):** `t97J07_eulerCharacteristic` applies the algebra
  leaf to the homology certificate.
- **Layer 3 (already proved):** `apm_t97j07` combines those results with
  the copied elementary lemmas.  Its body contains no `sorry`.

All three Layer 1 statements share no unproved dependency.  In particular,
the algebra leaf receives the LIBRARY conclusion as an explicit hypothesis.

## Compilation and axioms

Both files compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t97J07/RevisedMain.lean
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t97J07/Blueprint.lean
```

The final output of `#print axioms apm_t97j07` was:

```text
'apm_t97j07' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The two `sorry` warnings in `Blueprint.lean` are exactly the two Layer 1
lemmas.  The final theorem has no direct `sorry`.
