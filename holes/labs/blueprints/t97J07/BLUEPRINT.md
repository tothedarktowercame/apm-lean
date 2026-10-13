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

### `t97J07_eulerCharacteristic` — LIBRARY

**Statement in words.** The rational singular-homology Euler characteristic
of quotient-topological complex projective two-space is 3.

**Why true.** Compute
\(H_k(\mathbb{CP}^2;\mathbb Q)\): it is one-dimensional in degrees 0, 2,
and 4 and zero otherwise.  The identity induces the identity in each degree,
whose trace is the dimension, so the finite alternating sum is
`1 + 1 + 1 = 3`.  A standard construction can use the CW filtration
\(\mathbb{CP}^0\subset\mathbb{CP}^1\subset\mathbb{CP}^2\), with one cell
in each even dimension.

Mathlib does not currently provide this projective-space homology computation.
The closest sorry-free repository foundations are
`ConstructionTargets.ProjectiveSpaceTopology`, which supplies the exact
quotient-topological space, and
`ConstructionTargets.RationalLefschetz`, which supplies the honest
finite-support/finite-dimensional Euler-characteristic predicate.  What is
missing is the cellular or singular homology computation for complex
projective space.  This is therefore deliberately one LIBRARY obligation,
not a collection of fake small lemmas.

**Expected size.** 300+ lines / topology construction program.

**Dependencies.** Definitions and the two imported sorry-free construction
targets only; it does not depend on `t97J07_fixed_set`.

**Truth check.** The standard CW decomposition has exactly one cell in
dimensions 0, 2, and 4 and none in odd dimensions, giving alternating sum 3.
For boundary sanity, the analogous decomposition gives 1 for
\(\mathbb{CP}^0\) and 2 for \(\mathbb{CP}^1\), agreeing with a point and
a 2-sphere.

## Assembly and dependency layers

- **Layer 1 (parallel):** `t97J07_fixed_set` and the LIBRARY lemma
  `t97J07_eulerCharacteristic`.
- **Layer 2 (already proved):** `apm_t97j07` combines those two results with
  the copied elementary lemmas.  Its body contains no `sorry`.

The two Layer 1 statements share no unproved dependency, so seats can work on
them independently.

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

