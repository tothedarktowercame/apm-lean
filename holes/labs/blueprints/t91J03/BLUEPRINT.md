# t91J03 blueprint

## Triage

Verdict: **true and faithful**.  The frozen Lean theorem says exactly that the
first-coordinate projection of an embedded circle in `Circle × [0,1]` cannot
act by an integer of absolute value two on integral `H₁`.

Degenerate checks: a constant map cannot satisfy `IsEmbedding`; a horizontal
core circle has winding `±1`; a small contractible embedded circle has winding
zero.  The standard map wrapping twice at constant height has the requested
winding but is not injective.  Boundary heights `0` and `1` cause no exception:
the argument is in the closed strip and deck translation preserves both edges.
The solve-loop and topology ledgers contain no counterexample and explicitly
record the statement as sound.

## Lemmas

### `apm_t91J03_height_ne_of_circleMap_eq` (proved, about 15 lines)

If two distinct parameter points of an embedded annular circle have the same
circle coordinate, their heights differ.  Otherwise `Prod.ext` and
`Subtype.ext` show that their images under `gamma` agree, contradicting the
injectivity supplied by `Topology.IsEmbedding`.  This proof is copied from the
frozen `Main.lean` and compiles without `sorry`.

Truth check: this is simply coordinate extensionality; it also covers heights
at both endpoints of `Icc 0 1`.  Dependencies: none.

### `apm_t91J03_embedded_annular_circle_homology_bound` — **LIBRARY** (estimated 300–500 lines)

For every orientation of `H₁(S¹; ℤ)`, the first projection of an embedded
circle in the annulus acts by a scalar `m` with `m.natAbs ≤ 1`.  This is the
one genuinely large missing foundation: the classification of simple closed
curves in an annulus (equivalently, the fact that an essential such curve is
primitive in homology).

Suggested proof route: use `CircleUniversalCover` and
`CircleExponentialPathLift` to lift to the closed strip; apply planar Jordan
separation to a lifted proper line and its deck translates; then use
`CircleSingularHomology` to identify deck displacement with the displayed
homology scalar.  Mathlib has `SimpleGraph.Path` and Jordan-curve results for
spheres, but no ready theorem classifying embedded circles in an annulus, so
this leaf must remain **LIBRARY** rather than hiding that foundation among
nominally small lemmas.

Truth checks: a contractible embedded circle gives `m = 0`; either orientation
of a core gives `m = 1` or `m = -1`; boundary core circles at height `0` or `1`
are included because the strip is closed.  Reversing either parametrization or
the chosen generator only changes the sign.  Dependency: none of the new
leaves.

### `apm_t91J03_rank_one_scalar_unique` (estimated 20–40 lines, independent)

If the same morphism from `H₁(S¹; ℤ)` to `ℤ` is multiplication by both
`n` and `m` relative to one orientation, then `n = m`.  Evaluate at
`orientation.inv 1`, simplify with `Iso.hom_inv_id_apply`, and cancel
multiplication by one.  Useful Mathlib lemmas: `Iso.hom_inv_id_apply`,
`mul_one`.  This leaf is purely algebraic and can be proved independently.

Truth check: the chosen orientation is an isomorphism, so its inverse image of
`1` exists even though the source is presented as a homology object; there is
no zero-module degeneracy.

### `apm_t91J03_natAbs_two_not_le_one` (estimated 5–15 lines, independent)

An integer whose `natAbs` equals two cannot have `natAbs ≤ 1`.  `omega`
should close it directly; alternatively rewrite with the equality and use
`Nat.not_succ_le_zero`.  This is independent of all topology and homology.

### `apm_t91J03_no_embedded_winding_two` (proved assembly, about 10 lines)

Unpack the orientation in `HasWindingNumber`, obtain the bounded scalar from
the classification leaf, identify it with `n` using scalar uniqueness, and
apply the arithmetic leaf.  This lemma has no `sorry` of its own.

### `apm_t91J03_winding_two_forces_annulus_collision` (proved assembly, 3 lines)

The hypotheses are inconsistent by `apm_t91J03_no_embedded_winding_two`, so
the requested collision follows by `False.elim`.  This preserves the original
registered interface while removing its `sorry`.

### `apm_t91J03_no_two_of_forced_fiber_collision` (proved, about 15 lines)

Given the collision theorem as a hypothesis, obtain the two points and apply
`apm_t91J03_height_ne_of_circleMap_eq`.  This is copied from frozen
`Main.lean` and compiles without `sorry`.

Truth check: direct propositional composition of the preceding conclusions.
Dependency: `apm_t91J03_height_ne_of_circleMap_eq`.

## Dependency layers

- Layer 1, mutually independent seats:
  `apm_t91J03_embedded_annular_circle_homology_bound`,
  `apm_t91J03_rank_one_scalar_unique`, and
  `apm_t91J03_natAbs_two_not_le_one`.
- Already proved and independent bookkeeping:
  `apm_t91J03_height_ne_of_circleMap_eq`.
- Layer 2 (sorry-free assembly): `apm_t91J03_no_embedded_winding_two` and
  `apm_t91J03_winding_two_forces_annulus_collision`.
- Layer 3 (already proved):
  `apm_t91J03_no_two_of_forced_fiber_collision`, followed by the five-line
  frozen theorem.

There are three sorry-bearing leaves, of which only the annulus-classification
leaf is large.  The original LIBRARY lemma and the main theorem have no
`sorry`.  The two small leaves are independent of the classification and of
each other.

## Axiom check

```text
'apm_t91j03' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```
