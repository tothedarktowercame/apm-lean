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

### `apm_t91J03_winding_two_forces_annulus_collision` — **LIBRARY** (estimated 400–700 lines)

For an embedded annular circle with homological winding of absolute value two,
there are distinct parameter points with equal first coordinate and equal
height.  Equivalently, winding two contradicts embeddedness.

Proof program: construct the universal cover `ℝ × I → Circle × I`; identify
the homological multiplier with lift displacement; show the inverse image of
the curve consists of two disjoint properly embedded lines cyclically permuted
by unit deck translation; use planar Jordan separation to linearly order those
lines from bottom to top.  Deck translation preserves the order, hence fixes
each of two lines, contradicting its transposition.  The audit decomposed this
into circle-degree/lift work (roughly 140–260 lines), planar crossing
(250–450 lines), and assembly (120–220 lines).  This exceeds a lemma-seat
session, so the blueprint exposes the single honest library boundary rather
than fake small lemmas whose proofs duplicate the same separation theory.

Truth checks: the twice-wrapped constant-height loop visibly has collisions;
the horizontal core has only one lifted line modulo deck translation and so
does not trigger the conclusion; reversing orientation changes `2` to `-2`
but `natAbs` treats both alike.  Dependencies: none at the blueprint interface.

Search record: searched all sorry-free `ConstructionTargets` modules and names
containing `annulus`, `winding`, `circle`, `lift`, `crossing`, and `rectangle`.
The closest reusable files are `CircleExponentialPathLift.lean`,
`CircleUniversalCover.lean`, `PeriodicCircleHomotopyWinding.lean`, and
`CircleSingularHomology.lean`; none supplies the planar separation/order
theorem or the bridge from this `H₁` encoding to the full annular collision.
The topology STOP record and `~/notes/closer/audits/t91J03.md` identify the same
missing theorem.  No sorry-containing `ConstructionTargets` module is imported.

### `apm_t91J03_no_two_of_forced_fiber_collision` (proved, about 15 lines)

Given the collision theorem as a hypothesis, obtain the two points and apply
`apm_t91J03_height_ne_of_circleMap_eq`.  This is copied from frozen
`Main.lean` and compiles without `sorry`.

Truth check: direct propositional composition of the preceding conclusions.
Dependency: `apm_t91J03_height_ne_of_circleMap_eq`.

## Dependency layers

- Layer 1 / program: `apm_t91J03_winding_two_forces_annulus_collision`.
- Already proved and independent bookkeeping:
  `apm_t91J03_height_ne_of_circleMap_eq`.
- Layer 2 (already proved):
  `apm_t91J03_no_two_of_forced_fiber_collision`, followed by the five-line
  frozen theorem.

There is one remaining sorry-bearing lemma (the LIBRARY boundary), and three
top-level supporting lemmas total.  The main theorem has no `sorry`.

## Axiom check

```text
'apm_t91j03' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```
