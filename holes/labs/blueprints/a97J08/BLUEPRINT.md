# Blueprint for a97J08

## Triage

**Verdict: true and faithful.** The Lean theorem encodes the source statement's rectifiable Jordan curve by continuity on `[0,1]`, equal endpoints, injectivity on `[0,1)`, and bounded variation. Its `curveInterior` is the union of bounded complementary components, and `zeroCount` uses the positive part of the meromorphic divisor, so multiplicity is retained.

The usual degenerate failures are excluded. A constant curve cannot satisfy the stated injectivity. If the encoded interior is empty, both zero counts are zero. The hypotheses that `g` is nonzero on the curve and that the convergence is locally uniform are exactly those needed for the eventual Rouché inequality. As a topology check, an annulus has a bounded complementary component and its central circle is visibly noncontractible, whereas the complement of a disk has no bounded component. The missing planar lemma also becomes vacuous for an empty domain.

The 2026-08-26 classification was accurate: the missing construction is a loop in an open planar domain which surrounds a bounded connected component of its complement. The current file already defines the radial map from the domain to `Circle` and proves that a circle admitting the required degree-one homotopy certificate is non-nullhomotopic. I searched the current Mathlib tree for Alexander duality, planar/Jordan separation, Schoenflies, surrounding loops, and bounded-complement-component results. No theorem presently supplies this construction. Thus the construction remains blocked at the library level, not at the later analytic argument.

## Definitions and proved infrastructure

`Blueprint.lean` retains the definitions and every proved lemma from `problems/a97J08/lean/Main.lean`. In particular, it already proves compactness and boundary estimates, locally uniform limit analyticity, disk-wise Rouché transfer, finite divisor decomposition and additivity, conversion of noncontractible circles to essential based loops, and the final zero-count assembly. The main theorem contains no `sorry`.

## Parallel grid proof

The revised specifications carry a finite square region and a finite family
of oriented boundary loops. No assertion identifies the entire frontier with
one injective circle. This is essential when the pixelated region is an
annulus or has several boundary components.

### `apm_a97j08_clopen_separation_of_bounded_component`

**Statement.** A bounded component `K` can be separated, inside a sufficiently
large compact truncation of `Dᶜ`, into compact pieces `A,B` with `K⊆A`,
`z∈A`, and positive distance between them. **Sketch.** Components equal
quasi-components in compact Hausdorff spaces. Choose the clopen partition in
`Dᶜ∩closedBall(0,R)` after taking `R` beyond `K`; compact disjoint pieces
have positive distance. **Estimate:** 70–120 lines. **Dependencies:** proved
compactness of `K`. **Truth check:** for an annulus, `A` is the inner disk and
`B` is the exterior portion of the truncation. If `B=∅`, any positive
separation constant works vacuously.

### `apm_a97j08_grid_region_construction` (G1)

**Statement.** From the separated input, produce a finite union `U` of closed
shifted grid squares with `A⊆interior U`, `U∩B=∅`, `U⊆closedBall(0,R)`, and
with `z` on no grid line. **Sketch.** Choose the mesh below half the separation
and shift the grid generically; compactness makes the set of squares finite.
**Estimate:** 90–140 lines. **Dependencies:** the
separation conclusion is an explicit hypothesis, so this seat is independent.
**Truth check:** for `A` a circle separated from `B={0}`, `U` is correctly an
annulus, not a disk; a one-square compactum gives one square.

### Revision v3 (2026-10-13, claude-14): grid winding by angle steps

The v2 split was unsound as a parallel plan. `IsOrientedGridBoundary C` was
*defined* as `∑ winding = 1`, so G3 was vacuous, and G2 had to produce the
whole boundary-loop family together with sum one and a soundness certificate:
all of the Jordan-type content in one seat. `GridInput` also let `A` touch the
truncation sphere, and then G1 is false. `GridInput` now requires
`A ⊆ ball 0 (R - δ)`; the clopen separation can supply this because the
sphere slice is compact and disjoint from the component.

G2–G4 are replaced by thirteen statements, each with a consumer that takes
its suppliers as hypotheses. The assembly
`apm_a97j08_exists_noncontractible_circle_of_bounded_compl_component` is
proved from them.

Notation: lattice vertices `ℤ × ℤ` ↦ `gridVertex shift δ`; a square has its
four counterclockwise edges `squareEdges q`; `boundaryEdges Q` are the square
edges whose reverse is not a square edge; `angleStep z p q = arg((q-z)/(p-z))`
is the exact angle swept along `[p, q]` when the segment misses `z`;
`cycleEdges c = c.zip (c.rotate 1)`.

| id | lemma | content | kind |
|---|---|---|---|
| A1 | `angleStep_swap` | `arg` of the inverse; the ratio is not a negative real since `z ∉ [p,q]` | complex analysis, short |
| A2 | `squareSum_outside` | `z` outside a convex square: all vertices lie in an open half-plane at `z`, so the steps telescope to 0 | planar geometry |
| A3 | `squareSum_inside` | `z` inside: four steps in `(0, π)` summing to a multiple of `2π`, hence `2π` | planar geometry |
| A4 | `edgeAngle_swap` | lattice edges lie on grid lines, which `z` avoids; apply A1 | short |
| C1 | `boundary_sum` | distinct squares share no oriented edge; interior edges cancel in pairs | finite combinatorics |
| C2 | `boundary_balanced` | apply C1 to `[e.1 = v] - [e.2 = v]` | finite combinatorics |
| C3a | `exists_simple_cycle` | follow out-edges in a balanced finite edge set until a vertex repeats | graph combinatorics |
| C3b | `cycle_decomposition` | peel simple cycles (C3a); balance survives removal | graph combinatorics |
| E1 | `boundaryEdge_segment_subset` | a boundary edge borders an unselected square, so it misses `interior U ⊇ A`; it lies in `U`, so it misses `B`; hence it lies in `D` | point-set topology |
| Z1 | `square_total` | `z` is in exactly one lattice square, which is selected | short |
| L1 | `segment_lift` | `θ t = arg(p-z) + arg((lineMap p q t - z)/(p-z))`; the ratio stays in the slit plane | complex analysis |
| L2 | `polygon_path_lift` | concatenate segment paths; shift each lift by a multiple of `2π` to match | paths |
| L3 | `not_nullhomotopic_of_lift` | a nullhomotopy would make the lift's displacement 0 (`PeriodicCircleHomotopyWinding`, covering lifts) | homotopy lifting |

The clopen separation and G1 keep their v2 sketches. G1 may shrink `δ` (take a
quarter of the separation as mesh and output constant), so its squares stay
inside `ball 0 R` and away from `B`.

## Dependency layers

- Layer 1, parallel: all fifteen statements. Every consumer takes its
  suppliers' conclusions as explicit hypotheses.
- Layer 2, proved: the noncontractible-circle assembly.
- Layer 3, proved: all essential-loop, simple-connectivity, and main-theorem
  consequences.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/a97J08/Blueprint.lean
```

The final command in the file prints:

```text
'apm_a97j08' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The fifteen Layer 1 lemmas are exactly the sources of `sorryAx`.

## Doubt

The grid-cycle combinatorics and winding conversion are standard and the
statements are true. The family stores integer winding coordinates together
with their radial non-nullhomotopy interpretation; current
`ConstructionTargets` exposes the latter through circle homology rather than
a packaged analytic `windingNumber`. The largest implementation risk is the
edge-cycle decomposition in G2, but it is no longer entangled with G1 or G3.
