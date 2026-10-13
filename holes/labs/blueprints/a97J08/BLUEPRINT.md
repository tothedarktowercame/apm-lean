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

### `apm_a97j08_grid_boundary_cycle_decomposition` (G2)

**Statement.** Decompose the oriented exposed edges of `U` into finitely many
closed simple edge-loops, all lying in `D`, and attach their integer winding
coordinates. **Sketch.** Every grid vertex has balanced oriented incidence,
so the finite edge set splits into cycles. Boundary points avoid `A`; the mesh
and separation exclude `B`, hence the partition forces membership in `D`.
**Estimate:** 100–150 lines. **Dependencies:** region and separation are
explicit hypotheses. **Truth check:** an annulus yields two loops with
opposite boundary orientations; disconnected pixel components may yield more.

### `apm_a97j08_grid_boundary_winding_sum` (G3)

**Statement.** The sum of the winding coordinates of all oriented boundary
loops is one. **Sketch.** Sum the oriented boundaries of all selected squares;
internal edges cancel. A square contributes one exactly when it contains `z`
and zero otherwise. The shifted-grid condition gives a unique square
containing `z`. **Estimate:** 60–110 lines. **Dependencies:** the oriented
cycle certificate is explicit. **Truth check:** for an annulus around `z`,
the outer and inner boundary contributions combine to one; no individual
frontier component is selected prematurely.

### `apm_a97j08_noncontractible_circle_of_cycle_winding` (G4)

**Statement.** If a finite family of loops in `D` has winding sum one, some
loop has nonzero winding and is non-nullhomotopic in `D`. **Sketch.** If every
integer were zero their finite sum would be zero. For the chosen loop, use
the stored winding certificate and radial projection; a nullhomotopy would
remain one after composition. **Estimate:** 30–60 lines. **Dependencies:**
the family, boundary membership, and sum identity are explicit hypotheses.
**Truth check:** this works with any number of loops, including annular and
multiply connected regions; the empty family cannot have sum one.

The old `apm_a97j08_exists_noncontractible_circle_of_bounded_compl_component`
is now a proved assembly of these five statements.

## Dependency layers

- Layer 1, parallel: all five lemmas above. Every consumer takes the supplier's
  conclusion as an explicit hypothesis, so none inherits another lemma's
  `sorryAx`.
- Layer 2, proved: the former monolithic noncontractible-circle lemma.
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

The five Layer 1 lemmas are exactly the sources of `sorryAx`.

## Doubt

The grid-cycle combinatorics and winding conversion are standard and the
statements are true. The family stores integer winding coordinates together
with their radial non-nullhomotopy interpretation; current
`ConstructionTargets` exposes the latter through circle homology rather than
a packaged analytic `windingNumber`. The largest implementation risk is the
edge-cycle decomposition in G2, but it is no longer entangled with G1 or G3.
