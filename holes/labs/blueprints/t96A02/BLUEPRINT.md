# Blueprint for t96A02

## Triage

Verdict: true and faithful. `ProjectivePlaneWedge` is the point wedge of two
polygon models of `RP²`. Its positive-degree rational homology vanishes, so
every self-map has Lefschetz number one; finite-polyhedron Lefschetz then gives
a fixed point. The registered statements
`t96A02_wedge_fixed_point_of_lefschetz` and `apm_t96a02` remain byte-identical.

## Leaves

### `t96A02_wedge_lefschetz_number` — LIBRARY, 1000–2000 lines

Every self-map has rational Lefschetz number one. Use cellular/singular
comparison for the usual `RP²` complex (degree-two boundary is invertible over
`ℚ`) and the point-wedge reduced-homology sum. Independent of all
finite-polyhedron work.

C1: the `RP²` boundary is multiplication by two over `ℚ`. C2: no hypothesis.
C3: only the homology calculation. C4–C5: produces the exact predicate consumed
by the implication. C6–C7: coefficients and signs match `RationalLefschetz`.
C8: identity and constant maps both give one. C9: no repeated ancestor. C10:
exact statement.

### `t96A02_projectivePlaneWedge_isFinitePolyhedron` — LIBRARY, 350–650 lines

Exhibit a finite geometric triangulation of the polygon quotient and its point
wedge. Subdivide the disk so the `aa` boundary pairing is simplicial, descend
to `Surface false 1`, then identify the two center vertices. Build on
`Surfaces.PairingData`, the existing quotient presentation, and
`PointWedgeQuotient.Wedge`. A reusable finite-Δ-complex-to-geometric-complex
bridge is the missing foundation. Independent of the homology and shared
module leaves.

C1: finite polygon identifications produce a finite triangulation. C2: the
predicate is geometric and does not mention fixed points. C3: only an adapter.
C4–C5: produces exactly the public theorem's hypothesis. C6: describes the
registered concrete space. C7: quotient and subtype topologies must match by a
homeomorphism. C8: the wedge point remains a vertex. C9: no ancestor states
triangulability. C10: exact statement.

## Sorry-free assembly

`t96A02_wedge_fixed_point_of_lefschetz` applies
`ConstructionTargets.LefschetzCompactPolyhedron.fixedPointOfNonzeroLefschetz`
to the adapter, `hL f`, and `one_ne_zero`. `apm_t96a02` stays its original
one-line assembly. Layer 1 consists of the two independent t96A02 leaves and
the three independent shared-module leaves; the registered assemblies are
layer 2.

Truth checks: a constant map fixes its image and has value one; the identity
fixes every point. Rotation of `S¹` and the antipodal map of `S²` have
Lefschetz number zero, so the shared theorem does not apply. Translation on
`ℝ` is excluded because `ℝ` is not a finite polyhedron in the module's explicit
sense.

Main doubt: the triangulation adapter is standard mathematics, but the repo has
no generic finite Δ-complex realization bridge yet.
