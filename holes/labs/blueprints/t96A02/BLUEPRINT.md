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

### `t96A02_projectivePlaneWedge_isFinitePolyhedron` — assembled

This is now sorry-free assembly from
`FiniteTriangulation.realProjectivePlane_hasFiniteVertexTriangulation` and
`wedge_isFinitePolyhedron_of_vertexTriangulations`.  The former supplies the
subdivided `aa` polygon with its centre as a vertex; the latter identifies the
two marked vertices and realizes the finite abstract complex by basis vectors.
The three shared leaves, estimates, Mathlib tools, and C1--C10 records are in
`ConstructionTargets/FiniteTriangulation.blueprint.md` and are independent of
the homology leaf here.

C1: point gluing of the two marked complexes is finite. C2: no conclusion is
assumed. C3: assembly only. C4: both summands are supplied. C5: the marked
centre equalities are the maps consumed by gluing. C6: the registered concrete
space is unchanged. C7: the shared leaves supply a homeomorphism to the
Euclidean subspace realization. C8: the wedge point is a vertex. C9: no
ancestor states triangulability. C10: exact statement.

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
