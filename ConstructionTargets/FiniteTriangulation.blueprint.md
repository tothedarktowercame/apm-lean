# FiniteTriangulation blueprint

This module isolates the common triangulation work for the three Lefschetz
adapters.  Its central interface records an actual finite geometric complex,
a homeomorphism onto its subspace realization, and a distinguished singleton
face.  Thus the wedge theorem cannot hide the requirement that the gluing
point be a vertex.

## Leaves

### `hasFiniteVertexTriangulation_of_isFinitePolyhedron` — LIBRARY, 180–300 lines

Perform stellar subdivision in the (unique minimal) face containing the
chosen point, followed by compatible subdivisions of its cofaces.  Use
`Geometry.SimplicialComplex.space`, finiteness of `K.faces`, barycentric
coordinates on `convexHull`, and `Continuous.homeoOfEquivCompactToT2` for the
unchanged realization.  Independent.

C1 finite stellar subdivision preserves the realization; C2 the conclusion
adds a genuine singleton face; C3 only marks one point; C4 cofaces are also
subdivided; C5 the homeomorphism is retained; C6 no extra hypothesis; C7
`K.space` has the Euclidean subspace topology; C8 includes zero-dimensional
complexes (the chosen point is already a vertex); C9 stronger than, not a
repeat of, `IsFinitePolyhedron`; C10 exact.

### `wedge_isFinitePolyhedron_of_vertexTriangulations` — LIBRARY, 250–400 lines

Rename the two finite vertex sets disjointly, identify the marked vertices,
embed the resulting finite vertex type as standard basis vectors, and take
the downward closure of the two face families.  Affine independence follows
from the basis embedding; coordinate support proves the intersection axiom.
Construct the map from the quotient with
`PointWedgeQuotient.quotientMap` and finish with
`Continuous.homeoOfEquivCompactToT2`.  Independent of the stellar leaf because
it receives both marked triangulations explicitly.

C1 the two summands meet in exactly the common vertex; C2 neither input
assumes the conclusion; C3 only generic point gluing; C4 every face comes from
one summand; C5 the marked equalities identify the quotient maps; C6 arbitrary
finite polyhedra and points are allowed; C7 the target is the Euclidean
subspace realization; C8 empty face sets cannot occur for an inhabited marked
space, while dimension-zero wedges work; C9 no ancestor states marked gluing;
C10 exact.

### `realProjectivePlane_hasFiniteVertexTriangulation` — LIBRARY, 350–600 lines

Use a subdivision of the disk polygon compatible with the `aa` boundary
identification, with the disk centre included as a vertex.  The raw two-gon is
not a simplicial complex: subdivide its boundary so no simplex is identified
with itself.  Descend the realization map through the `Surfaces.PairingData`
quotient and use the quotient's T2 instance plus compact-to-Hausdorff to get
the homeomorphism.  Independent of both generic leaves.

C1 the standard subdivided `RP²` triangulation is valid; C2 the singleton-face
clause is extra data; C3 only triangulates one concrete space; C4 boundary
pairing is simplicial after subdivision; C5 the centre maps to `surfacePoint`;
C6 it is exactly `Surface false 1`; C7 quotient and subspace topologies are
linked by the homeomorphism; C8 the centre is an interior vertex and boundary
self-identification is excluded; C9 not an ancestor; C10 exact.

`wedge_isFinitePolyhedron` and the forgetful theorem are sorry-free assembly.
Dependency layers: all three leaves are parallel; the generic wedge closure is
the next layer.  Main doubt: Mathlib has geometric simplicial complexes but no
ready-made stellar-subdivision or abstract-finite-complex realization API, so
the first two estimates may grow; both remain genuine shared LIBRARY work.

## Review fix (claude-14, 2026-10-28)

`wedge_isFinitePolyhedron_of_vertexTriangulations` now concludes `HasFiniteVertexTriangulation (Wedge x₀ y₀) (quotientMap x₀ y₀ (.inl x₀))`: the glued vertex IS the wedge point, so the marking is free to keep, and keeping it lets t99A03 wedge two wedges without the stellar-subdivision leaf. `hasFiniteVertexTriangulation_of_isFinitePolyhedron` is now used only by the general `wedge_isFinitePolyhedron`, which no consumer needs; it is not queued.
