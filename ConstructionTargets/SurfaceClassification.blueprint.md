# Surface classification blueprint

This blueprint follows the route audits for `t00A02` (connected finite-cover
classification), `t00A03` (classification with boundary), `t91J05` and
`t92J05` (polygon-surface classification), `t94J04` (genus-two recognition),
`t96A01` (`closedOrientableSurface_classification`), and `t97J02`
(`surface-triangulation`).  This first program ends at finite triangulation;
the later nodes record the route from a triangulation to the classification
theorem required by those audits.

The construction builds on Mathlib's `SimplexCategory`, `GeometricRealization`,
`IsCoveringMap`, compactness and manifold APIs, and on
`compactSurfaceFiniteNestedTriangleCover` in this module.  No quotient or
geometric realization is identified by definitional equality: every such
identification below is an explicit `Homeomorph`.

## Fixed representations

`FiniteTwoComplex` is a finite semisimplicial complex truncated in dimensions
0, 1, and 2.  Its face maps satisfy the semisimplicial identities.  Its
realization is the quotient of the finite disjoint union of standard simplices
by those face maps.  A triangulation requires every nondegenerate 2-simplex to
have three distinct vertices; lower-dimensional identifications are allowed.

```lean
structure FiniteTwoComplex where
  vertex edge face : Type
  vertex_finite : Finite vertex
  edge_finite : Finite edge
  face_finite : Finite face
  edgeVertex : edge → Fin 2 → vertex
  faceEdge : face → Fin 3 → edge
  faceVertex : face → Fin 3 → vertex
  face_compat : ∀ f i j, edgeVertex (faceEdge f i) j =
    faceVertex f (Fin.succAbove i j)
  face_vertices_injective : ∀ f, Function.Injective (faceVertex f)
```

`FiniteTwoComplex.Realization K` is the quotient described above.
`FiniteTwoComplex.FaceBound K` means every attaching face has at most three
edges; it is deliberately redundant with the `Fin 3` representation and is a
useful finite-combinatorics interface.

```lean
def AdmitsFiniteTriangulation (M : Type*) [TopologicalSpace M] : Prop :=
  ∃ K : FiniteTwoComplex, Nonempty (K.Realization ≃ₜ M)

def HasFiniteFibers {E M : Type*} (p : E → M) : Prop :=
  ∀ x, (p ⁻¹' {x}).Finite
```

The final theorem's exact statement is:

```lean
theorem compactSmoothSurfaceFiniteTriangulation
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace EuclideanPlane M]
    [IsManifold (𝓘(ℝ, EuclideanPlane)) (⊤ : ℕ∞) M]
    [CompactSpace M] [ConnectedSpace M] :
    AdmitsFiniteTriangulation M ∧
      ∀ {E : Type*} [TopologicalSpace E] [T2Space E]
        (p : E → M), IsCoveringMap p → HasFiniteFibers p →
          AdmitsFiniteTriangulation E
```

Compactness extracts the finite atlas, `T2Space` makes finite gluing quotients
closed, the charted/manifold hypotheses supply disk charts and transition
maps, and connectedness removes empty components.  In the cover clause,
`IsCoveringMap` lifts each simplex and `HasFiniteFibers` makes the lifted
complex finite; `T2Space E` supplies the realization homeomorphism.

### B1. Finite two-complex and realization
lean: `FiniteTwoComplex`, `FiniteTwoComplex.Realization`
uses: Mathlib finite types, standard simplices, quotient topology
status: planned

Define the displayed structure and the quotient realization.  Prove that each
simplex inclusion is continuous and that the realization has the quotient
topology.  The face identities are used to show that the generating gluing
relation is compatible at vertices.

### B2. Face bound
lean: `FiniteTwoComplex.face_card_le_three` : `∀ K : FiniteTwoComplex, K.FaceBound`
uses: B1
status: planned

Represent the boundary-edge set of a face as the image of `Fin 3`.  Its
cardinality is at most three by `Finset.card_image_le`; no manifold hypothesis
is involved.

### B3. Finite closed coordinate disks
lean: `compactSmoothSurfaceFiniteClosedDiskCover`
uses: `compactSurfaceFiniteNestedTriangleCover`
status: planned

Shrink each banked nested coordinate triangle once more.  Compactness chooses
a finite subcover.  The outer triangles contain the closures of the inner
ones, so all intersections relevant to subdivision lie inside chart targets.
The manifold hypothesis supplies the charts; Hausdorffness makes compact
triangle images closed.

### B4. Finite general-position arcs
lean: `surfaceFiniteDiskCover_generalPosition`
uses: B3
status: planned

Induct over the finite disk cover.  Inside a chart, replace boundary arcs by
polygonal arcs, one at a time, fixing already chosen vertices.  At each step
avoid the finite set of old vertices and transverse crossings.  Prove that
intersections are finite and consist of endpoints or transverse crossings.

### B5a. Regular neighborhoods and planar faces
lean: `surfaceFiniteDiskCover_regularNeighborhoodFaces`
uses: B3, B4, Jordan--Schoenflies for polygonal arcs
status: revised (transversality alone neither gives cellularity nor makes
closures of graph-complement components into surfaces at cut vertices)

First insert every transverse crossing from B4 as a vertex and split every
arc there.  This produces a finite embedded polygonal graph `G`, whose raw
complement may have pinched frontiers at cut vertices.  Do not use closures
of those raw components.  Instead choose pairwise disjoint closed polygonal
vertex disks and, following the cyclic order of incident half-edges in the
oriented coordinate disk, pairwise disjoint closed rectangular edge bands.
Their union `N(G)` is a compact regular neighborhood.  Prove explicitly that
each component of `N(G)` is a compact surface with boundary, retracts onto the
corresponding component of `G`, and has boundary a finite disjoint union of
polygonal cycles determined by the rotation system.

Remove the interior of `N(G)` from the closed outer coordinate disk.  A local
chart proof at vertex-disk arcs, edge-band sides, and the outer boundary shows
that every connected component of the remainder is now a genuine compact
planar surface with finitely many disjoint polygonal boundary cycles.  This is
the planar-face theorem used below; in particular it covers cut vertices and
the transverse figure-eight without assigning a boundary-component count to
a pinched raw frontier.

### B5b. Cellularize the regular-neighborhood faces
lean: `surfaceFiniteDiskCover_cellularSubdivision`
uses: B5a, Jordan--Schoenflies for polygonal arcs
status: revised

For each planar face supplied by B5a, if it has more than one boundary cycle,
choose two cycles and a polygonal embedded arc in the face joining them.  The
arc's interior avoids `N(G)` and all earlier cutting arcs; add endpoint
vertices and the arc to the subdivision.

Cutting along such an arc joins two boundary components and decreases
`boundaryComponentCount - 1` by one.  Sum this natural-number measure over
the finitely many B5a faces.  Prove by cutting a compact surface along a
properly embedded arc that the result remains a compact planar surface and
that this measure decreases by exactly one.  Induction terminates.  At measure
zero every connected face has one polygonal boundary cycle; polygonal
Jordan--Schoenflies identifies it with a closed disk.  The vertex disks and
edge bands of `N(G)` already have finite disk subdivisions; subdivide them
compatibly at all cutting-arc endpoints.  Thus every final cell is a disk and
every frontier is a finite cyclic edge path.  The outer-disk containment from
B3 keeps the construction inside one chart.  The nested-polygon example is
cut across its annular B5a face, while the figure-eight is first unpinched by
its vertex disk.

### B6. Triangulate the polygonal cells
lean: `surfaceFiniteDiskCover_cellTriangulation`
uses: B5b
status: planned

Triangulate each polygonal disk by induction on its number of boundary edges.
Choose a diagonal lying in the disk, split into smaller polygons, and prove
compatibility on shared boundary arcs because the complete cellular graph,
including B5b's cutting arcs and B5a's regular-neighborhood subdivision, is
fixed before any region is triangulated.

### B7. Assemble the finite complex
lean: `surfaceFiniteDiskCover_finiteTwoComplex`
uses: B1, B6
status: planned

Take vertices, edges, and faces from the finite subdivisions.  Quotient only
duplicate chart labels representing the same point.  Finiteness follows from
the finite cover and finite subdivisions.  Verify every semisimplicial identity
and distinctness of the three vertices of each triangle.

### B8. Realization map is a homeomorphism
lean: `surfaceFiniteDiskCover_realizationHomeomorph`
uses: B3, B7
status: planned

Map each realized simplex through its chart embedding.  Compatibility on face
maps gives a continuous map from the quotient.  It is surjective by the inner
cover and injective by the subdivision equivalence relation.  The source is
compact and the surface Hausdorff, hence the continuous bijection is a
homeomorphism.

### B9. Lift a finite triangulation through a finite covering
lean: `FiniteTwoComplex.liftAlongFiniteCover`
uses: B1, Mathlib `IsCoveringMap` evenly-covered neighborhoods
status: planned

Subdivide finitely until every closed simplex lies in an evenly covered open
set.  Lift each simplex once for every point in the fiber over a selected
vertex.  Unique lifting makes face maps agree.  `HasFiniteFibers` and the
finiteness of the base complex make all lifted simplex types finite.

### B10. Lifted realization identifies the covering space
lean: `FiniteTwoComplex.liftedRealizationHomeomorph`
uses: B9
status: planned

The lifted simplex maps define a continuous bijection to the total space.
Even covering charts give a local inverse, hence a homeomorphism.  The
`T2Space E` hypothesis is used to separate coincident candidates and, together
with the finite construction, also permits the compact-to-Hausdorff argument.

### B11. Compact smooth surface finite triangulation
lean: `compactSmoothSurfaceFiniteTriangulation` : the exact statement above
uses: B7, B8, B9, B10
status: planned

Use B3--B8 for the first conjunct.  For a finite covering, lift that complex
with B9 and use B10.  Connectedness is used in B3 to discard the empty case
and ensure the cover describes the single surface rather than a finite family
of components.

### B12. Polygon normal form
lean: `FiniteTwoComplex.closedSurface_polygonNormalForm`
uses: B2, B11
status: planned

Choose a spanning tree in the primal one-skeleton and in the dual graph.
Collapse the primal tree and cut along all dual-tree edges.  The remaining
2-cell is a polygon whose paired boundary word realizes the original surface.

### B13. Normalize the polygon word
lean: `SurfacePolygon.normalForm`
uses: B12
status: planned

Apply elementary cut-and-paste homeomorphisms to move paired letters together.
Induct on the number of pairs.  The orientable case becomes a product of
commutators; the nonorientable case becomes a product of squares.

### B14. Recognize orientability and Euler characteristic
lean: `closedOrientableSurface_classification`
uses: B13, homology-orientability, Euler characteristic of a finite complex
status: planned

Top homology selects the orientable normal form.  Count the one-vertex polygon
cell structure to obtain `χ = 2 - 2*g`; integer cancellation gives uniqueness
of `g`.  Transport the polygon homeomorphism to the consumer's surface model.
