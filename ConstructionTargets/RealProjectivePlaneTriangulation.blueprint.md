# RealProjectivePlaneTriangulation blueprint

## Triage and route

The target is true and faithful.  For `SurfaceRel false 1`, unfolding `SurfaceRel`
gives the two semicircle parameterizations with the *same* parameter.  Directly from
`edgePoint`, the second point is the negative of the first.  Thus the identification is
antipodal on the boundary circle, not a reversal of the parameter within an edge.

The proposed fine disk fan is unnecessary: the classical minimal triangulation of
`RP²` has six vertices and ten triangles, and no triangle contains two representatives
which are identified in the polygon model.  Its barycentric/piecewise-affine comparison
with the disk polygon gives the same centre-marking requirement.  The explicit model is
kept as one LIBRARY item because Mathlib presently has no theorem turning a finite
abstract simplicial complex into the required `Geometry.SimplicialComplex` realization
together with its quotient homeomorphism.

## Leaves

| Leaf | Claim and proof route | Estimate | Independent? |
|---|---|---:|---|
| `rp2_t2Space` | `Surface false 1` is Hausdorff.  Show the antipodal boundary equivalence relation is closed on the compact disk, then use the compact closed-equivalence quotient theorem (`Quotient`, `Topology.IsQuotientMap`, `isClosed_eq`). | 70–120 | yes |
| `finite_simplicialComplex_space_isCompact` | A finite union of convex hulls of finite faces is compact.  Unfold `Geometry.SimplicialComplex.space`; use `Finite.isCompact_biUnion`, `Finset.finite_toSet`, and `Set.Finite.isCompact_convexHull`. | 20–40 | yes |
| `rp2_explicit_finite_model` | Realize the six vertices by coordinate basis vectors and the ten facets of the minimal `RP²` triangulation; build with `Geometry.SimplicialComplex.ofErase`.  Define the simplexwise affine characteristic map to the polygon disk and descend through `surfaceQuotient`; prove compatibility, continuity, and the boundary fibre calculation. | 250–400, **LIBRARY** | yes |

Dependency layers: layer 0 consists of all three leaves.  The final theorem is a
sorry-free assembly using `Continuous.homeoOfEquivCompactToT2` and
`Equiv.ofBijective`.

## Explicit-model proof obligations

Use the standard six-vertex ten-facet list (each edge occurs in exactly two facets).
For the geometric realization, standard basis coordinates give affine independence;
`convexHull` intersections reduce to equality of nonnegative coordinate supports.
The characteristic maps on adjacent triangles agree on their shared edge, so the finite
closed-cover pasting lemma gives continuity.  On the polygon boundary, unfold
`Surfaces.SurfaceRel`, `Surfaces.edgePoint`, and use `Complex.exp_pi_mul_I` to prove
that exactly antipodal points have equal quotient image.  Interior simplex coordinates
give injectivity away from that boundary, and the triangle cover gives surjectivity.
Choose the vertex corresponding to the polygon centre, so the marking equation is
literal after descent.  Useful declarations: `Surfaces.Disk`, `Surfaces.SurfaceRel`,
`Surfaces.surfaceQuotient`, `Surfaces.continuous_surfaceQuotient`,
`Surfaces.surjective_surfaceQuotient`, `Geometry.SimplicialComplex.ofErase`,
`Geometry.SimplicialComplex.space`, and
`Continuous.homeoOfEquivCompactToT2`.  `StandardTriangleEmbedding` and
`ChartTriangleEmbedding` are alternative local-coordinate tools if the affine pasting
proof is expressed through the existing polygon chart infrastructure.

## C1–C10 checks

- `rp2_t2Space`: C1 the relation is specifically `false,1`, not a general quotient;
  C2 it supplies a genuine separation instance; C3 only the closed-relation argument;
  C4 closed quotient theorem closes; C5 no hidden map; C6 matches the concrete model;
  C7 coinduced topology checked; C8 boundary and centre checked; C9 not the ancestor;
  C10 prose matches.
- `finite_simplicialComplex_space_isCompact`: C1 finite faces are essential; C2 the
  conclusion is not assumed; C3 one finite-union calculation; C4 every face covered;
  C5 uses `K.space`; C6 no extra target hypothesis; C7 finite `biUnion`; C8 an empty
  face family gives the empty compact set; C9 general helper, not target; C10 matches.
- `rp2_explicit_finite_model`: C1 the ten-facet complex is the standard closed
  triangulated surface and the fibre calculation handles the quotient; C2 no conclusion
  is passed as a hypothesis; C3 marked LIBRARY because the missing realization-and-map
  foundation remains 250–400 lines; C4 its five outputs are exactly what assembly uses;
  C5 it carries the actual map and marking; C6 no stronger target assumptions; C7 map
  direction is `K.space → Surface`; C8 centre, boundary, and vertices checked; C9 it is
  weaker than the ancestor (continuous bijection, not a homeomorphism); C10 matches.

## Doubt / missing foundation

The explicit-model leaf is still LIBRARY-sized.  A further honest split requires first
committing concrete facet and characteristic-map definitions; splitting it using an
abstract predicate would merely hide the whole theorem in that predicate.  The main
risk is the amount of piecewise-affine infrastructure needed to connect the six-vertex
model to the round-disk presentation, not the topology or the boundary sign convention.

## Revised plan for `rp2_explicit_finite_model` (claude-14, 2026-10-28)

The marked point `surfacePoint false 1` is the image of the disk centre, so the
centre must be a vertex.  The six-vertex model has its centre inside a triangle,
so it is replaced by a 10-vertex, 18-triangle model (V − E + F = 10 − 27 + 18 = 1):

* boundary hexagon `B₀ … B₅` with `B_i ~ B_{i+3}` (labels `a, b, c, a, b, c`);
* a ring `m₀ … m₅`, `m_i` on the ray through the midpoint of edge `B_i B_{i+1}`;
* the centre `O`.
* Triangles: `{O, m_i, m_{i+1}}`, `{B_i, B_{i+1}, m_i}`, `{B_{i+1}, m_i, m_{i+1}}`
  for `i ∈ Fin 6`, with `B` labels taken mod 3.  Distinct triangles have distinct
  label sets, and two triangles that share two labels share that edge.

Stages (each needs the previous one landed, to avoid the sorry trap in defs):
1. Generic basis realization: `_aux_basis_indep`, `_aux_basis_inter` (queued).
2. Define `basisComplex F` (faces = nonempty subsets of the facets `F`, mapped to
   basis vertices) and the RP² facet list; `faces.Finite`.
3. Polar sector map `Disk → Hex`, `r·e^{2πi(j+t)/6} ↦ r((1−t)ζ_j + tζ_{j+1})`: a
   homeomorphism onto the hexagon that commutes with negation.  (It also gives
   `boundary_affine` for t02A04's `DiskConeModel`.)
4. Piecewise-affine `P : Hex → K.space` on the planar 18-triangle subdivision:
   continuous by pasting finitely many closed triangles, surjective, and
   `P x = P y ↔ x = y ∨ (x ∈ ∂Hex ∧ y = −x)`.
5. Descend to `RealProjectivePlane → K.space`; it is a continuous bijection from a
   compact space to a T2 space, so a homeomorphism; take `f` as its inverse.  Then
   `f (basis O) = surfacePoint false 1`, because `P 0 = O`.
