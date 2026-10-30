# Geometric simplicial subdivision

This module supplies the barycentric-subdivision infrastructure needed by the
Lefschetz compact-polyhedron development, without importing that development.
The public theorem `exists_fine_subdivision` has exactly the registered target
statement.  Its proof is a sorry-free assembly; all open work is in the leaves
listed below.

## Definitions and assembly

`barycentricFaces K` consists of the barycenters (`Finset.centerMass` with unit
weights) of nonempty faces occurring in a finite strict inclusion chain.  The
empty chain contributes the empty set, which `SimplicialComplex.ofErase`
removes.  The definition `barycentricSubdivision` is assembled only from proof
parameters, so it contains no hidden dependency on a sorry leaf.

The final assembly instantiates one subdivision step with the three complex
axioms, finiteness, space equality, and the mesh estimate.  It then calls the
iteration leaf.  No leaf invokes another leaf.

## Leaves

| Leaf | Claim and proof route | Estimate | Dependencies | Class |
|---|---|---:|---|---|
| `barycentricFaces_affineIndependent` | Barycenters of a strict chain are affinely independent. Order the chain by cardinality and use triangular barycentric coordinates; `Finset.centerMass`, `AffineIndependent.of_comp`, `K.indep`. | 120–180 | definitions only | ordinary |
| `barycentricFaces_isLowerSet` | A subset of the image of a chain is the image of a subchain; remove duplicate preimages using strict-chain injectivity. Use `Finset.image_subset_iff`, `Finset.filter`, `IsLowerSet`. | 50–90 | definitions only | ordinary |
| `barycentricFaces_inter_subset` | Uniqueness of barycentric coordinates for two flags implies support lies in their common barycenters. Use `AffineIndependent.affineCombination_eq_iff`, `convexHull_eq`, and the first differing faces of the two chains. | 180–260 | definitions only | **LIBRARY** (hard flag-intersection foundation) |
| `barycentricSubdivision_finite` | Finite old faces give finitely many chains and images. Use `Set.Finite.fintype`, `Set.Finite.finset`, `Set.Finite.image`. | 40–70 | explicit `hi hd hx`; independent of other leaves | ordinary |
| `barycentricSubdivision_space` | Each barycenter lies in its old face; conversely triangulate an old simplex by sorting barycentric coordinates. Use `Finset.centerMass_mem_convexHull`, `convexHull_mono`, `K.convexHull_inter_convexHull`. | 160–240 | explicit `hi hd hx`; independent | **LIBRARY** (simplex flag decomposition) |
| `barycentricSubdivision_mesh` | Hatcher 2.21: distances between barycenters in a flag are at most `d/(d+1)` times old mesh, then pass to hull diameter. Use `Metric.diam_convexHull`/`diam_convexHull`, `Finset.centerMass`, triangle inequality and `csSup_le`. | 150–220 | explicit `hi hd hx`, dimension bound; independent | **LIBRARY** if diameter API needs rebuilding |
| `exists_fine_of_barycentric_step` | Iterate the supplied one-step witness; `(n/(n+1))^m → 0`, while finite space-preserving steps compose. Use `tendsto_pow_atTop_nhds_zero_of_lt_one`, `Metric.diam_nonneg`, `Real.exists_nat_pow_lt`. | 100–160 | only explicit `step` hypothesis | ordinary |
| `exists_inducedContinuousMap` | Glue affine maps on faces; face intersections agree by common vertices. Use `AffineIndependent.affineCombination`, `ContinuousMap.piecewise`, `K.convexHull_inter_convexHull`. | 160–220 | interface definitions only | **LIBRARY** (PL realization/gluing) |
| `inducedMap_homotopic_of_star_condition` | The star condition puts `g x` and the affine image in a common target simplex; its convexity contains the straight-line homotopy. Use `Convex.segment_subset`, `ContinuousMap.Homotopic`, `IsSimplicialVertexMap`. | 120–180 | explicit star and affine-carrier hypotheses | ordinary |
| `exists_vertexMap_of_mesh_lt_lebesgue` | Choose for each vertex a target open star containing its `δ`-ball; the half-mesh bound makes all vertices of a face share a target simplex. Use `lebesgue_number_lemma_of_metric`, finite choice, `Metric.mem_ball`, open-star cover. | 140–200 | explicit Lebesgue and mesh hypotheses | ordinary |

Dependency layers: layer 0 contains all ten leaves (each is independently
statable/provable).  Layer 1 is the definition `barycentricSubdivision` and the
sorry-free theorem `exists_fine_subdivision`.

## C1–C10 review

- `barycentricFaces_affineIndependent`: C1 strict inclusion makes distinct barycenters and gives the triangular proof; C2 conclusion is not assumed; C3 only linear algebra; C4 no induction interface; C5 uses actual face inclusions; C6 faithful; C7 real unit weights have nonzero total on faces; C8 empty complex is vacuous and a singleton chain gives one point; C9 is not the target; C10 matches.
- `barycentricFaces_isLowerSet`: C1 the empty subface is represented by the empty subchain; C2 nonvacuous; C3 combinatorial only; C4 arbitrary subsets handled; C5 image witnesses retained; C6–C7 faithful/ordinary Finset semantics; C8 empty chain checked; C9 distinct; C10 matches.
- `barycentricFaces_inter_subset`: C1 flags in one simplex meet in their common flag face; C2 no intersection conclusion is assumed; C3 isolates only the hard axiom; C4 disjoint chains give empty intersection of hulls by uniqueness; C5 exact Mathlib axiom shape; C6–C7 faithful; C8 empty faces erased downstream but statement also handles them; C9 distinct; C10 marks LIBRARY.
- `barycentricSubdivision_finite`: C1 finite powerset of a finite face set; C2 finiteness not assumed for output; C3 one counting fact; C4 all chains covered; C5 proof parameters expose the exact complex; C6–C7 faithful; C8 empty complex finite; C9 distinct; C10 matches.
- `barycentricSubdivision_space`: C1 standard flag triangulation; C2 equality not assumed; C3 isolated geometric decomposition (marked LIBRARY); C4 both inclusions included; C5 same proof-parameterized complex; C6–C7 faithful; C8 empty complex gives empty space and dimension zero is unchanged; C9 not the ancestor statement; C10 matches.
- `barycentricSubdivision_mesh`: C1 for a 1-simplex the two edges have half the diameter; for a 2-simplex factor is `2/3`; C2 bound not assumed; C3 one-step estimate only; C4 `sSup` covers all old faces; C5 dimension hypothesis is explicit; C6 ambient `n` supplies the final bound; C7 casts are real (not Nat division); C8 zero-dimensional factor is zero; C9 distinct; C10 matches.
- `exists_fine_of_barycentric_step`: C1 contraction `n/(n+1)<1`, including `n=0`; C2 output is not in `step`; C3 iteration only; C4 base and successor space equalities compose; C5 exact witness passed; C6–C7 real powers; C8 empty and `n=0` terminate correctly; C9 weaker reusable induction, not ancestor repeat; C10 matches.
- `exists_inducedContinuousMap`: C1 a simplicial map has a PL realization; C2 only vertex values assumed; C3 gluing isolated; C4 intersection compatibility follows from common vertices; C5 returns the map consumed later; C6–C7 faithful; C8 empty source admits the unique map, zero-dimensional source is vertexwise; C9 distinct; C10 matches.
- `inducedMap_homotopic_of_star_condition`: C1 carrier condition supplies a common convex simplex; C2 homotopy not assumed; C3 homotopy only; C4 boundary points belong to every needed closed carrier; C5 takes the actual `f`, `g`, and vertex map; C6–C7 faithful; C8 empty source and boundary points checked; C9 distinct; C10 matches.
- `exists_vertexMap_of_mesh_lt_lebesgue`: C1 is the standard simplicial approximation choice argument; C2 star conclusion is not assumed (Lebesgue balls are); C3 choice only; C4 every vertex/face covered; C5 returns the exact vertex map and star condition; C6–C7 faithful and `δ/2` is real; C8 empty complex is vacuous, isolated vertices choose from the cover; C9 distinct; C10 matches.

## Truth checks and doubts

- Empty complex: the raw empty face is erased; its realization remains empty,
  finiteness and all mesh assertions are vacuous.
- Dimension zero: subdivision has the same singleton faces and mesh zero.
- One simplex: its flag subdivision is the usual barycentric subdivision.  In
  dimension one it consists of the two half-edges, giving factor `1/2`.
- A 2-simplex is cut into the six vertex–edge–face flag triangles; the standard
  estimate is `2/3`.
- Strict chains are essential: their barycenter coordinate matrix is triangular
  with nonzero diagonal, hence affine independence.

The main uncertainty is API cost, not mathematical truth: Mathlib appears not
to expose the desired convex-hull diameter lemma under the prompt's exact names
in this revision, and it has no ready-made PL gluing or barycentric subdivision.
Those three foundations are therefore honestly marked LIBRARY rather than
hidden in an ordinary leaf.

## Review fixes (claude-14, 2026-10-28)

- `barycentricSubdivision_mesh` now assumes `K.faces.Finite`. Without it the leaf is false: for an infinite complex with unbounded face diameters, `sSup` of the unbounded set is `0` in ℝ, so the claim would be `diam ≤ 0`. The assembly already had `hL`.
- `exists_inducedContinuousMap` now assumes `K.faces.Finite` and also concludes the carrier property (`x ∈ hull s → f x ∈ hull (h '' s)`). Without finiteness it is false: edges `[0, p_k]` with `p_k → 0` and `h 0 ≠ h p_k` give a piecewise-affine map discontinuous at `0` in the subspace topology. Without the carrier clause it was too weak to feed `inducedMap_homotopic_of_star_condition`'s `haff` (any continuous map with the vertex values satisfied it).
