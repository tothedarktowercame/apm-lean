# Concrete simplicial chain maps — revised split

## Triage and defect repairs

The old `oriented_model_of_explicit_maps` was false: it concluded
`HomologyModels M g` without relating `g` to the vertex map (on a triangulated
sphere take a carrier-avoiding map but `g = id`, whose Lefschetz number is 2).
It now takes an affine realization `f`, its carrier property, and the exact
homotopy `e ∘ g ∘ e⁻¹ ∘ Homeomorph.setCongr hspace ≃ f`.

`exists_fine_iterated_approximation` returns an explicit `m` and
`K' = (barycentricStep^[m]) K`, the space equality, simplicial and avoidance
properties, and the star condition for that exact transported map. The
sorry-free adapter obtains `f` from `exists_inducedContinuousMap` and derives
the required homotopy with `inducedMap_homotopic_of_star_condition`. The count
`m` is the subdivision evidence; assembly recursively composes one-step maps.

Both comparison leaves are now degreewise homology equalities for specific
chain morphisms. Their source complexes are `ChainComplex.of` built from
explicit square-zero hypotheses, as in `orderedFace_singular_quasiIso`; their
right sides are the specific Mathlib maps `induced f k` and
`induced (Homeomorph.setCongr hspace) k`. There is no existential singular map.

`IsSubdivisionChainMap` now fixes every coefficient by `flagSign`, a closed
inversion-parity formula on the unique vertices introduced along the inclusion-
ordered flag. Thus `subdivisionChainMap_commutes` concerns a determined map.

## Leaves

| Leaf | Claim and intended tools | Size | Independence |
|---|---|---:|---|
| `vertexChainMap_exists` | Extend the generator formula with `Finsupp.lsingle`, `Finset.image`, `sortingSign`. | 70–110 | independent |
| `vertexChainMap_commutes` | Signed deletion naturality; injective terms match, collision terms cancel. | 120–180 | independent; predicate inputs only |
| `barycentricSubdivisionChainMap_exists` | Sum `flagSign` over strict maximal flags using `Finset.powerset` and `Finsupp.linearCombination`. | 120–170 | independent |
| `subdivisionChainMap_commutes` | Pair internal flag-boundary terms and identify endpoints using the closed inversion formula. | 150–210 | independent; **LIBRARY if >200** |
| `vertexChainMap_affineComparison_square` | Acyclic-carrier/straight-line homotopy proves `H(hm) ≫ H(cmpL) = H(cmpK) ≫ induced f`; use `HomologicalComplex.homologyMap_comp` and singular homotopy invariance. | 100–160 | independent |
| `subdivision_affineComparison_square` | Carrier homotopy proves `H(sd) ≫ H(cmpK') = H(cmpK) ≫ induced(setCongr hspace)`. | 100–160 | independent |
| `composite_zero_diagonal` | Expand a basis vector; each flag is carried by `s`, while its image is disjoint from `s`. | 40–70 | independent |
| `exists_fine_iterated_approximation` | Iterate `barycentricStep`, use mesh contraction and `exists_vertexMap_of_mesh_lt_lebesgue`, retain star condition, use margin for avoidance. | 300–450 | **LIBRARY**, geometric |
| `oriented_model_of_explicit_maps` | Compose step maps along `m`; choose deletions/comparisons; apply squares and `orderedFace_singular_quasiIso`; package model; transfer through supplied homotopy. | 350–550 | **LIBRARY**, assembly |

Layers: the first seven leaves are mutually independent. Geometric preparation
is independent of them. Model assembly consumes both groups. The final adapter
is already sorry-free.

## Consumer audit

- `m`, `K'`, finiteness, space equality, `h`, simpliciality, avoidance, star:
  `exists_fine_iterated_approximation`.
- affine `f` and carrier property: proved `exists_inducedContinuousMap`.
- exact `g`–`f` homotopy: proved `inducedMap_homotopic_of_star_condition`,
  invoked in the adapter.
- vertex map/chain law: `vertexChainMap_exists`, `vertexChainMap_commutes`.
- step subdivision maps/chain laws: `barycentricSubdivisionChainMap_exists`,
  `subdivisionChainMap_commutes`; the returned iterate licenses recursion.
- homology naturality: the two repaired comparison-square leaves.
- comparison quasi-isomorphisms: proved `orderedFace_singular_quasiIso`.
- zero trace: `composite_zero_diagonal`; finiteness/boundedness: proved
  `faceModule_finiteDimensional`, `faceModule_zero_above`.

## Tests and C1–C10

Degeneracies: a collapsed edge maps to zero and its boundary cancels; a
transposition has sign `-1`; a subdivided edge gives `[a,m]+[m,b]` after
sorting; degree-zero flags have sign `1`; empty complexes have zero modules;
`m=0` makes `K'=K` and the recursive subdivision map the identity. Equality
orientations were checked so each `Homeomorph.setCongr` points with its map.

- `vertexChainMap_exists`: C1 collision/transposition; C2 fixed generators; C3 construction only; C4 both cardinality cases; C5 exact modules; C6 faithful; C7 rational parity; C8 empty/zero; C9 new; C10 current.
- `vertexChainMap_commutes`: C1 collapsed cancellation; C2 no conclusion input; C3 one identity; C4 exhaustive cases; C5 same deletions; C6 faithful; C7 fixed signs; C8 zero; C9 new; C10 current.
- `barycentricSubdivisionChainMap_exists`: C1 genuine maximal flags; C2 computed coefficients; C3 construction; C4 all powerset flags; C5 canonical step; C6 faithful; C7 closed sign; C8 empty/vertices; C9 new; C10 current.
- `subdivisionChainMap_commutes`: C1 edge test; C2 determined map; C3 one identity; C4 internal/end terms; C5 exact differentials; C6 faithful; C7 parity fixed; C8 zero; C9 new; C10 current.
- `vertexChainMap_affineComparison_square`: C1 convex straight-line homotopy; C2 no existential/vacuous square; C3 one homology equality; C4 all degrees; C5 specific `induced f`; C6 carrier retained; C7 rational; C8 empty; C9 repaired, not repeated; C10 current.
- `subdivision_affineComparison_square`: C1 canonical realization; C2 no existential map; C3 one equality; C4 all degrees; C5 specific `setCongr`; C6 faithful; C7 rational; C8 identity/empty; C9 repaired; C10 current.
- `composite_zero_diagonal`: C1 zero/triangle tests; C2 geometric avoidance; C3 short calculation; C4 injective/collapsed; C5 exact coefficient; C6 faithful; C7 sign-independent; C8 empty/zero; C9 new; C10 current.
- `exists_fine_iterated_approximation`: C1 exact iterate/star output; C2 margin is not conclusion; C3 LIBRARY; C4 includes `m=0`; C5 all consumer data; C6 faithful; C7 positive δ; C8 empty; C9 stronger than rejected ancestor; C10 current.
- `oriented_model_of_explicit_maps`: C1 sphere counterexample blocked by homotopy; C2 no model/trace conclusion assumed; C3 LIBRARY; C4 iterate recursion covered; C5 exact maps exposed; C6 faithful; C7 rational; C8 empty/zero; C9 strict repair; C10 current.

## Doubts / LIBRARY boundary

The two marked LIBRARY leaves remain substantial. No missing manifold or
classification foundation is apparent. The highest-risk interface is checking
that `flagSign` agrees in all dimensions with the deletion order in
`IsSignedDeletion`; edge and transposition tests agree. The iterated
subdivision proof must also establish the carrier behavior of the recursive
composite rather than infer it merely from equality of realizations.

## Review fix (claude-14, 2026-10-28)

`exists_fine_iterated_approximation` as submitted asked for a vertex map `h : K' → K` into the ORIGINAL complex that is carrier-avoiding for `K`'s faces. False for a coarse `K`: on the triangle boundary `abc` with the half-turn (face-avoiding with a positive margin), the vertex `b` lies in `[a,b]` and `[b,c]`, so `h b` would have to avoid `a`, `b` and `c`. As in Hatcher 2C.3 the TARGET must be fine too. Now: `L := barycentricStep^[p] K` (mesh `< δ/2`; margin passes to `L`'s faces since each lies in a `K`-face), `K' := barycentricStep^[m] L`, `h : K' → L` simplicial, carrier-avoiding for `L`, star condition for `g` transported to `K'.space → L.space`. Truth: `g' v ∈ st_L (h v)` gives `dist (g' v) (h v) < mesh L < δ/2`; if `h v` were in an `L`-face `t ∋ v` this would contradict the margin `δ`. The adapter now feeds `oriented_model_of_explicit_maps` with `L`, `K'` and `eL := e.trans (setCongr hL.symm)`.
Sorry-trap: `barycentricStep` is a def over GeometricSimplicialSubdivision's three face leaves (affineIndependent, isLowerSet, inter_subset); leaves mentioning it (`exists_fine_iterated_approximation`, `oriented_model_of_explicit_maps`) carry sorryAx until those three land, so they are queued only after them.
