# Concrete ordered-face chains — revised split

## Triage

The old split was false: `Model.comparison`, `sd`, and `hm` were arbitrary, and
`A'` modeled the wrong complex.  This revision removes those structures.  Its
chain group is concretely `FaceIndex K k →₀ ℚ`, where `FaceIndex K k` is the
subtype of actual faces of cardinality `k+1`.

The imported `CoefficientSimplicialChainFinsupp*` files describe chains of an
already-given simplicial set; they do not define the ordered-face subcomplex of
a geometric simplicial complex.  An ambient linear order is therefore supplied
explicitly as the orientation choice (Euclidean space has no Mathlib
`LinearOrder` instance).

## Stage 1

| Leaf | Concrete claim / Mathlib route | Size | Independence |
|---|---|---:|---|
| `signedDeletion_exists` | Linear extension of the displayed signed-deletion formula; `SimplicialComplex.down_closed`, `Finset.card_erase_of_mem`, `Finsupp.linearCombination`. | 60–100 | independent |
| `signedDeletion_sq_zero` | Pair the two deletion orders with opposite signs; `Finset.sum_bij`, list `idxOf`/erase lemmas. | 80–140 | takes the formula explicitly, independent |
| `faceModule_finiteDimensional` | A subtype of finite `K.faces` is finite; Finsupp on a finite basis is finite-dimensional. | 30–60 | independent |
| `faceModule_zero_above` | Bound face cardinalities by their finite maximum; the empty complex gives zero modules. | 40–70 | independent |
| `affineComparison_exists_and_commutes` | Send an ordered face to its affine singular simplex; use `CoefficientH0.singularGenerator_boundary`, affine face formulas, and `SimplicialComplex.convexHull_subset_space`. | 100–150 | takes signed deletion explicitly |

No definition contains a proof obligation or uses a leaf.  `ChainComplex.of` is
introduced only in stage-two statements with `hdd` supplied explicitly.

## Stage 2

| Leaf | Concrete claim / route | Size | Building on |
|---|---|---:|---|
| `orderedFace_singular_quasiIso` | The homology map of the generator-specified affine comparison is bijective. Use repeated `CoefficientSingularSubdivision.singularSubdivision`, small-chain/range results, and `CoefficientSimplicialChainFinsuppRange.chainsMap_component_range_finsupp`. | 250–450 | explicit stage-1 conclusions; **LIBRARY** |

## Honest missing LIBRARY foundation

The available imports do not yet connect geometric subdivision to the concrete
ordered-face modules.  Still needed are (1) the signed barycentric-subdivision
map of `K`, (2) the signed ordered-face map of a simplicial vertex map (sorting
sign, zero on collisions), and (3) their basis-coefficient formula.  This is an
estimated 250–400-line **LIBRARY** item.  Until it exists, carrier avoidance
cannot imply zero trace: it says nothing about an unconstrained linear map.
Accordingly this revision does not reintroduce false arbitrary-`sd`/`hm` leaves.

The eventual LCP adapter statement is exactly:

```lean
∃ M : LefschetzCompactPolyhedron.FiniteChainEndomorphism,
  (∀ k, M.chainTrace k = 0) ∧
    LefschetzCompactPolyhedron.HomologyModels M g
```

It will build `M.C` via `ChainComplex.of` from `signedDeletion_sq_zero`, use the
two finiteness leaves, obtain finite homology through the quasi-isomorphism, and
take `M.φ` to be the concrete subdivision/vertex-map composite.

## C1–C10

- `signedDeletion_exists`: C1 erased faces remain faces/nonempty; C2 formula not conclusion; C3 construction only; C4 every term; C5 exact `d`; C6 faithful; C7 order fixes signs; C8 degree zero/empty K; C9 new; C10 matches.
- `signedDeletion_sq_zero`: C1 paired deletion cancellation; C2 only formula assumed; C3 one identity; C4 both orders; C5 exact `d`; C6 faithful; C7 index shift checked; C8 bottom degree; C9 new; C10 matches.
- `faceModule_finiteDimensional`: C1 finite subtype; C2 no conclusion assumed; C3 one fact; C4 all k; C5 exact module; C6–7 faithful; C8 empty basis; C9 new; C10 matches.
- `faceModule_zero_above`: C1 maximum cardinality; C2 bound constructed; C3 one fact; C4 empty faces; C5 exact module; C6–7 faithful; C8 empty/dimension zero; C9 new; C10 matches.
- `affineComparison_exists_and_commutes`: C1 affine boundary formula; C2 generator formula fixes comparison; C3 no quasi-iso; C4 all faces; C5 actual singular complex; C6 faithful; C7 same sign order; C8 vertices/empty K; C9 new; C10 matches.
- `orderedFace_singular_quasiIso`: C1 standard theorem; C2 comparison fixed; C3 marked LIBRARY; C4 disconnected cases; C5 actual map; C6 no connectedness; C7 ℚ; C8 empty/isolated vertices; C9 new; C10 matches.

## Compile gate

Direct compilation reports zero errors and exactly six sorry warnings (the six
leaves above).  No SphereCap/LinearGraphMeasure, LCP, or geometric-subdivision
module was added or edited.

## Review (claude-14, 2026-10-28)

Accepted. Truth of `orderedFace_singular_quasiIso` for an ARBITRARY `cmp` satisfying `IsAffineComparison` + `hchain` (not only the affine one): `IsAffineComparison` forces each vertex to the constant simplex at that vertex, and every face's image lies in its closed face, which is contractible; by acyclic carriers any two such chain maps are chain homotopic, so their homology maps agree and bijectivity is independent of the choice. A seat may prove it for the affine `cmp` first and transfer by that argument.
Open (next split): concrete subdivision chain map `C(K) → C(sd K)` and vertex-map chain map `C(K') → C(K)` with basis formulas, zero diagonal of the composite under carrier avoidance, their comparison squares, and the LCP adapter.
