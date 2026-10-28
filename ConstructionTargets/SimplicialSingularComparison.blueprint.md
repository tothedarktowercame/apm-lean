# Ordered faces versus singular chains

## Triage and correction to route C

The target is true, including the empty complex and degree zero. The reference
map is now the concrete `OrientedSimplicialChains.affineCmp`; AC1--AC3 provide
its basis formula, carrier condition, and chain square.

A fixed choice `c : K.space → K.vertices` does **not** give the proposed map
from open-star-small singular simplices by sending the chosen vertex tuple to a
face and nonfaces to zero. Although choices commute with taking a singular
face, a tuple which is not a face can have codimension-one subtuples which are
faces, so the zero image can have nonzero prescribed boundary. The repair is
the standard one: subdivide sufficiently and use a compatible simplicial
approximation (or construct it inductively by dimension), then use an
acyclic-carrier prism. The existing
`CoefficientSmallComparison.inclusion_isIso`, `homologyIso_hom`,
`inverse_left`, and `inverse_right` identify open-cover-small homology with all
singular homology.

## Statement ladder

`affine_reference_quasiIso_exists` keeps its statement byte-identical and is a
sorry-free assembly: choose `affineCmp`, discharge `IsAffineComparison` using
`affineCmp_single` and `faceSimplex_range`, use `affineCmp_comm` for the chain
square, and combine the two new leaves below. The separately queued
`affineComparison_homologyMap_eq` is unchanged.

| Leaf | Claim and tools | Estimate | Independence / building on |
|---|---|---:|---|
| `affineCmp_homologyMap_injective` | Injectivity in degree `k`. Represent a null image by an open-star-small bounding chain via `CoefficientEventualSmallness.actual_chain_eventual`; use `CoefficientSmallComparison.inclusion_isIso` and `inverse_left`; construct the compatible subdivided approximation back to ordered faces; the carrier prism shows the original ordered cycle bounds. Use `GeometricSimplicialSubdivision.openStar`, `exists_vertexMap_of_mesh_lt_lebesgue`, `CoefficientSingularSubdivision.singularSubdivisionDegree_comm_d`, and `CoefficientBarycentricNaturality.vertexSubdivision_comm_d`. | 140--200 | independent of surjectivity; builds on AC1--AC3 and the sorry-free small-chain library |
| `affineCmp_homologyMap_surjective` | Surjectivity in degree `k`. Subdivide a representative cycle until open-star-small, apply the compatible approximation to obtain an ordered-face cycle, and use the carrier prism plus `CoefficientSmallComparison.inverse_right` to identify its affine image with the original class. Same subdivision and star tools. | 140--200 | independent of injectivity; builds on AC1--AC3 and the sorry-free small-chain library |
| `affineComparison_homologyMap_eq` | Any two face-carried chain maps induce equal homology maps, by the facewise convex acyclic-carrier homotopy. | 180--280 | independent, pre-existing and queued to another seat; untouched here |

Dependency layers: the injective and surjective leaves are layer 0 and can be
proved in parallel. The reference existential is a small layer-1 assembly. The
final theorem additionally consumes the independent carrier-invariance leaf.

The new leaves share no sibling conclusion. Splitting by injectivity and
surjectivity avoids an abstract “inverse data” hypothesis which would merely
restate quasi-isomorphism. Each seat performs one direction of the
small-chain/subdivision argument, not the whole comparison theorem.

## C1--C10 checks

### `affineCmp_homologyMap_injective`

- **C1:** Standard simplicial/singular comparison injectivity; finiteness gives the uniform subdivision and open-star cover.
- **C2:** No null-homology reflection or inverse is assumed.
- **C3:** Only one degree and one direction are proved; surjectivity and carrier invariance are absent.
- **C4:** `hdd` builds the source complex and AC3 supplies the exact chain map.
- **C5:** The conclusion is the precise `ChainComplex.ofHom` map used by the assembly.
- **C6:** No purity, connectedness, or nonemptiness hypothesis is added.
- **C7:** Homological degrees are `ℕ`; coefficients and signs are `ℚ` and `o`.
- **C8:** Empty source is injective; a single vertex is identity on `ℚ`; two vertices remain separated; degree zero needs no predecessor degree.
- **C9:** Unlike the ancestor it proves neither existence nor bijectivity, only injectivity of the defined concrete map.
- **C10:** The prose describes exactly this concrete degreewise map.

### `affineCmp_homologyMap_surjective`

- **C1:** Small-chain inclusion is an isomorphism for the open-star cover, and compatible approximation supplies a face representative.
- **C2:** No representative lift or surjectivity is assumed.
- **C3:** Only one degree and one direction are proved.
- **C4:** Subdivision preserves cycles and the carrier prism identifies the affine image; `inverse_right` returns to full homology.
- **C5:** The preimage belongs to the exact ordered-face homology object in the conclusion.
- **C6:** Uses precisely finiteness, signed deletion, and square-zero from the registered statement.
- **C7:** Choice is made after compatible subdivision; no invalid pointwise nonface-to-zero convention is used.
- **C8:** Empty space gives zero chains; one vertex gives `H₀ = ℚ`; two vertices give `ℚ²`; triangle boundary gives `H₁ = ℚ`; a filled triangle has no positive homology; degree zero uses the H0 branch of `inclusion_isIso`.
- **C9:** One direction for the concrete map is not the ancestor's theorem for every carried comparison.
- **C10:** Prose and Lean both state degreewise surjectivity.

The unchanged carrier leaf retains its prior audit: convex face hulls are
nonempty for indexed faces, equality is not assumed, it proves equality only
(not bijectivity), and empty/disconnected/degree-zero cases remain facewise.

## Truth-case audit

- Single vertex: `affineCmp` induces the identity on `ℚ` in degree zero.
- Two isolated vertices: the disjoint star carriers give `ℚ²`.
- Triangle boundary: compatible subdivision preserves its rational 1-cycle.
- Filled triangle: its convex carrier kills positive-degree homology.
- Degree zero: the small-chain theorem has an explicit H0 case; no fictitious degree `-1` occurs.

## Compile gate and doubts

The scoped compile reports zero errors and exactly three sorry warnings: the
two new directional leaves and unchanged `affineComparison_homologyMap_eq`.
`#print axioms` reports `[propext, sorryAx, Classical.choice, Quot.sound]`;
within this file `sorryAx` reaches the final theorem only through these leaves
(AC2/AC3 are upstream conclusions explicitly permitted by the packet).

The remaining risk is implementation size. The repository has the small-chain
isomorphism and geometric star/subdivision ingredients, but no ready-made
ordered-face approximation chain map. If either proof exceeds 200 lines, the
genuine shared missing foundation is a reusable compatible
approximation/carrier-prism construction; it should become a **LIBRARY** module
which does not import `SimplicialChainMaps`, rather than reviving the false
point-choice map. No forbidden sphere-cap or linear-graph module is imported.
