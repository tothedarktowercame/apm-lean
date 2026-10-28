# Ordered faces versus singular chains

## Triage and route

The target statement is true at its stated generality.  In particular, it must
hold for **any** `cmp` satisfying `IsAffineComparison` and the chain-map square:
each basis face is carried by its closed convex hull, and those hulls are
contractible, so the acyclic-carriers theorem makes all such comparisons chain
homotopic.

This split chooses route **(C), acyclic carriers plus subdivision**.  Route (A)
would require a new singular Mayer--Vietoris comparison for closed face
attachments (the existing `RP3Homology.rationalMayerVietoris` is for open
covers).  Route (B) would require the currently absent relative ordered-face
complex and its relative comparison theorem.  Route (C) can use the already
available chain-map calculations
`CoefficientSingularSubdivision.singularSubdivisionDegree_comm_d`,
`CoefficientSingularSubdivision.generator_formula`,
`CoefficientBarycentricNaturality.vertexSubdivision_comm_d`, and
`CoefficientBarycentricNaturality.vertexSubdivision_affine_natural`.

The imported subdivision library still lacks the decisive bridge from its
full vertex-chain complex to `FaceModule K`: it has no theorem identifying the
ordered-face subcomplex and no small-chain quasi-isomorphism specialized to a
finite geometric complex.  This is recorded as a LIBRARY leaf below rather
than hidden in an ordinary seat.

## Statement ladder and assembly

The final theorem has the identical binders, hypotheses, and conclusion of
`OrientedSimplicialChains.orderedFace_singular_quasiIso`.  Its proof extracts a
reference comparison from `affine_reference_quasiIso_exists`, rewrites the
given comparison's homology map using
`affineComparison_homologyMap_eq`, and applies the reference bijectivity.
Thus the assembly is sorry-free and neither leaf uses the other.

| Leaf | Actual claim and proof route | Estimate | Independence / status |
|---|---|---:|---|
| `affine_reference_quasiIso_exists` | There exists a face-carried chain map whose induced maps are bijective.  Build it from affine face simplices; use `CoefficientSingularSubdivision.singularSubdivisionDegree_comm_d` and `generator_formula`, `CoefficientBarycentricNaturality.vertexSubdivision_comm_d` and `vertexSubdivision_affine_natural`, and the finite-subdivision results `GeometricSimplicialSubdivision.barycentricSubdivision_finite`, `barycentricSubdivision_space`, and `exists_fine_subdivision`.  The missing ordered-face/small-chain bridge makes this about 350--500 lines. | 350--500 | independent; **LIBRARY** |
| `affineComparison_homologyMap_eq` | Any two chain maps whose basis images fill exactly the corresponding closed face hull induce equal homology maps.  Construct the carrier homotopy inductively on degree, filling cycles in each convex hull by the straight-line cone/prism; conclude with Mathlib's homology-map invariance under homotopy (or the corresponding `HomologicalComplex` boundary calculation). | 180--280 | independent; possibly **LIBRARY** until a reusable algebraic acyclic-carriers theorem exists |

Dependency layers: both leaves are layer 0 and can be proved in parallel; the
sorry-free final theorem is layer 1.

## Why the leaves are not placeholders or overloaded

The reference leaf constructs one concrete quasi-isomorphism but says nothing
about an arbitrary comparison.  The carrier leaf proves only equality of two
induced maps and says nothing about bijectivity.  Neither conclusion repeats a
hypothesis, and neither leaf implies the target without the other.

The existential in the reference leaf packages its chain-map proof together
with the witness.  This is intentional: the final assembly does not call the
currently sorry-backed `affineCmp_comm`, so its only nonstandard axiom sources
are the two new leaves.  The witness is not consumed by a sibling leaf; the
generic carrier leaf accepts both comparisons and their exact chain squares as
parameters.

## C1--C10 checks

### `affine_reference_quasiIso_exists`

- **C1:** This is the standard finite-simplicial-complex comparison theorem over
  `ℚ`; geometric subdivision preserves `K.space`.
- **C2:** No hypothesis supplies a comparison, inverse, or bijectivity.
- **C3:** It is the remaining large subdivision/small-chain foundation and is
  explicitly marked LIBRARY; it does not include independence of arbitrary
  comparisons.
- **C4:** The reference map, its chain square, and bijectivity are packaged
  together, so the assembly has every proof argument needed by
  `ChainComplex.ofHom`.
- **C5:** The witness has exactly the `FaceModule` components and singular-chain
  codomain consumed by the target.
- **C6:** Finiteness is exactly `hK`; no connectedness or purity hypothesis is
  added.
- **C7:** Coefficients are `ℚ`, degrees are homological `ℕ`, and the supplied
  signed deletion uses the same ambient order `o`.
- **C8:** Empty `K` gives zero complexes; one vertex gives `ℚ` in degree zero;
  two isolated vertices give `ℚ²`; boundary of a triangle gives `H₁ = ℚ`; a
  filled triangle is acyclic above degree zero.
- **C9:** Unlike the ancestor target, this asserts existence of one reference
  comparison, not that every comparison is a quasi-isomorphism.  Unlike
  `affineComparison_exists_and_commutes`, it additionally proves bijectivity.
- **C10:** The Lean statement packages precisely the witness, carrier condition,
  chain square, and degreewise bijectivity described here.

### `affineComparison_homologyMap_eq`

- **C1:** Closed convex hulls are nonempty for every `FaceIndex`; facewise cone
  fillings prove the acyclic-carrier uniqueness theorem.
- **C2:** Equality of homology maps is not assumed; only carrier and chain-map
  conditions are supplied.
- **C3:** It proves invariance only, not either map's bijectivity.
- **C4:** Both maps share the exact source differential `d`, and both chain
  squares are explicit hypotheses.
- **C5:** The conclusion compares the exact `ChainComplex.ofHom` maps used by
  the consumer, including their proof arguments (proof irrelevance handles
  those arguments).
- **C6:** No finiteness is required for carrier uniqueness, and none is added.
- **C7:** The hull equality in `IsAffineComparison` fixes the carrier; signs are
  already controlled by the two chain squares.
- **C8:** In degree zero, `IsAffineComparison` sends a vertex to the constant
  simplex at that vertex.  Empty complexes are vacuous; disconnected complexes
  remain componentwise, so two vertices are not accidentally identified.
- **C9:** The ancestor concludes bijectivity; this concludes equality of maps
  for a pair of comparisons and is a genuine transfer theorem.
- **C10:** The prose and Lean both state equality of induced homology maps, not
  equality of chain maps.

## Truth-case audit

- Single vertex: the reference and arbitrary comparisons send its generator to
  the constant singular 0-simplex; both homologies are `ℚ` in degree zero.
- Two vertices: carrier fillings never cross components, so `H₀ = ℚ²`.
- Triangle boundary: subdivision/small chains preserve its single rational
  1-cycle, giving `H₁ = ℚ`.
- Filled 2-simplex: its convex carrier contracts positive-degree cycles.
- Degree zero convention: `stdSimplex ℝ (Fin 1)` is a point, and the range
  condition forces the constant simplex at the unique face vertex.

## Compile gate

`lake env lean ConstructionTargets/SimplicialSingularComparison.lean` under the
required lock and 12G systemd scope reports zero errors and exactly two sorry
warnings, one for each leaf.  The final `#print axioms` reports
`[propext, sorryAx, Classical.choice, Quot.sound]`; inspection of the assembly
shows `sorryAx` enters only through the two leaves above.

No import or declaration from `SphereCap*` or `LinearGraphMeasure` is used.

## Doubts / missing foundation

The main uncertainty is size, not truth.  Without a reusable acyclic-carriers
theorem, the second leaf may grow beyond 280 lines and should then be split into
a generic carrier-homotopy construction and a 30--60-line homology-invariance
corollary.  The first leaf is definitely LIBRARY-sized until the ordered-face
small-chain bridge is implemented; pretending the existing subdivision chain
maps alone close that gap would be incorrect.
