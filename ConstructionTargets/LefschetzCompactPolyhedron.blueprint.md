# Rational Lefschetz theorem for finite polyhedra

## Triage and choice of hypothesis

The theorem is true.  `IsFinitePolyhedron X` means that `X` is homeomorphic to
the realization `K.space` of a geometric simplicial complex in some finite
Euclidean space and that `K.faces` is finite.  This was chosen over a custom
finite Δ-complex because Mathlib already supplies `Geometry.SimplicialComplex`,
`Geometry.SimplicialComplex.space`, convex hulls, and the face-intersection
theorem.  It was chosen over “compact retract of a polyhedron” because the
retract version makes the Lefschetz proof harder without making the polygon
quotient adapters simpler.

This hypothesis is geometric, not a disguised fixed-point property.  It gives
the proof an actual finite chain complex.  The cost is that each quotient model
needs a triangulation adapter.  Polygon quotients, finite point wedges, and a
single disk attachment all have finite Δ-complex presentations; barycentric
subdivision converts those presentations to finite geometric complexes.

`FaceAvoiding K e g` says exactly that every point of a closed simplex is sent
outside that same simplex.  Thus the diagonal coefficient of the associated
simplicial chain map is zero.  It does not assert a Lefschetz number or a fixed
point conclusion.

## Leaf statements and proof plans

### `fixedPointFree_homotopic_faceAvoiding` — LIBRARY, 700–1200 lines

For a specified finite complex and homeomorphism, a fixed-point-free continuous
map is homotopic to a face-avoiding map.  Prove compactness of `K.space` from
`hK` using finite unions and `isCompact_convexHull`; the continuous positive
function `x ↦ dist (e x) (e (f x))` has a positive minimum.  Iterated
barycentric subdivision gives mesh smaller than the corresponding Lebesgue
number.  Apply the simplicial approximation construction and its straight-line
homotopy simplex by simplex.  The star choice and the separation bound imply
the stated closed-simplex avoidance.  Mathlib starting points:
`Geometry.SimplicialComplex.space`,
`Geometry.SimplicialComplex.convexHull_inter_convexHull`,
`isCompact_convexHull`, `IsCompact.exists_isMinOn`, and uniform continuity on
compact sets.  Mathlib currently has no barycentric-subdivision/simplicial-
approximation implementation for this geometric complex, so this is genuinely
LIBRARY.

Independent of both other leaves.  C1: compactness follows from finite faces;
the uniform separation is unavailable only when a fixed point exists. C2: the
hypothesis is fixed-point-freeness, not face avoidance. C3: this is only the
geometric approximation half, not the trace theorem. C4: the output is exactly
what the trace leaf consumes. C5: `K` and `e` are explicit parameters. C6:
finite triangulability is the public hypothesis. C7: distances are real and no
truncated subtraction is involved. C8: for the empty realization no self-map
exists; the implication is harmless; dimension zero works by the same finite
separation argument. C9: no ancestor has this conclusion. C10: prose matches
the Lean statement.

### `hasLefschetzNumber_of_homotopic` — 40–80 lines

Homotopic maps have the same `HasLefschetzNumber`.  Preserve the supplied
finite-dimensional instances and bound, and rewrite every induced endomorphism
using
`ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic`.
Then the finite trace sum is unchanged.

Independent.  C1: the cited theorem is sorry-free and works over `ModuleCat ℚ`.
C2: homotopy is strictly weaker than equality and does not restate the result.
C3: this is a finite-sum rewrite only. C4–C5: it returns exactly the predicate
needed by the trace leaf, for the same map `g`. C6: no extra geometry. C7: the
direction of homotopy does not matter for equality. C8: empty and zero-dimensional
spaces are covered functorially. C9: not an ancestor repeat. C10: exact match.

### Split of `lefschetzNumber_eq_zero_of_faceAvoiding`

The file now defines `FiniteChainEndomorphism`, a bounded degreewise
finite-dimensional rational chain complex with an endomorphism, and its chain
and homology traces.  This is data, not a proposition encoding the desired
equality; in particular it has no field mentioning a Lefschetz number.

#### `HomologyModels` — definition (no `sorry`)

`HomologyModels M g` supplies degreewise linear equivalences from the model's
homology to singular homology and says that they intertwine the two
endomorphisms.  It deliberately does **not** mention traces.  This prevents the
comparison interface from merely renaming the desired trace equality.

#### `faceAvoiding_uniform_carrier_margin` — 90–150 lines, independent

Finite many compact closed faces and pointwise face avoidance give one
`δ > 0` separating `g x` from every point of the face containing `x`.  Prove
compactness with `isCompact_convexHull`, finite-union compactness, compactness
of `K.space`, continuity of distance, and a finite minimum over faces.  The
empty realization is handled separately (take `δ = 1`); empty faces contribute
no points.

C1: the margin is over the compact incidence set `(s,x,y)`, and finiteness is
essential. C2: pointwise nonmembership does not restate a positive uniform
distance. C3: only compactness/separation, no chains. C4–C5: its exact `δ` and
inequality are passed to the model leaf. C6: no stronger avoidance is assumed.
C7: ordinary real distance. C8: empty space/empty face are vacuous; a one-vertex
complex admits no `havoid`. C9: the ancestor returned a chain model, not a
metric margin. C10: matches the quantified `y` in Lean.

#### `exists_carrier_avoiding_oriented_chain_model` — LIBRARY, 450–750 lines

From an explicit positive carrier margin, construct a fine barycentric
subdivision `K'`, a carrier-avoiding simplicial approximation `h`, the ordered
or oriented rational chains of `K`, the subdivision chain map `sd`, and
`φ = h_# ≫ sd` (with the categorical composition order checked in the proof).
The ordered simplex basis is finite in each degree and empty above the maximum
face cardinality, supplying `finiteChain`, `finiteHomology`, and `chainAbove`.
Carrier avoidance makes every diagonal coefficient zero.  The direct
simplicial-simplex realization map to singular chains is a chain-homotopy
equivalence and gives the degreewise equivalences and intertwining equation in
`HomologyModels`.

Build on the sorry-free declarations
`CoefficientSimplicialChainFinsuppNaturality.chainsMap_component_finsupp_naturality`,
`CoefficientSimplicialChainFinsuppRange.chainsMap_component_range_finsupp`,
`CoefficientSingularSubdivision.singularSubdivision`,
`CoefficientSingularSubdivision.singularSubdivision_natural`,
`CoefficientBarycentricNaturality.vertexSubdivision_affine_natural`, and
`CoefficientAffineNaturality.vertexRealization_affine_natural`.  The missing
foundation is specifically the geometric `SimplicialComplex` barycentric
subdivision plus simplicial-approximation/carrier construction; Mathlib's
coefficient chain operators begin only after that data exists.  This is why
this residual piece is honestly LIBRARY rather than split into false
independently statable claims about a nonexistent canonical `K'`.

The star condition uses two inputs: uniform continuity of `g` on compact
`K.space` controls `g(st v) ⊆ st(h v)`, while the explicit `hmargin` controls
carrier avoidance after making the subdivision mesh smaller than `δ`.

C1: the supplied margin is exactly strong enough for closed carriers. C2:
`HomologyModels` is conjugacy data, not trace equality. C3: this remains the one
declared missing library foundation; it does not contain the trace algebra,
Hopf formula, or Lefschetz sum. C4–C5: it returns precisely `M`, zero chain
traces, and the comparison equivalences consumed downstream. C6: the metric
hypothesis was derived from the public assumptions. C7: changing orientations
conjugates by diagonal signs, so diagonal zero and trace are invariant. C8:
empty realization gives the zero complex; dimension zero is logically valid
though `hmargin` cannot arise for a nonempty vertex-only self-map. C9: stronger
structural conjugacy, but no trace conclusion of the ancestor. C10: exact Lean
output is `∃ M, (∀k, chainTrace=0) ∧ HomologyModels M g`.

#### `homologyTrace_eq_of_models` — 35–70 lines, independent algebra

Unpack the degreewise equivalence and intertwining equation.  Apply trace
invariance under conjugacy, using `LinearMap.trace_conj'` (or equivalently
`LinearMap.trace_comp_comm` twice), installing `M.finiteHomology k`; finite
dimensionality of `Homology X k` follows through the equivalence.

C1: conjugate finite-dimensional maps have equal trace. C2: the hypothesis is
an actual intertwiner and contains no trace equation. C3: one-degree linear
algebra only. C4–C5: conclusion is exactly the original consumer's trace
equation for `induced g k`. C6: no geometry. C7: composition direction is
spelled out in `HomologyModels`. C8: zero-dimensional vector spaces work. C9:
not the model-existence ancestor. C10: matches Lean.

#### `exists_faceAvoiding_simplicial_trace_model` — sorry-free assembly

Obtain the uniform margin, obtain the oriented model and its conjugacy
certificate, then apply `homologyTrace_eq_of_models`.  Thus `sorryAx` reaches
this declaration only through the three new leaves, never through another
leaf's proof.

#### `hopf_trace_formula` — 120–180 lines

For `FiniteChainEndomorphism M`, prove that the alternating trace on homology
equals the alternating chain trace through `M.bound`.  Split each finite
dimensional chain group into boundaries, homology representatives, and a
complement mapping isomorphically onto boundaries one degree lower; off-diagonal
blocks do not affect trace and boundary traces telescope.  Use
`LinearMap.trace_conj'`, `LinearMap.trace_comp_comm`, the homology short exact
sequences for `HomologicalComplex`, and finite-dimensional complements.

Independent. C1: boundedness kills the terminal boundary term and makes the
finite formula true. C2: its hypotheses are structural fields, not its
conclusion. C3: this is pure linear algebra and knows nothing about spaces or
face avoidance. C4: the range is exactly the model bound. C5: the endomorphism
is `M.φ` on both chain and homology. C6: no geometric hypothesis is added. C7:
the sign is exactly `(-1 : ℚ)^k`. C8: the zero complex and bound zero work;
degree zero has no lower boundary term. C9: no ancestor is an abstract Hopf
trace theorem. C10: exact match.

#### `lefschetzNumber_eq_model_homology_trace` — 80–140 lines

Reconcile the arbitrary bound in `HasLefschetzNumber g L` with `M.bound`, then
rewrite each summand by `htrace`.  Above `M.bound`, `M.chainAbove` implies zero
homology; above the certificate's bound the singular homology is subsingleton.
Pad both sums to the maximum of the bounds and use `LinearMap.trace_eq_zero_of_subsingleton`.

Independent of the construction and Hopf leaves: it takes their eventual
trace equality explicitly. C1: the two vanishing hypotheses justify changing
bounds. C2: `htrace` is degreewise naturality, not the alternating-sum
conclusion. C3: only finite-sum padding/rewrite remains. C4: it yields precisely
the first equality in the assembly. C5: both sides use the named map `g`. C6:
no geometry. C7: the exponent/sign is copied byte-for-byte from
`HasLefschetzNumber`. C8: bound zero and subsingleton homology are included.
C9: no ancestor is a bound-reconciliation statement. C10: exact match.

`lefschetzNumber_eq_zero_of_faceAvoiding` is now sorry-free: obtain the model,
rewrite `L` as its alternating homology trace, apply Hopf trace, and use the
degreewise zero chain traces.

## Assembly

`fixedPointOfNonzeroLefschetz` is sorry-free.  Assuming no fixed point, unpack
the explicit triangulation, obtain the homotopic face-avoiding `g`, transport
the Lefschetz certificate to `g`, and deduce `L = 0`, contradicting `L ≠ 0`.

For this re-split, the three new leaves are all independently provable: the
comparison leaf constructs the model, while the other two quantify over an
arbitrary supplied model (and the bound leaf takes trace naturality explicitly).
Their sorry-free assembly is the next layer.  The earlier subdivision,
separation, fine-face, and homotopy leaves keep their prior dependency status;
the public theorem remains the final layer.

## Consumer adapters

The first consumer has the leaf:

```lean
theorem t96A02_projectivePlaneWedge_isFinitePolyhedron :
    IsFinitePolyhedron ProjectivePlaneWedge
```

Estimate: LIBRARY, 350–650 lines.  Triangulate the standard polygon disk so the
`aa` edge pairing is simplicial after subdivision, descend it to `Surface false
1`, take two finite complexes and identify the chosen center vertices.  Build
on `Surfaces.PairingData`, its quotient map, and
`PointWedgeQuotient.Wedge`.  This adapter is independent of the three theorem
leaves.

The later adapters should be stated as:

```lean
theorem apm_t02A04_isFinitePolyhedron :
    IsFinitePolyhedron apm_t02a04_X

theorem t99A03_fourProjectivePlanesWedge_isFinitePolyhedron :
    IsFinitePolyhedron T99A03.FourProjectivePlanesWedge
```

The t02A04 adapter is estimated at 300–550 lines: triangulate the solid torus
and the attached disk compatibly with the PL attaching map `z ↦ (z,z²)`, then
use the finite pushout triangulation.  The t99A03 adapter is 100–180 lines once
the t96A02 adapter and a generic finite point-wedge triangulation lemma exist.
Both are LIBRARY adapters, independent of the Lefschetz leaves.

## Truth checks

* A point satisfies `IsFinitePolyhedron`; its identity has `L = 1` and a fixed
  point.
* A nontrivial rotation of `S¹` is fixed-point-free and has `L = 0`; the theorem
  does not apply because `L ≠ 0` fails.
* The antipodal map of `S²` has `L = 1 + (-1)^3 = 0`, so again the nonzero
  hypothesis fails.
* A constant self-map of a nonempty finite polyhedron has `L = 1` and fixes its
  image point.
* `ℝ` cannot satisfy `IsFinitePolyhedron`: a finite realization is compact,
  whereas `ℝ` is not.  Thus translation of `ℝ`, despite its formal Lefschetz
  value `1`, is excluded.
* For the boundary of a triangle, subdivide finely enough and take the
  half-turn rotation.  No closed fine edge meets its image; the chain diagonal
  is zero and the circle Lefschetz number is `1 - 1 = 0`.
* For a single vertex, `FaceAvoiding` is impossible: applying it to the unique
  point and vertex face says that same vertex is both in and not in its convex
  hull.  Thus no leaf asserts existence of a face-avoiding self-map there.
* The alternating convention in every new sum is `(-1 : ℚ)^k * trace`, exactly
  the convention in `HasLefschetzNumber`.  Reversing a simplex orientation
  conjugates its matrix by signs, leaving the trace (and zero diagonal) fixed.

Main doubt: the theorem leaves are mathematically standard, but Mathlib lacks
the geometric subdivision and direct simplicial/singular comparison layers.  The
adapter estimates assume a reusable finite-Δ-complex-to-geometric-complex
construction; without it each quotient adapter would be substantially larger.

## Review fix (claude-14, 2026-10-28)

The split's first leaf, `fixedPointFree_homotopic_faceAvoiding`, asked for a map homotopic to `f` that is face-avoiding with respect to the ORIGINAL complex `K`. The standard proof only gives face avoidance after subdividing `K` to small mesh, and I could not confirm the coarse-`K` version is true. It is replaced by three leaves, and the assembly now uses `f` itself:

- `fixedPointFree_uniform_separation` (40-80): `K.space` is compact (a finite union of convex hulls of finite sets), so `x ↦ dist (e x) (e (f x))` is a continuous positive function on compact `X` and has a positive minimum (`IsCompact.exists_isMinOn`; empty `X`: take `ε = 1`).
- `exists_fine_subdivision` (LIBRARY, barycentric subdivision of a geometric simplicial complex: Mathlib has `Geometry.SimplicialComplex` but no subdivision; iterate barycentric subdivision, mesh shrinks by `d/(d+1)`).
- `faceAvoiding_of_fine` (30-60): `x, f x ∈ convexHull s` gives `dist ≤ diam < ε ≤ dist` (`Metric.dist_le_diam_of_mem`, boundedness from `Set.Finite.isBounded` + `convexHull` of a bounded set is bounded).

`fixedPointOfNonzeroLefschetz` subdivides to mesh `< ε`, transports `e` along `K'.space = K.space` (`Homeomorph.setCongr`), and applies `lefschetzNumber_eq_zero_of_faceAvoiding` to `f` itself. `hasLefschetzNumber_of_homotopic` is no longer used by the assembly; it stays as a leaf because the proof of `lefschetzNumber_eq_zero_of_faceAvoiding` (simplicial approximation of `g`) will need it.
Truth: `lefschetzNumber_eq_zero_of_faceAvoiding` is true because a face-avoiding map has no fixed point (each point lies in some face) and the Lefschetz theorem holds; its proof is the Hopf-trace + comparison program and needs its own split.
