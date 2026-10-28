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

### `lefschetzNumber_eq_zero_of_faceAvoiding` — LIBRARY, 1000–1800 lines

For a specified finite triangulation, a face-avoiding map with Lefschetz number
`L` has `L = 0`.  Construct the finite oriented simplicial chain complex over
`ℚ`; simplicial approximation gives a chain map whose diagonal entries vanish
by `FaceAvoiding`, hence every chain trace is zero.  Apply the finite Hopf trace
formula, then transport from simplicial homology to the singular homology used
by `RationalLefschetz.Homology`.  Build the comparison on the existing singular
simplex machinery in `CoefficientSimplicialChainFinsupp*`, subdivision from
`CoefficientSingularSubdivision.lean`, naturality from
`CoefficientBarycentricNaturality.lean`, and the homology infrastructure in
`CoefficientSubcomplexRelative*`.  The comparison theorem and finite Hopf
trace formula do not yet exist as repo declarations, so this leaf is genuinely
LIBRARY rather than hiding them in a hypothesis.

Independent.  C1: avoidance of every closed simplex forces every diagonal
simplex coefficient to vanish. C2: neither `FaceAvoiding` nor `HasLefschetzNumber`
contains `L = 0`. C3: this is the algebraic/comparison half only; it does not
produce an approximation or fixed point. C4: it accepts the exact geometric
output of the first leaf. C5: `K`, `e`, and `g` are explicit. C6: no extra
assumption beyond the public triangulation. C7: the alternating sign is
`(-1 : ℚ)^k`, matching `HasLefschetzNumber`. C8: the empty complex has zero
chain complex; dimension zero reduces to the diagonal of vertices. C9: no
ancestor states this comparison. C10: exact match.

## Assembly

`fixedPointOfNonzeroLefschetz` is sorry-free.  Assuming no fixed point, unpack
the explicit triangulation, obtain the homotopic face-avoiding `g`, transport
the Lefschetz certificate to `g`, and deduce `L = 0`, contradicting `L ≠ 0`.

Dependency layer 1 contains all three leaves in parallel.  The public theorem
is layer 2.

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

Main doubt: the theorem leaves are mathematically standard, but Mathlib lacks
the geometric subdivision and simplicial/singular comparison layers.  The
adapter estimates assume a reusable finite-Δ-complex-to-geometric-complex
construction; without it each quotient adapter would be substantially larger.

## Review fix (claude-14, 2026-10-28)

The split's first leaf, `fixedPointFree_homotopic_faceAvoiding`, asked for a map homotopic to `f` that is face-avoiding with respect to the ORIGINAL complex `K`. The standard proof only gives face avoidance after subdividing `K` to small mesh, and I could not confirm the coarse-`K` version is true. It is replaced by three leaves, and the assembly now uses `f` itself:

- `fixedPointFree_uniform_separation` (40-80): `K.space` is compact (a finite union of convex hulls of finite sets), so `x ↦ dist (e x) (e (f x))` is a continuous positive function on compact `X` and has a positive minimum (`IsCompact.exists_isMinOn`; empty `X`: take `ε = 1`).
- `exists_fine_subdivision` (LIBRARY, barycentric subdivision of a geometric simplicial complex: Mathlib has `Geometry.SimplicialComplex` but no subdivision; iterate barycentric subdivision, mesh shrinks by `d/(d+1)`).
- `faceAvoiding_of_fine` (30-60): `x, f x ∈ convexHull s` gives `dist ≤ diam < ε ≤ dist` (`Metric.dist_le_diam_of_mem`, boundedness from `Set.Finite.isBounded` + `convexHull` of a bounded set is bounded).

`fixedPointOfNonzeroLefschetz` subdivides to mesh `< ε`, transports `e` along `K'.space = K.space` (`Homeomorph.setCongr`), and applies `lefschetzNumber_eq_zero_of_faceAvoiding` to `f` itself. `hasLefschetzNumber_of_homotopic` is no longer used by the assembly; it stays as a leaf because the proof of `lefschetzNumber_eq_zero_of_faceAvoiding` (simplicial approximation of `g`) will need it.
Truth: `lefschetzNumber_eq_zero_of_faceAvoiding` is true because a face-avoiding map has no fixed point (each point lies in some face) and the Lefschetz theorem holds; its proof is the Hopf-trace + comparison program and needs its own split.
