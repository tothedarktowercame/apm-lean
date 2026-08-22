# Concrete singular-homology infrastructure checklist

This checklist tracks the route from Mathlib's abstract singular-chain functor
to the concrete computations needed by the APM corpus. An item is checked only
when its Lean declaration compiles without `sorryAx` and, where it introduces a
mathematical object, has a concrete anti-vacuity witness.

The priority order is deliberately fixed:

1. `Hₙ(S¹)`;
2. a Künneth or product computation;
3. `Hₙ(T²)`;
4. `Hₙ(Sⁿ)`.

## Available foundation at the pinned Mathlib revision

- [x] `AlgebraicTopology.singularChainComplexFunctor` constructs the singular
  chain complex of a topological space.
- [x] `AlgebraicTopology.singularHomologyFunctor` takes its homology with
  coefficients in an object of a preadditive category.
- [x] Totally disconnected spaces are computed in all degrees.
- [x] Simplicially homotopic maps induce equal maps on homology.
- [x] `SSet.S1` exists as the coequalizer of the two endpoints of `Δ[1]`.
- [ ] No existing concrete singular-homology computation for the topological
  circle, torus, or positive-dimensional sphere was found.
- [ ] No singular Mayer–Vietoris, excision, cellular/singular comparison, or
  Künneth theorem was found.
- [ ] Mathlib's singular-homology homotopy-invariance API initially stops at
  simplicial homotopies; the TopCat cylinder bridge is supplied locally below.

## Ground computation and homotopy bridge

- [x] Define ordinary integer-coefficient `SingularHomology n X` from the real
  Mathlib functor.
- [x] Compute `H₀(*) ≅ ℤ` (`pointH0IsoInt`).
- [x] Exhibit `pointH0Generator`, prove it maps to `1`, and prove it is nonzero.
- [x] Prove `Hₙ(*)` is zero for every `n > 0`.
- [x] Convert a TopCat cylinder homotopy into an `SSet.Homotopy`
  (`topCatHomotopyToSSet`).
- [x] Prove topologically homotopic maps induce equal maps on ordinary singular
  homology (`singularHomology_map_eq_of_topCatHomotopy`).
- [x] Package explicit inverse maps and cylinder homotopies as an isomorphism
  on singular homology (`singularHomologyIsoOfTopCatHomotopyEquivalence`).
- [x] Compute all singular homology groups of a contractible space from the
  point computation (`contractibleH0IsoInt`,
  `contractibleHigherHomology_isZero`).
- [x] Use the interval as a concrete witness, including a named nonzero
  zeroth-homology generator.

## Circle: concrete chain model

- [x] Define the one-vertex, one-edge cellular boundary in degree one.
- [x] Compute the resulting cellular-model `H₁` as `ℤ`.
- [x] Exhibit the oriented-edge generator and prove it is nonzero.
- [x] Package the full cellular circle chain complex in `AddCommGrpCat`, not
  merely its degree-one quotient (`circleCellularChainComplex`).
- [x] Compute its homology in degree zero, degree one, and all other degrees
  (`circleCellularModelH0IsoInt`, `circleCellularModelH1IsoInt`,
  `circleCellularModelHomology_isZero_of_ne_zero_one`).

These names retain `CellularModel` until a comparison theorem exists. The file
must never identify this algebraic model with singular homology by definition.

## Circle: comparison with genuine singular homology

There are three plausible routes. They are ordered by how much reusable
infrastructure they provide; the first route whose prerequisites close should
be used.

### Route decision (2026-08-19, approved by Joe)

**Route B first, then Route A as a layer on top of it.** A survey of the pinned
Mathlib revision found that none of the three routes has its prerequisites in
place: there is no excision, no singular Mayer-Vietoris (the only
`mayerVietoris` API is for sheaf cohomology), no Kunneth, no Eilenberg-Zilber
or Alexander-Whitney, and no CW structure on any circle or sphere. The
`sSetTopAdj` Quillen equivalence that Route C would lean on is an open TODO in
Mathlib itself.

The decisive correction to this section is that **A and B are not independent
alternatives**: the cellular/singular comparison of Route A rests on relative
homology and excision, which is Route B's trunk. So the missing
relative-homology/excision layer is shared, and building it first makes Route A
a cheap reusable front end rather than a competing foundation.

Route C was declined: its cheap part (the algebraic `SSet.S1` computation) is
not the part we need, and its expensive part (realization versus singular
chains) is either a one-object result leaving nothing reusable, or Mathlib's own
open problem.

This decision would be wrong if a non-obvious existing quasi-isomorphism between
normalized chains of `X` and singular chains of `|X|` exists (making C cheaper),
or if a ready-made cellular relative-homology API exists under names the survey
missed (making A preferable). Neither was found.

Implementation order:

1. Relative singular chains and maps of pairs.
2. Short exact sequence and long exact sequence of a pair.
3. A quotient/suspension calculation, if it can compute the circle before full
   open-cover excision.
4. Subdivision and excision.
5. Mayer-Vietoris.
6. Cellular comparison as the reusable finite-CW front end.
7. Eilenberg-Zilber/Kunneth, developed separately.

### Route A: cellular/singular comparison

- [ ] Define the cellular filtration chain complex for a finite CW complex.
- [ ] Construct the comparison map from cellular chains to singular chains.
- [ ] Prove the comparison is a quasi-isomorphism for the one-cell circle.
- [ ] Identify the standard topological circle (`UnitAddCircle`, `Circle`, or
  `TopCat.sphere 1`) with that CW realization.

### Route B: Mayer–Vietoris

- [x] Define relative singular chains for a subspace inclusion
  (`relativeSingularSubcomplex`, `RelativeSingularChains`), prove the
  differential restricts, recover the absolute complex for `(X, ∅)`, and
  exhibit a nonzero relative chain for the proper pair `(Bool, {false})`.
- [x] Prove the short exact sequence underlying excision/Mayer–Vietoris
  (`singularSubspaceMap_mono`, `singularPairShortComplex_shortExact`).
- [x] Establish the long exact homology sequence
  (`singularPairConnecting`, `singularPairHomology_exact_subspace`,
  `singularPairHomology_exact_absolute`, `singularPairHomology_exact_relative`).
- [x] Compute `H₀` of a totally disconnected space directly as the coproduct
  of one coefficient object per point, naturally in maps; prove point
  inclusions are coproduct injections and the two-point collapse is the
  codiagonal (`directDiscreteH0Iso`,
  `directDiscreteH0Iso_boolCollapse_codiagonal`).
- [x] Exercise the pair LES on the interval endpoints: compute
  `H₁(I,∂I) ≅ ℤ` through the connecting map and the codiagonal kernel,
  and exhibit a named nonzero relative fundamental class
  (`intervalBoundaryRelativeH1IsoInt`,
  `intervalBoundaryRelativeH1Generator_ne_zero`).
- [x] Build the affine singular-simplex and generator-cone foundation for
  subdivision, including face restriction and the signed cone boundary
  identity (`affineSimplex`, `singularGenerator_boundary`,
  `coneGenerator_boundary`, `coneGenerator_vertex_boundary`).
- [x] Define recursive barycentric subdivision via the prepend-cone convention
  and prove its signed chain-map identity, with the standard-edge boundary
  check (`vertexSubdivision`, `vertexSubdivision_comm_d`,
  `affineSubdivision_boundary`, `affineSubdivision_edge_boundary`).
- [x] Construct the recursive prism and prove subdivision chain-homotopic to
  the identity, with the production standard-edge generator check
  (`vertexPrism`, `vertexPrism_identity`,
  `vertexPrism_standardEdge_identity`).
- [x] Expose genuine finite support for production subdivision and prove the
  explicit `n/(n+1)` diameter contraction on every supported simplex
  (`finiteVertexSubdivisionSupport`, `finiteVertexSubdivision_realize`,
  `finiteVertexSubdivision_diameter_le`).
- [x] Iterate subdivision and prove every supported affine simplex is
  subordinate to an arbitrary open cover, using the compounded diameter bound
  and an explicit Lebesgue number
  (`iteratedFiniteVertexSubdivision_diameter_le`,
  `exists_iteratedFiniteVertexSubdivision_subordinate`).
- [x] Transport finite subdivision support through arbitrary singular
  simplices, select one subdivision depth over a finite chain, and prove the
  production prism preserves cover-smallness
  (`postcomposedIteratedSubdivision_small`,
  `Finsupp.exists_uniform_depth`, `finiteVertexPrism_realize`,
  `postcomposedPrism_small`).
- [ ] Cover the circle by two contractible arcs with two-component overlap.
- [ ] Compute `H₁(S¹) ≅ ℤ` from exactness.

### Route C: simplicial circle

- [ ] Compute the normalized chain complex of `SSet.S1` (one nondegenerate
  vertex, one nondegenerate edge, no higher nondegenerate simplices).
- [ ] Compare normalized and unnormalized alternating-face complexes.
- [ ] Prove the realization/singular comparison for `SSet.S1`.
- [ ] Identify `|SSet.S1|` with the selected topological circle.

### Circle acceptance gate

- [ ] A named isomorphism `H₁(S¹) ≅ ℤ` for genuine singular homology.
- [ ] A named singular-homology generator whose image is `1 : ℤ`.
- [ ] A proof that the generator is nonzero and `H₁(S¹)` is nontrivial.
- [ ] `H₀(S¹) ≅ ℤ` and `Hₙ(S¹) = 0` for `n ≥ 2`.
- [ ] `#print axioms` confirms every headline result is free of `sorryAx`.

## Product theorem and Künneth

- [ ] Construct the singular-chain cross product.
- [ ] Construct an Eilenberg–Zilber/Alexander–Whitney comparison between
  chains on `X × Y` and the tensor product of chains.
- [ ] Prove the comparison is a chain-homotopy equivalence or quasi-isomorphism.
- [ ] State the integral Künneth short exact sequence, including the `Tor`
  term; do not silently state a false tensor-only theorem.
- [ ] Prove the torsion-free specialization needed for products of circles.
- [ ] Anti-vacuity: compute `H₁(S¹ × S¹)` or a smaller nontrivial product
  directly from the theorem.

## Torus

- [ ] Fix the concrete torus model and prove it is homeomorphic to
  `S¹ × S¹` if it is not definitionally that product.
- [ ] Compute `H₀(T²) ≅ ℤ`.
- [ ] Compute `H₁(T²) ≅ ℤ × ℤ` with two named circle-factor generators.
- [ ] Compute `H₂(T²) ≅ ℤ` with a named fundamental class.
- [ ] Prove all higher homology groups vanish.
- [ ] Prove at least one generator/fundamental class is nonzero independently
  of the abstract isomorphism statement.

## Spheres

- [x] Construct explicit disk/closed-hemisphere and sphere/equator
  homeomorphisms, with a boundary-compatibility theorem identifying the
  resulting maps of pairs (`T02A06HemisphereCoordinates.lean`).
- [x] Fix the sphere excision pair and prove its production excision map is a
  homology isomorphism.  In explicit coordinates its source is the open disk
  relative to the punctured open disk, with a proved homeomorphism of pairs
  (`T02A06HemisphereExcision.lean`).
- [x] Compare the closed disk/boundary pair with the open disk/punctured-disk
  pair by radial normalization.  The punctured disk deformation retracts onto
  the radius-`1/2` sphere, and the induced relative homology map is an
  isomorphism in degrees at least two
  (`T02A06DiskRadialComparison.lean`).
- [x] Prove the positive-degree sphere shift from the pair LES, stereographic
  contractibility of the north-pole complement, open-cover excision, hemisphere
  coordinates, and radial disk-pair comparison (`T02A06SphereShift.lean`).
- [ ] Compute `H₀(Sⁿ)`, handling `S⁰` separately from connected spheres.
- [ ] Compute `Hₙ(Sⁿ) ≅ ℤ` for `k = 0,n` and zero otherwise.
- [ ] Exhibit the top-dimensional fundamental class and prove it is nonzero.
- [ ] Reconcile the result with Mathlib's `TopCat.sphere n` indexing and with
  any `Metric.sphere`/`Circle` models used by APM problem statements.

## Validation target: APM `t02A06` (2026-08-19, Joe's decision)

**COMPLETED 2026-08-20.** `problems/t02A06/lean/Main.lean` now has zero
`sorry`/`admit`, and `#print axioms apm_t02a06` reports only `propext`,
`Classical.choice`, and `Quot.sound`.  The reusable route landed as singular
subdivision and small chains, open-cover excision, disk-pair comparisons,
sphere shifts, path-connected `H₀`, and the explicit one-disk/interval pair
comparison.  The final obstruction uses the retract `S² ⇄ S² × S²`, so no
Künneth theorem was required.

This module's work is validated against the now-closed APM problem `t02A06`
(`problems/t02A06/lean/Main.lean`). Joe's instruction was that the objective
was closing the problem, not completing this checklist for its own sake; the
retract argument is the resulting cheaper route for the second conjunct.

- `bridge_1` (oriented intersection of two great circles) is closed by the
  explicit normalized-cross-product classification in the problem module.
- **`bridge_2`** — no homeomorphism `S² × S² ≃ₜ S⁴` — is THIS module's target.

  **KÜNNETH IS NOT REQUIRED FOR IT** (route survey, 2026-08-19; this SUPERSEDES
  the first version of this section, which demanded `H₂(S² × S²) ≅ ℤ²`). Pick
  `p : S²` and set `i : x ↦ (x,p)`, `r = Prod.fst`. Then `r ∘ i = 𝟙`, so
  functoriality makes `H₂(i)` split injective and `H₂(S²) ↪ H₂(S² × S²)`. A
  homeomorphism to `S⁴` would force that group into `H₂(S⁴) = 0`. So the
  prerequisite is only

      `H₂(S²) ≠ 0`  and  `H₂(S⁴) = 0`,

  NOT `H₂(S² × S²) ≅ ℤ²`. This plan and the problem file's commentary both
  overstate it, following the informal solution — which uses Künneth because it
  is the natural PAPER argument, not the cheapest Lean one. This removes the
  Eilenberg-Zilber/Künneth program and the torus from the critical path to
  `bridge_2`: an estimated 12-20 commits down to 4-8.

  Note `H₂(S⁴) = 0` is an OFF-DEGREE vanishing statement, not the top class: the
  sphere section must deliver `Hₖ(Sⁿ)` for all `k`, not only `k = n`.

- **Priority consequence:** for the validation objective the deliberately fixed
  order (circle, Künneth, torus, spheres) is wrong — SPHERES are the target and
  they are last. Künneth and the torus keep their independent value but are off
  the critical path to closing `t02A06`.
- `bridge_3` — every map `S³ → T³` is zero on `H₃` — is closed by
  constructing simple connectivity of the metric `S³`, lifting each circle
  coordinate through its real universal cover, and applying homotopy
  invariance.  The required sphere simple-connectivity theorem was supplied by
  `SimplyConnectedOpenCover`, rather than by Mathlib's sphere instances.

The `t02A06` acceptance gate is closed; `t01A07` remains a separate landing
condition for the intersection track.

## Corpus integration

- [ ] Inventory the 41 dependent APM problems by the weakest theorem they need:
  circle, product/Künneth, torus, sphere, degree/transfer, or a later general
  homology API.
- [ ] Add small adapter lemmas for the concrete space representation used by
  each first acceptance problem.
- [x] Wire this module into `ConstructionTargets.lean` only after the concrete
  circle acceptance gate is met.
- [ ] Close one real blocked APM problem before generalizing the API further.

## Validation

Run after every shared-module change:

```sh
lake env lean ConstructionTargets/SingularHomologyConcrete.lean
```

For each claimed computation, print axioms for the isomorphism, generator
evaluation, nontriviality witness, and vanishing theorem. A result containing
`sorryAx` remains unchecked.

Relevant branch commits as of 2026-08-19:

- `73f669d` — nontrivial cellular circle homology model;
- `fc551df` — genuine singular homology of a point;
- `07c05e3` — TopCat homotopies act equally on singular homology.
