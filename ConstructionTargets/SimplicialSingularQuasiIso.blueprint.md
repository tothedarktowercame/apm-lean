# Ordered faces compute singular homology (route S)

claude-14, 2026-10-30. Replaces route C's plan for the two directional leaves
(`SimplicialSingularComparison.blueprint.md`). Each leaf's docstring in
`SimplicialSingularQuasiIso.lean` is its proof sketch; this note gives the
overall argument and the dependency layers.

## Argument

`U = starCover K`: open stars of vertices, as subsets of `K.space`
(open: `starCover_isOpen`; cover: `starCover_covers`).

1. **Carrier.** For `A ⊆ K.space`, `starCarrier K A` is the set of nonempty
   subsets of minimal faces of points of `A` (`IsMinimalFace`: the hull contains
   the point and no facet's hull does). If `A` lies in the open star of `a`,
   every minimal face of a point of `A` contains `a`
   (`isMinimalFace_mem_of_openStar`), so the carrier is a cone on `a`
   (`starCarrier_cone`). Cones are acyclic for ordered faces
   (`coneSupported_cycle_bounds`, `coneSupported_zero_bounds`, from the apex cone
   `SimplicialChainMaps.subdivisionCone`), and the polyhedron of the carrier is
   star-shaped about `a`, so rationally pointlike (`starCarrier_pointlike`).
2. **ψ.** Acyclic carriers give a chain map `ψ` from small chains to ordered faces,
   carried by `starCarrier K (range σ)` (`smallToFace_exists`).
3. **Surjective.** `ψ ≫ cmpH` agrees with the small-chain inclusion on homology
   (`smallToFace_homology`, singular-side carriers), and the inclusion is an
   isomorphism on homology (`CoefficientSmallComparison.inclusion_isIso`):
   `package_homology_surjective`.
4. **Injective.** `cmpH ≫ Sd^r` lifts through the inclusion as `Φ`
   (`affineCmp_small_lift`). `Φ ≫ ψ` sends each face to chains on its subsets and
   is the identity in degree zero (`smallLift_comp_carried`, using
   `subdivisionIterate_subsetCarried`, `smallChain_span_of_subsetCarried`,
   `isMinimalFace_subset`), so it is the identity on homology
   (`faceCarried_endo_homology`): `package_homology_injective`.
5. **Transport.** `affineCmp_homologyMap_injective/surjective` apply the package
   theorems to `cmpH := q ≫ e` (the identity map `e` of
   `SimplicialChainMaps.orientedPackage_homology_bijective`).

## Layers (dispatch a layer only after the one before has landed)

| Layer | Leaves |
|---|---|
| 0 | `exists_isMinimalFace`, `isMinimalFace_subset`, `coneSupported_cycle_bounds`, `coneSupported_zero_bounds`, `affineCmp_small_lift`, `subdivisionIterate_subsetCarried`, `smallChain_span_of_subsetCarried` |
| 1 | `isMinimalFace_mem_of_openStar`, `faceCarried_endo_homology` |
| 2 | `starCarrier_pointlike`, `smallToFace_exists` |
| 3 | `smallToFace_homology`, `smallLift_comp_carried` |
| 4 | `package_homology_surjective`, `package_homology_injective` |
| 5 | `affineCmp_homologyMap_injective`, `affineCmp_homologyMap_surjective` |

## Truth checks

- Degree zero of `smallLift_comp_carried`: the minimal face of a vertex `v` is
  `{v}` (`isMinimalFace_subset` with `s = {v}`), so `ψ` of the point `v` is
  supported on `{v}` with coefficient sum 1, i.e. `single {v} 1`; subdivision
  fixes 0-simplices.
- `smallChain_span_of_subsetCarried`: generators are a basis and the inclusion
  sends small generators to generators, so the support of `q` consists of small
  simplices with range in `A`.
- `smallToFace_exists` in degree 1: `ψ (d σ)` has coefficient sum `1 - 1 = 0`.
- `affineCmp_small_lift`: finitely many faces in all degrees, and
  `actual_chain_eventual` holds for all `k ≥ N`, so one `r` works.
