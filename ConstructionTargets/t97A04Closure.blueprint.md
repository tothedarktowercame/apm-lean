# t97A04 closure: the top homology action of an integral torus map

This blueprint follows the `t97A04` audit in
`~/notes/closer/audits/t97A04.md`, specifically its remaining
`T97A04TorusH2.shearY_H2`, `apm_t97A04_bridge_3`, and `hcore` steps.  The
route file predates the completed H0 and H1 bridges and also predates the
production connecting-map naturality theorem.  The only mathematical bridge
still missing is the action of `apm_t97a04_Lbar` on integral H2; after that,
the second placeholder is a direct assembly.

The formalisation uses singular homology in `AddCommGrpCat` for the
Mayer--Vietoris calculation, then transports the result to the frozen
`ModuleCat ℤ` objects with
`IntegralSingularHomologyComparison.singularHomologyModuleIsoOfGroupIso` and
its naturality theorem.  The torus model throughout is
`AddCircle (1 : ℝ) × AddCircle (1 : ℝ)`.  Its top-class coordinate is the one
transported from `Circle × Sphere 1` by the product of the two canonical
circle homeomorphisms and
`BoundaryTorusH2ConnectingIso.boundaryTorusH2IsoInt`.

## Existing API

The nodes below build on these compiled declarations.

- `ProductionOpenCoverMayerVietoris.productionConnecting_naturality`: the
  connecting square for a morphism of Boolean-cover short complexes.
- `ProductionOpenCoverMayerVietoris.coverRangeMap`,
  `coverRangeMap_inter_left`, and `coverRangeMap_inter_right`: the maps and
  commuting squares from which the required short-complex morphism is built.
- `BoundaryTorusOpenCover.leftOpen`, `rightOpen`, their openness and cover
  proofs, and the overlap coordinate equivalences used by
  `BoundaryTorusMayerVietoris`.
- `BoundaryTorusH2ConnectingIso.productionConnecting_H1_mono` and
  `boundaryTorusH2IsoInt`: injectivity of the degree-two connecting map and
  the resulting integral top-class coordinate.
- `BoundaryTorusIntegralHomologyComplete.boundaryTorusH2ModuleIsoInt` and
  `IntegralSingularHomologyComparison.singularHomologyComparison_naturality`.
- The frozen helpers `t97A04HomologyMap_comp`,
  `t97A04HasHomologicalData.of_maps`, and `apm_t97a04_matrix_det`.

### B1. Frozen-torus top-class coordinate

lean: `ConstructionTargets.T97A04Closure.frozenTorusH2GroupIsoInt` :
`SingularHomology 2 (TopCat.of (AddCircle (1 : ℝ) × AddCircle (1 : ℝ))) ≅ AddCommGrpCat.of ℤ`

uses: Mathlib `AddCircle.homeomorphCircle`,
`SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv`,
`BoundaryTorusH2ConnectingIso.boundaryTorusH2IsoInt`

status: planned

Transport the compiled boundary-torus H2 coordinate along
`Homeomorph.prodCongr (AddCircle.homeomorphCircle one_ne_zero)
(AddCircle.homeomorphCircle one_ne_zero)` and the existing identification of
the second circle with `Sphere 1`.  Fix this composite once: all later scalar
statements use this coordinate, rather than an arbitrary rank-one
isomorphism.  The forward map sends the frozen torus fundamental class to the
integer selected by the Mayer--Vietoris connecting coordinate.

### B2. Vertical two-open cover on the frozen torus

lean: `ConstructionTargets.T97A04Closure.frozenYCover` : a structure
containing open sets `U V : Set FrozenTorus`, proofs `IsOpen U`, `IsOpen V`,
`U ∪ V = Set.univ`, and a homeomorphism of this covered space with the
transport of `BoundaryTorusOpenCover.leftOpen/rightOpen`

uses: B1, `BoundaryTorusOpenCover.leftOpen`,
`BoundaryTorusOpenCover.rightOpen`

status: planned

Take the cover in the second coordinate: under the canonical AddCircle-to-
Circle homeomorphism it is exactly the banked boundary-torus cover.  Record
the two member equations and the intersection equation under the product
homeomorphism.  Do not introduce a second, merely homotopy-equivalent cover;
the connecting-map coordinate in B1 is tied to this transported cover.

### B3. Cover-preserving upper-triangular shear

lean: `ConstructionTargets.T97A04Closure.shearY` :
`ℤ → ℤ → C(FrozenTorus, FrozenTorus)`

uses: B2

status: planned

Define `shearY a b (x,y) = (a • x + b • y, y)`.  Prove it maps each member of
`frozenYCover` to itself, because its second coordinate is literally `y`.
Also prove the composition laws needed later:
`shearY a b ∘ shearY c d = shearY (a*c) (a*d+b)` in the cases used by B9,
and the pointwise formulas at `(3,1)`, `(1,-1)`, and `(1,0)`.

### B4. Shear morphism of Mayer--Vietoris short complexes

lean: `ConstructionTargets.T97A04Closure.shearYShortComplexHom` : for
`a b : ℤ`, a morphism from the Boolean-cover short complex of B2 to itself

uses: B2, B3,
`ProductionOpenCoverMayerVietoris.coverRangeMap_inter_left`,
`ProductionOpenCoverMayerVietoris.coverRangeMap_inter_right`

status: planned

Use `coverRangeMap` for the intersection, the two cover members, and the
union.  The left and right intersection squares prove compatibility with the
signed inclusion arrow; the defining `coverRangeMap_comp_ι` equation proves
compatibility with reassembly.  These are the two fields of the short-complex
morphism.  This node contains no homology calculation.

### B5. Identify the union endpoint of the shear morphism

lean: `ConstructionTargets.T97A04Closure.shearY_productionUnionMap` :
`productionUnionMap ... (shearYShortComplexHom a b) n =
  HomologicalComplex.homologyMap
    (SingularSubdivision.singularPostcomposition (shearY a b)) n`

uses: B4, `ProductionOpenCoverMayerVietoris.productionUnionMap`

status: planned

Expand the union transport and use `coverRangeMap_comp_ι`.  Cancel the
cover-small/production isomorphisms on both sides.  What remains is equality
of postcomposition chain maps, proved degreewise on singular simplices by
the defining equation of `coverRangeMap`.  This is where the abstract union
endpoint is connected to the actual induced map of `shearY`.

### B6. Identify the overlap endpoint and its degree

lean: `ConstructionTargets.T97A04Closure.shearY_overlap_coordinate` : under
the banked overlap H1 coordinate, the map
`productionIntersectionMap ... (shearYShortComplexHom a b) 1` is
multiplication by `a` on each signed overlap generator

uses: B2, B4, `BoundaryTorusMayerVietoris.overlapHomologyIsoCircleBiprod`,
the circle H1 degree theorem, and the existing winding-coordinate naturality

status: planned

The transported overlap is two components, each homotopy equivalent to the
first-coordinate circle.  On either component the restricted map is
`x ↦ a • x + constant`; homotope away the constant within that component.
The remaining power map has H1 degree `a`.  Prove the statement on both
biproduct injections and use biproduct extensionality.  Keep the existing
sign convention of the signed intersection arrow; the same scalar occurs on
both components, so it also acts by `a` on the signed-fold kernel coordinate.

### B7. H2 action of the upper-triangular shear

lean: `ConstructionTargets.T97A04Closure.shearY_H2` : for `a b : ℤ`, in the
B1 coordinate the homology map induced by `shearY a b` is multiplication by
`a`

uses: B1, B2, B4, B5, B6,
`ProductionOpenCoverMayerVietoris.productionConnecting_naturality`,
`BoundaryTorusH2ConnectingIso.productionConnecting_H1_mono`

status: planned

Apply production connecting-map naturality to B4 in degree one.  Rewrite its
union endpoint with B5 and its intersection endpoint with B6.  The resulting
square says that connecting after `H2(shearY a b)` equals multiplication by
`a` after connecting.  Cancel the monic connecting map.  Finally unfold the
B1 coordinate, whose forward arrow is this connecting map followed by the
banked overlap-kernel coordinate, to obtain the scalar equation.  No
Künneth or cross-product theorem is used.

### B8. Coordinate swap acts by a unit and cancels in pairs

lean: `ConstructionTargets.T97A04Closure.swap_H2_square` : if
`swap (x,y) = (y,x)`, then
`H2(swap) ≫ H2(swap) = 𝟙 _`; consequently its scalar in the B1 coordinate
satisfies `s*s = 1`

uses: B1, Mathlib functoriality, `ContinuousMap.ext`

status: planned

Prove `swap.comp swap = ContinuousMap.id FrozenTorus` pointwise, rewrite with
the homology functor's composition and identity laws, and conjugate by B1.
Only `s*s=1` is needed: do not choose an orientation sign for the swap.

### B9. Degree-three action of the frozen map

lean: `ConstructionTargets.T97A04Closure.frozenLbar_H2` : in the B1
coordinate, the induced H2 map of `apm_t97a04_Lbar` is multiplication by `3`

uses: B3, B7, B8, `t97A04HomologyMap_comp`

status: planned

Define `g(x,y) = (x,y-x)` and prove
`g = swap ∘ shearY 1 (-1) ∘ swap`; B7 gives scalar one for the middle shear,
and B8 cancels the two swap scalars.  Prove pointwise that
`apm_t97a04_Lbar = shearY 3 1 ∘ g`.  Functoriality then makes its H2 scalar
`3*1=3`.  The matrix identity is checked by the displayed coordinate
formulas; `apm_t97a04_matrix_det` is a consistency check, not a substitute
for this induced-map calculation.

### B10. Module coordinate and bridge 3

lean: `ConstructionTargets.T97A04Closure.bridge3` :
`∃ h2 : T97A04Homology 2 ≅ ModuleCat.of ℤ ℤ,
  ∀ a, h2.hom (t97A04HomologyMap 2 apm_t97a04_Lbar a) = 3 * h2.hom a`

uses: B1, B9,
`IntegralSingularHomologyComparison.singularHomologyComparison_naturality`,
`singularHomologyModuleIsoOfGroupIso`

status: planned

Convert B1 to a `ModuleCat ℤ` isomorphism.  Naturality of the comparison
identifies the frozen `t97A04HomologyMap` with the AddCommGrp singular
homology map used in B9.  Apply B9 elementwise and use that the comparison
and coordinate maps are additive, so integer scalar multiplication becomes
the frozen expression `3 * h2.hom a`.  This theorem has exactly the type of
`apm_t97A04_bridge_3` and may be used as its proof without changing the
registered statement.

### B11. Close the frozen problem

lean: `apm_t97A04_bridge_3` and the `hcore` proof inside `apm_t97a04`

uses: B10, existing `apm_t97A04_bridge_1`, existing
`apm_t97A04_bridge_2`, `t97A04HasHomologicalData.of_maps`

status: planned

Set bridge 3 to B10.  For `hcore`, destruct the three bridge witnesses and
return `⟨h0, h1, h2, H0, H1, H2⟩`; the existing final wrapper then applies
`t97A04HasHomologicalData.of_maps`.  This removes both remaining placeholders
without changing any registered declaration or definition.

## Dependency order and review findings

The formalisation order is B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11.
B4--B7 are the only Mayer--Vietoris-specific part; B8--B10 are finite
assembly and representation transport.

Every hypothesis in the frozen bridge is accounted for: the concrete map is
used in B9, the coefficient ring is fixed to ℤ in B1/B10, and the scalar `3`
comes from the explicit factorisation in B9.  No extra hypothesis is needed.
The audit's proposed new `productionConnecting_naturality` node is omitted
because that theorem is already compiled.  The audit's Künneth alternative
is deliberately not used.
