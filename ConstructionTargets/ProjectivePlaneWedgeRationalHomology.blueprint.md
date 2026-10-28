# Projective-plane wedge rational homology

## Verdict and route

The target is true.  All homology in this module is singular homology with
coefficients in `ℚ`; no statement silently asserts the false integral claim
`H₁(RP²; ℤ) = 0`.

Use the polygon-cell/open-cover Mayer--Vietoris route for `RP²`, rather than
transfer from `S²`.  The repository already contains the coefficient
Mayer--Vietoris stack (`ProductionOpenCoverMayerVietoris`), the polygon radial
cover and its attaching-map calculation (`PolygonSurfaceHomology`), whereas it
does not contain the transfer theorem identifying quotient homology with
antipodal invariants.  In the `aa` cellular coordinates the only positive
differential is multiplication by `2`, an isomorphism over `ℚ`.

`RationallyPointlike X` means `H₀(X;ℚ) ≅ ℚ` and `H_k(X;ℚ)=0` for every
`k>0`.  `HasPointedContractibleNeighbourhood x` supplies an open neighbourhood
and a pointed contraction.  The latter is deliberately stronger than merely
being contractible: it is exactly the input consumed by
`GenericPointWedgeOpenCoverComparison` and excludes wild wedge points.

## Leaves

### `realProjectivePlane_rationallyPointlike` — LIBRARY, 180–260 lines

The concrete `Surface false 1` is rationally pointlike.  Specialize the radial
polygon cover to `nonorientableStandardPairingData 1`; use
`ProductionOpenCoverMayerVietoris.productionMayerVietoris_exact_*`, the
homotopy-invariance isomorphisms in `PolygonSurfaceHomology`, and reduce the
boundary matrix to `[2]`.  The remaining missing bridge is coefficient change
from the existing integral polygon calculation to the native `ModuleCat ℚ`
functor, so this leaf remains honestly **LIBRARY**.

C1: cellular complex is `ℚ --2--> ℚ`, hence true. C2: no conclusion is assumed.
C3: one shared coefficient-change specialization, not the wedge or Lefschetz
argument. C4–C5: use the named radial cover maps, not arbitrary coordinates.
C6–C7: coefficients are explicitly `ℚ`, and `2` is invertible. C8: degree zero
is stated separately; all positive degrees are covered. C9: not an ancestor
restatement. C10: matches the Lean predicate.

### `realProjectivePlane_pathConnected` — 30–50 lines, independent

Show the closed disk is path connected and push the instance through the
surjective continuous `surfaceQuotient`; use
`Continuous.pathConnectedSpace`/the quotient-map instance pattern and
`Surfaces.surjective_surfaceQuotient`.

C1: quotient of the nonempty disk is path connected. C2–C3: conclusion is only
the connectivity adapter. C4–C5: the concrete quotient map is exposed. C6–C7:
no hidden separation hypothesis. C8: the disk contains zero. C9: distinct from
homology. C10: matches Lean.

### `surfacePoint_hasPointedContractibleNeighbourhood` — 70–110 lines, independent

Choose a small open ball about `0` strictly inside the polygon disk.  Boundary
identifications do not meet it, so the quotient restricts to a homeomorphism;
transport the straight-line contraction.  Build with
`PointedContraction`, `Surfaces.surfaceQuotient`, and the saturated-open image
pattern in `PointWedgeRestrictedOpenQuotient`.

C1: the chosen centre is interior. C2: the contraction is produced, not passed
in. C3: local geometry only. C4–C5: contraction fixes the centre as required.
C6–C7: openness is in the subtype topology. C8: radius is positive and avoids
the boundary. C9: distinct from homology/connectivity. C10: matches Lean.

### `wedge_rationallyPointlike` — LIBRARY, 180–260 lines, generic

Given rationally pointlike summands and pointed contractible neighbourhoods at
the gluing points, the binary point wedge is rationally pointlike.  Destructure
the two neighbourhood witnesses, form
`GenericPointWedgeOpenCoverComparison.genericPointWedgeCoverPackage`, use
`GenericPointWedgeOverlapInclusionSquares` to identify the overlap maps, and
apply the coefficient open-cover Mayer--Vietoris exact sequence degree by
degree.  Degree zero may instead use `CoefficientH0.h0Iso` after the already
proved `PointWedgePathConnected` instance.  This is **LIBRARY** because the
generic coefficient-MV diagram chase is a shared foundation slightly beyond a
normal seat.

C1: the open-cover hypotheses exclude Hawaiian-earring behaviour. C2: neither
summand conclusion is the wedge conclusion. C3: only the reusable MV step.
C4: degree zero and every positive degree are explicit. C5: the overlap-square
module supplies the actual inclusion maps. C6–C7: native rational homology
throughout. C8: two one-point spaces wedge to one point and the proof still
applies. C9: genuinely generic, not the original concrete theorem. C10:
matches Lean.

### `wedgePoint_hasPointedContractibleNeighbourhood` — 60–100 lines, generic

The wedge of the two supplied neighbourhoods is an open neighbourhood of the
wedge point and contracts pointwise to it.  Use
`PointWedgeRestrictedOpenQuotient.restrictedOpen_isOpen`,
`restrictedOpenHomeomorphWedge`, and
`PointWedgePointedContractionDescent.wedgeContractionHomotopy`.

C1: pointed contractions agree at the identified point. C2: conclusion is new
local data. C3: no homology. C4–C5: uses the canonical quotient point and maps.
C6–C7: no separation assumptions. C8: singleton neighbourhoods work. C9:
distinct from L3. C10: matches Lean.

### `induced_zero_eq_id` — 45–70 lines, generic and independent

For a path-connected space whose `H₀` is one-dimensional, every self-map acts
as the identity on `H₀`.  Follow
`apm_t02A04_lefschetz_number_aux_trace_H0_aux_induced_eq_id`: use
`CoefficientH0.h0Augmentation_naturality`, split the augmentation with a vertex,
and cancel it after proving injectivity from equal finite ranks.

C1: path connectedness makes the augmentation an isomorphism. C2: identity is
proved from naturality, not assumed. C3: only the `H₀` map. C4–C5: the actual
`RationalLefschetz.induced` map is used. C6–C7: field is `ℚ`. C8: path-connected
spaces are nonempty in Lean's class, including a point. C9: generic extraction
of the t02A04 proof pattern. C10: matches Lean.

## Sorry-free assemblies and dependency layers

`lefschetzNumber_one_of_rationallyPointlike` is sorry-free: L6 gives trace one
in degree zero, and `IsZero` gives finite-dimensional/subsingleton positive
homology with bound zero.  `projectivePlaneWedge_rationallyPointlike` and
`projectivePlaneWedge_pointedNeighbourhood` are also sorry-free.

Layer 1 (all parallel): L1, L2, L3, L4, L5, L6.  L4 and L5 take all needed
summand conclusions as hypotheses and therefore do not acquire another leaf's
`sorryAx`.  Layer 2 consists only of the assemblies.  L1 and L4 are LIBRARY;
the other four leaves are normal seats.

## Consumer adapters

For `t96A02` (do not edit its file), the adapter is:

```lean
intro f
open ConstructionTargets.ProjectivePlaneWedgeRationalHomology in
  letI : PathConnectedSpace
      ConstructionTargets.StatementSurfaceModels.RealProjectivePlane :=
    realProjectivePlane_pathConnected
  exact lefschetzNumber_one_of_rationallyPointlike
    projectivePlaneWedge_rationallyPointlike f
```

For `t99A03`, instantiate the same `PathConnectedSpace`, apply
`wedge_rationallyPointlike` to two copies of the twofold result using
`projectivePlaneWedge_pointedNeighbourhood`, then apply the Lefschetz assembly.

## Checks

The module build completes with zero errors and exactly six sorry warnings,
one for each leaf.  No `SphereCap*` or `LinearGraphMeasure` module is imported.
The material doubt is implementation size of the native-`ℚ` specialization of
the polygon calculation (L1) and the generic coefficient Mayer--Vietoris chase
(L4); both are marked LIBRARY rather than disguised as normal leaves.
