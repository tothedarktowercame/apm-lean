# PolygonSurfaceHomology blueprint

This foundation follows the route audits encoded by
`holes/labs/blueprints/t97A01/BLUEPRINT.md`, lemma
`apm_t97a01_polygon_singular_homology`, and
`holes/labs/blueprints/t94J09/BLUEPRINT.md`, lemma
`apm_t94J09_polygon_homology`.  It supplies the common Mayer--Vietoris
calculation for a one-vertex polygon quotient.  The `t97A01` adapter uses it
directly for its two six-edge presentations.  The `t94J09` adapter transports
along its separately reviewed normalization to the standard `N6` quotient.

The implementation builds on the sorry-free modules
`PolygonSurfacePiOne`, `PolygonRadialOpenCoverPackages`,
`PolygonInnerOpenPointedContraction`, `PolygonOverlapHomotopyEquivCircle`,
`PolygonBoundaryThreeCirclesLiteralFormulas`, and
`ProductionOpenCoverMayerVietoris`.  Homology means Mathlib integral singular
homology in `ModuleCat ℤ`; no cellular-homology comparison is assumed.

The representation throughout is
`PolygonSurfacePiOne.PairingData.Space P`.  Edge coordinates are the finite
orbit type `PairingOrbit P.pair`.  The sign convention is fixed by
`PairingData.signedWedgeArc`: traversing edge `i` contributes `+1` when its
signed parameter agrees with the positive orbit circle and `-1` when it is
reversed.  This convention makes the two `t97A01` vectors `(2,2,2)` and
`(0,0,2)`.

### B1. Integral homology notation

lean: `ConstructionTargets.PolygonSurfaceHomology.H` :
`(P : PairingData) → ℕ → ModuleCat ℤ`

uses: Mathlib `AlgebraicTopology.singularHomologyFunctor`

status: planned

Define `H P k` to be integral singular homology in degree `k` of `P.Space`.
This is an abbreviation, not a certificate.

### B2. Signed attaching degree vector

lean: `ConstructionTargets.PolygonSurfaceHomology.attachingDegree` :
`(P : PairingData) → PairingOrbit P.pair → ℤ`

uses: `PairingData.signedWedgeArc`, finite sums on `Fin P.edgeCount`

status: planned

For orbit `l`, sum the signs of all boundary edges whose pairing orbit is
`l`.  Prove the representative-free formula by summing over edge indices,
not by choosing an orbit representative.  Record the formula for each edge
as a simp lemma.  This is the abelianized attaching word.

### B3. Degree-two boundary map

lean: `ConstructionTargets.PolygonSurfaceHomology.attachingBoundary` :
`(P : PairingData) → ℤ →ₗ[ℤ] (PairingOrbit P.pair → ℤ)`

uses: B2

status: planned

Send `n` to `n • attachingDegree P`.  Define
`BoundaryKernel P := LinearMap.ker (attachingBoundary P)` and
`BoundaryCokernel P := (PairingOrbit P.pair → ℤ) ⧸
LinearMap.range (attachingBoundary P)`.  These are the exact models returned
in degrees two and one.

### B4. Outer-piece homology coordinates

lean: `ConstructionTargets.PolygonSurfaceHomology.outerHomology` :
for positive finite orbit type `L`, the outer radial piece has `H₀ ≅ ℤ`,
`H₁ ≅ ModuleCat.of ℤ (L → ℤ)`, and zero homology in degrees at least two

uses: puncture deformation retract from `PolygonSurfacePiOne`, the reviewed
boundary-wedge homeomorphism, finite-wedge homology, homotopy invariance

status: planned

Transport the outer piece to the boundary skeleton, then to the finite wedge
of orbit circles.  Preserve the coordinate in which the positive loop of
orbit `l` is the basis vector `Pi.single l 1`; this coordinate is required by
B7 and may not be replaced by an unspecified module isomorphism.

### B5. Inner-piece and overlap homology

lean: `ConstructionTargets.PolygonSurfaceHomology.innerOverlapHomology` :
the inner piece has the homology of a point, and the overlap has the homology
of `Circle`, with its positive radial circle generator fixed

uses: `PolygonInnerOpenPointedContraction`,
`PolygonOverlapHomotopyEquivCircle`, point and circle singular homology

status: planned

Use the explicit contractions/equivalence.  State `H₀`, `H₁`, and vanishing
above the dimensions needed in the Mayer--Vietoris sequence.  Keep the
positive circle generator rather than merely asserting rank one.

### B6. Mayer--Vietoris exact segment

lean: `ConstructionTargets.PolygonSurfaceHomology.radialMVSegment` :
the production Mayer--Vietoris sequence for `P.openCover`, rewritten through
B4 and B5 as the exact sequence with degree-one source `ℤ` and target
`PairingOrbit P.pair → ℤ`

uses: B4, B5, `ProductionOpenCoverMayerVietoris`

status: planned

Instantiate the radial open cover.  Naturality supplies all conjugation
squares.  Contractibility kills the inner positive-degree terms; overlap and
outer coordinates leave one map `ℤ → (PairingOrbit P.pair → ℤ)`.

### B7. Attaching-map coordinate calculation

lean: `ConstructionTargets.PolygonSurfaceHomology.radialMV_boundary_eq` :
the remaining B6 homomorphism equals `attachingBoundary P`

uses: B2, B3, B6, the literal boundary-loop formulas and ordered arc
decomposition

status: planned

Split the positive overlap loop into the ordered polygon arcs.  For each arc,
use `signedWedgeArc_of_sign` or `signedWedgeArc_of_not_sign`; apply circle
Hurewicz and additivity.  The result on `1` is `attachingDegree P`, hence the
linear maps agree by `ℤ`-linearity.  This is the geometric step that must not
be replaced by a cellular-homology assertion.

### B8. Low-degree kernel/cokernel extraction

lean: `ConstructionTargets.PolygonSurfaceHomology.lowDegreeHomology` :
`Nonempty (H P 0 ≅ ModuleCat.of ℤ ℤ) ∧
 Nonempty (H P 1 ≅ ModuleCat.of ℤ (BoundaryCokernel P)) ∧
 Nonempty (H P 2 ≅ ModuleCat.of ℤ (BoundaryKernel P))`

uses: B3, B6, B7

status: planned

Extract kernel and cokernel from exactness.  Connectedness gives degree zero.
At degree two, the zero outer/inner term identifies surface homology with the
kernel; at degree one, exactness identifies it with the cokernel.

### B9. Higher-degree vanishing

lean: `ConstructionTargets.PolygonSurfaceHomology.highDegreeHomology` :
`∀ k : ℕ, 3 ≤ k → Limits.IsZero (H P k)`

uses: B4, B5, B6

status: planned

Use the Mayer--Vietoris sequence in adjacent degrees.  All three piece terms
vanish there, so exactness makes the middle surface term zero.

### B10. Final polygon-quotient homology theorem

lean: `ConstructionTargets.PolygonSurfaceHomology.polygonQuotient_homology` :
`(P : PairingData) →
 Nonempty (H P 0 ≅ ModuleCat.of ℤ ℤ) ∧
 Nonempty (H P 1 ≅ ModuleCat.of ℤ (BoundaryCokernel P)) ∧
 Nonempty (H P 2 ≅ ModuleCat.of ℤ (BoundaryKernel P)) ∧
 (∀ k : ℕ, 3 ≤ k → Limits.IsZero (H P k))`

uses: B8, B9

status: planned

Assemble the preceding results without changing coordinates.  Consumer
adapters compute the finite vector: `(2,2,2)` and `(0,0,2)` have zero kernel
and cokernel `ℤ × ℤ × ZMod 2`; the standard nonorientable genus-six vector
has zero kernel and cokernel `(Fin 5 → ℤ) × ZMod 2`.  Thus their stronger
vanishing from degree two follows from B8 plus the explicit injectivity
calculation, while B9 handles degree three and above.

Every hypothesis in the final declaration is contained in `PairingData` and
is used by B2, B4, or B7.  No consumer theorem, frozen definition, or
statement-registry entry is changed.
