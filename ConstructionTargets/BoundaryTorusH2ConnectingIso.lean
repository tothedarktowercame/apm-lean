import ConstructionTargets.BoundaryTorusMayerVietorisAdjacentExactness

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ConstructionTargets.BoundaryTorusH2ConnectingIso

open ConstructionTargets.BoundaryTorusOpenCover
open ConstructionTargets.BoundaryTorusMayerVietoris
open ConstructionTargets.BoundaryTorusIntegralHomology
open ConstructionTargets.BoundaryTorusMayerVietorisExactness
open ConstructionTargets.BoundaryTorusMayerVietorisAdjacentExactness
open ConstructionTargets.ProductionOpenCoverMayerVietoris
open ConstructionTargets.SingularHomologyConcrete

private abbrev H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  SingularHomology k (TopCat.of X)

private abbrev BT :=
  ConstructionTargets.SolidTorusGluingOpenCover.BoundaryTorus

theorem h2Pieces_isZero : IsZero
    (H 2 leftOpen ⊞ H 2 rightOpen) := by
  rw [biprod_isZero_iff]
  exact ⟨leftHomology_isZero_of_one_lt 2 (by omega),
    rightHomology_isZero_of_one_lt 2 (by omega)⟩

instance productionConnecting_H1_mono :
    Mono (productionConnecting leftOpen rightOpen leftOpen_isOpen
      rightOpen_isOpen leftOpen_union_rightOpen 1) := by
  exact (productionMayerVietoris_exact_union leftOpen rightOpen
    leftOpen_isOpen rightOpen_isOpen leftOpen_union_rightOpen 1).mono_g
      (h2Pieces_isZero.eq_of_src _ _)

instance integerConnectingArrow_H1_mono :
    Mono (integerConnectingArrow 1 circleH1GroupIsoInt) := by
  dsimp only [integerConnectingArrow]
  letI : Mono (productionConnecting leftOpen rightOpen leftOpen_isOpen
      rightOpen_isOpen leftOpen_union_rightOpen 1) := by
    exact (productionMayerVietoris_exact_union leftOpen rightOpen
      leftOpen_isOpen rightOpen_isOpen leftOpen_union_rightOpen 1).mono_g
        (h2Pieces_isZero.eq_of_src _ _)
  constructor
  intro Z' a b hab
  apply (cancel_mono (productionConnecting leftOpen rightOpen leftOpen_isOpen
    rightOpen_isOpen leftOpen_union_rightOpen 1)).1
  apply (cancel_mono (overlapIntegerIso 1 circleH1GroupIsoInt).hom).1
  simpa only [Category.assoc] using hab

instance integerConnectingKernelLift_H1_mono :
    Mono (integerConnectingKernelLift 1 circleH1GroupIsoInt) := by
  apply mono_of_mono_fac (kernel.lift_ι
    BoundaryTorusMayerVietorisAlgebra.intSignedFold
    (integerConnectingArrow 1 circleH1GroupIsoInt)
    (integerIntersectionLiteralShortComplex 1 circleH1GroupIsoInt).zero)

instance integerConnectingKernelCoordinate_H1_mono :
    Mono (integerConnectingKernelCoordinate 1 circleH1GroupIsoInt) := by
  dsimp only [integerConnectingKernelCoordinate]
  infer_instance

instance integerConnectingKernelCoordinate_H1_isIso :
    IsIso (integerConnectingKernelCoordinate 1 circleH1GroupIsoInt) :=
  isIso_of_mono_of_epi _

/-- The H2 coordinate forced by Mayer--Vietoris exactness and the vanishing of
the two H2 piece groups. -/
noncomputable def boundaryTorusH2IsoInt : H 2 BT ≅ AddCommGrpCat.of ℤ :=
  asIso (integerConnectingKernelCoordinate 1 circleH1GroupIsoInt)

#print axioms h2Pieces_isZero
#print axioms integerConnectingArrow_H1_mono
#print axioms integerConnectingKernelCoordinate_H1_isIso
#print axioms boundaryTorusH2IsoInt

end ConstructionTargets.BoundaryTorusH2ConnectingIso
