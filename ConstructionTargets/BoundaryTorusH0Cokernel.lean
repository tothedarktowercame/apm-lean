import ConstructionTargets.BoundaryTorusIntegralHomologyComplete
import ConstructionTargets.T00A01MayerVietorisAdapters

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ConstructionTargets.BoundaryTorusH0Cokernel

open ConstructionTargets.BoundaryTorusOpenCover
open ConstructionTargets.BoundaryTorusMayerVietoris
open ConstructionTargets.BoundaryTorusMayerVietorisAlgebra
open ConstructionTargets.BoundaryTorusMayerVietorisExactness
open ConstructionTargets.BoundaryTorusIntegralHomology
open ConstructionTargets.BoundaryTorusIntegralHomologyComplete
open ConstructionTargets.IntegralSingularHomologyComparison
open ConstructionTargets.ProductionOpenCoverMayerVietoris
open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.T00A01MayerVietorisAdapters

private abbrev BT :=
  ConstructionTargets.SolidTorusGluingOpenCover.BoundaryTorus
private abbrev H (k : ℕ) := SingularHomology k (TopCat.of BT)
private abbrev MH (k : ℕ) :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of BT))
private abbrev Z := BoundaryTorusMayerVietorisAlgebra.IntGroup

/-- The degree-zero pieces segment with the computed signed fold and actual
production reassembly arrow exposed literally. -/
noncomputable def h0PiecesLiteralShortComplex : ShortComplex AddCommGrpCat :=
  ShortComplex.mk intSignedFold
    (integerReassemblyArrow 0 circleH0GroupIsoInt) (by
      rw [← integerPiecesShortComplex_f 0 circleH0GroupIsoInt,
        ← integerPiecesShortComplex_g 0 circleH0GroupIsoInt]
      exact (integerPiecesShortComplex 0 circleH0GroupIsoInt).zero)

theorem h0PiecesLiteralShortComplex_exact :
    h0PiecesLiteralShortComplex.Exact := by
  apply ShortComplex.exact_of_iso ?_ integerPiecesShortComplex_H0_exact
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simpa using (integerPiecesShortComplex_f 0 circleH0GroupIsoInt).symm)
    (by simpa using (integerPiecesShortComplex_g 0 circleH0GroupIsoInt).symm)

/-- Degree-zero production reassembly remains epic after applying the inverse
piece coordinate. -/
noncomputable instance integerReassemblyArrow_H0_epi :
    Epi (integerReassemblyArrow 0 circleH0GroupIsoInt) := by
  dsimp only [integerReassemblyArrow]
  letI : Epi (productionReassemblyArrow leftOpen rightOpen 0) :=
    productionReassemblyArrow_epi_zero leftOpen rightOpen leftOpen_isOpen
      rightOpen_isOpen leftOpen_union_rightOpen
  constructor
  intro W f g hfg
  apply (cancel_epi (productionReassemblyArrow leftOpen rightOpen 0)).1
  apply (cancel_epi (piecesIntegerIso 0 circleH0GroupIsoInt).inv).1
  simpa only [Category.assoc] using hfg

/-- Exactness plus the epic endpoint identifies ambient H0 with the
categorical cokernel of the literal signed fold. -/
noncomputable def boundaryTorusH0IsoSignedFoldCokernel :
    H 0 ≅ cokernel intSignedFold := by
  letI : Epi h0PiecesLiteralShortComplex.g := by
    change Epi (integerReassemblyArrow 0 circleH0GroupIsoInt)
    infer_instance
  let hR : IsColimit (CokernelCofork.ofπ
      (integerReassemblyArrow 0 circleH0GroupIsoInt)
      h0PiecesLiteralShortComplex.zero) :=
    (h0PiecesLiteralShortComplex.exact_and_epi_g_iff_g_is_cokernel.mp
      ⟨h0PiecesLiteralShortComplex_exact, inferInstance⟩).some
  exact (IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel intSignedFold) hR).symm

noncomputable def boundaryTorusH0GroupIsoInt : H 0 ≅ Z :=
  boundaryTorusH0IsoSignedFoldCokernel ≪≫ integerSignedFoldCokernelIso

noncomputable def boundaryTorusH0ModuleIsoInt :
    MH 0 ≅ ModuleCat.of ℤ ℤ :=
  singularHomologyModuleIsoOfGroupIso (TopCat.of BT) 0 _
    boundaryTorusH0GroupIsoInt

/-- All integral homology clauses for the boundary torus, without any
fundamental-group assertion. -/
theorem boundaryTorus_complete_module_homology :
    Nonempty (MH 0 ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (MH 1 ≅ ModuleCat.of ℤ (Fin 2 → ℤ)) ∧
    Nonempty (MH 2 ≅ ModuleCat.of ℤ ℤ) ∧
    ∀ k : ℕ, 3 ≤ k → IsZero (MH k) := by
  rcases boundaryTorus_positiveDegree_module_homology with ⟨h1, h2, hhi⟩
  exact ⟨⟨boundaryTorusH0ModuleIsoInt⟩, h1, h2, hhi⟩

#print axioms h0PiecesLiteralShortComplex_exact
#print axioms integerReassemblyArrow_H0_epi
#print axioms boundaryTorusH0GroupIsoInt
#print axioms boundaryTorusH0ModuleIsoInt
#print axioms boundaryTorus_complete_module_homology

end ConstructionTargets.BoundaryTorusH0Cokernel
