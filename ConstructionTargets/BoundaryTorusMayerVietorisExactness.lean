import ConstructionTargets.BoundaryTorusIntegralHomology

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ConstructionTargets.BoundaryTorusMayerVietorisExactness

open ConstructionTargets.BoundaryTorusOpenCover
open ConstructionTargets.BoundaryTorusMayerVietoris
open ConstructionTargets.BoundaryTorusMayerVietorisAlgebra
open ConstructionTargets.BoundaryTorusIntegralHomology
open ConstructionTargets.ProductionOpenCoverMayerVietoris
open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.BooleanTwoCoverScaffold

private abbrev H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  SingularHomology k (TopCat.of X)

private abbrev Z := BoundaryTorusMayerVietorisAlgebra.IntGroup

/-- The production reassembly map after replacing the two piece homologies by
their integral circle coordinates. -/
noncomputable def integerReassemblyArrow (k : ℕ)
    (e : H k Circle ≅ AddCommGrpCat.of ℤ) :
    Z ⊞ Z ⟶ H k
      ConstructionTargets.SolidTorusGluingOpenCover.BoundaryTorus :=
  (piecesIntegerIso k e).inv ≫
    productionReassemblyArrow leftOpen rightOpen k

/-- The degree-`k` pieces segment, written with literal integer coordinates
on the overlap and both pieces. -/
noncomputable def integerPiecesShortComplex (k : ℕ)
    (e : H k Circle ≅ AddCommGrpCat.of ℤ) : ShortComplex AddCommGrpCat :=
  transportShortComplex
    (ShortComplex.mk
      (productionIntersectionArrow leftOpen rightOpen k)
      (productionReassemblyArrow leftOpen rightOpen k)
      (by
        rw [← booleanIntersectionArrow_eq_production leftOpen rightOpen k,
          ← booleanReassemblyArrow_eq_production leftOpen rightOpen
            leftOpen_isOpen rightOpen_isOpen leftOpen_union_rightOpen k]
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
        have hz :
            HomologicalComplex.homologyMap
                (shortComplex leftOpen rightOpen).f k ≫
              HomologicalComplex.homologyMap
                (shortComplex leftOpen rightOpen).g k = 0 := by
          rw [← HomologicalComplex.homologyMap_comp,
            (shortComplex leftOpen rightOpen).zero,
            HomologicalComplex.homologyMap_zero]
        simpa only [Category.assoc, zero_comp, comp_zero] using
          congrArg (fun q ↦
            (booleanIntersectionProductionHomologyIso
                leftOpen rightOpen k).inv ≫ q ≫
              (booleanUnionProductionHomologyIso leftOpen rightOpen
                leftOpen_isOpen rightOpen_isOpen
                leftOpen_union_rightOpen k).hom) hz))
    (overlapIntegerIso k e) (piecesIntegerIso k e) (Iso.refl _)

theorem integerPiecesShortComplex_f (k : ℕ)
    (e : H k Circle ≅ AddCommGrpCat.of ℤ) :
    (integerPiecesShortComplex k e).f = intSignedFold :=
  productionIntersectionArrow_integer_conjugacy k e

theorem integerPiecesShortComplex_g (k : ℕ)
    (e : H k Circle ≅ AddCommGrpCat.of ℤ) :
    (integerPiecesShortComplex k e).g = integerReassemblyArrow k e := by
  rfl

/-- Production Mayer--Vietoris exactness at the two pieces, transported to
literal integral signed-fold coordinates. -/
theorem integerPiecesShortComplex_exact (k : ℕ)
    (e : H k Circle ≅ AddCommGrpCat.of ℤ) :
    (integerPiecesShortComplex k e).Exact := by
  apply transportShortComplex_exact
  exact productionMayerVietoris_exact_pieces leftOpen rightOpen
    leftOpen_isOpen rightOpen_isOpen leftOpen_union_rightOpen k

theorem integerPiecesShortComplex_H0_exact :
    (integerPiecesShortComplex 0 circleH0GroupIsoInt).Exact :=
  integerPiecesShortComplex_exact 0 circleH0GroupIsoInt

theorem integerPiecesShortComplex_H1_exact :
    (integerPiecesShortComplex 1 circleH1GroupIsoInt).Exact :=
  integerPiecesShortComplex_exact 1 circleH1GroupIsoInt

/-- The computed kernel object of the literal arrow occurring in the
transported H0 and H1 segments. -/
noncomputable def integerSignedFoldKernelIso :
    kernel intSignedFold ≅ Z :=
  signedFoldKernelIso Z

/-- The computed cokernel object of the literal arrow occurring in the
transported H0 and H1 segments. -/
noncomputable def integerSignedFoldCokernelIso :
    cokernel intSignedFold ≅ Z :=
  signedFoldCokernelIso Z

#print axioms integerPiecesShortComplex_exact
#print axioms integerPiecesShortComplex_H0_exact
#print axioms integerPiecesShortComplex_H1_exact
#print axioms integerSignedFoldKernelIso
#print axioms integerSignedFoldCokernelIso

end ConstructionTargets.BoundaryTorusMayerVietorisExactness
