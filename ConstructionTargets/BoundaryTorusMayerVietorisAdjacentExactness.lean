import ConstructionTargets.BoundaryTorusMayerVietorisExactness

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option maxHeartbeats 800000

namespace ConstructionTargets.BoundaryTorusMayerVietorisAdjacentExactness

open ConstructionTargets.BoundaryTorusOpenCover
open ConstructionTargets.BoundaryTorusMayerVietoris
open ConstructionTargets.BoundaryTorusMayerVietorisAlgebra
open ConstructionTargets.BoundaryTorusIntegralHomology
open ConstructionTargets.BoundaryTorusMayerVietorisExactness
open ConstructionTargets.ProductionOpenCoverMayerVietoris
open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.BooleanTwoCoverScaffold

private abbrev H (k : ℕ) (X : Type) [TopologicalSpace X] :=
  SingularHomology k (TopCat.of X)

private abbrev Z := BoundaryTorusMayerVietorisAlgebra.IntGroup

/-- The production connecting map, expressed in the two integral overlap
coordinates. -/
noncomputable def integerConnectingArrow (n : ℕ)
    (e : H n Circle ≅ AddCommGrpCat.of ℤ) :
    H (n + 1) ConstructionTargets.SolidTorusGluingOpenCover.BoundaryTorus ⟶
      Z ⊞ Z :=
  productionConnecting leftOpen rightOpen leftOpen_isOpen rightOpen_isOpen
      leftOpen_union_rightOpen n ≫
    (overlapIntegerIso n e).hom

/-- Exactness at the union, with the adjacent piece and overlap objects put
in integral circle coordinates. -/
noncomputable def integerUnionShortComplex (n : ℕ)
    (eSucc : H (n + 1) Circle ≅ AddCommGrpCat.of ℤ)
    (e : H n Circle ≅ AddCommGrpCat.of ℤ) : ShortComplex AddCommGrpCat :=
  transportShortComplex
    (ShortComplex.mk
      (productionReassemblyArrow leftOpen rightOpen (n + 1))
      (productionConnecting leftOpen rightOpen leftOpen_isOpen rightOpen_isOpen
        leftOpen_union_rightOpen n)
      (by
        rw [← booleanReassemblyArrow_eq_production leftOpen rightOpen
          leftOpen_isOpen rightOpen_isOpen leftOpen_union_rightOpen (n + 1)]
        have hcancel :
            HomologicalComplex.homologyMap
                (shortComplex leftOpen rightOpen).g (n + 1) ≫
              (booleanUnionProductionHomologyIso leftOpen rightOpen
                leftOpen_isOpen rightOpen_isOpen leftOpen_union_rightOpen
                (n + 1)).hom ≫
              (booleanUnionProductionHomologyIso leftOpen rightOpen
                leftOpen_isOpen rightOpen_isOpen leftOpen_union_rightOpen
                (n + 1)).inv ≫
              subcomplexMayerVietorisConnecting
                (leftRange leftOpen) (rightRange rightOpen) n =
            HomologicalComplex.homologyMap
                (shortComplex leftOpen rightOpen).g (n + 1) ≫
              subcomplexMayerVietorisConnecting
                (leftRange leftOpen) (rightRange rightOpen) n := by simp
        have hz := (subcomplexMayerVietorisShortComplex_shortExact
          (leftRange leftOpen) (rightRange rightOpen)).comp_δ
            (n + 1) n rfl
        simp only [productionConnecting]
        calc
          _ = (booleanPiecesProductionHomologyIso leftOpen rightOpen
                (n + 1)).inv ≫
              (HomologicalComplex.homologyMap
                  (shortComplex leftOpen rightOpen).g (n + 1) ≫
                (booleanUnionProductionHomologyIso leftOpen rightOpen
                  leftOpen_isOpen rightOpen_isOpen leftOpen_union_rightOpen
                  (n + 1)).hom ≫
                (booleanUnionProductionHomologyIso leftOpen rightOpen
                  leftOpen_isOpen rightOpen_isOpen leftOpen_union_rightOpen
                  (n + 1)).inv ≫
                subcomplexMayerVietorisConnecting
                  (leftRange leftOpen) (rightRange rightOpen) n) ≫
              (booleanIntersectionProductionHomologyIso
                leftOpen rightOpen n).hom := by simp only [Category.assoc]
          _ = (booleanPiecesProductionHomologyIso leftOpen rightOpen
                (n + 1)).inv ≫
              (HomologicalComplex.homologyMap
                  (shortComplex leftOpen rightOpen).g (n + 1) ≫
                subcomplexMayerVietorisConnecting
                  (leftRange leftOpen) (rightRange rightOpen) n) ≫
              (booleanIntersectionProductionHomologyIso
                leftOpen rightOpen n).hom :=
                congrArg (fun q ↦
                  (booleanPiecesProductionHomologyIso leftOpen rightOpen
                    (n + 1)).inv ≫ q ≫
                  (booleanIntersectionProductionHomologyIso
                    leftOpen rightOpen n).hom) hcancel
          _ = (booleanPiecesProductionHomologyIso leftOpen rightOpen
                (n + 1)).inv ≫ 0 ≫
              (booleanIntersectionProductionHomologyIso
                leftOpen rightOpen n).hom :=
                congrArg (fun q ↦
                  (booleanPiecesProductionHomologyIso leftOpen rightOpen
                    (n + 1)).inv ≫ q ≫
                  (booleanIntersectionProductionHomologyIso
                    leftOpen rightOpen n).hom) hz
          _ = 0 := by simp))
    (piecesIntegerIso (n + 1) eSucc) (Iso.refl _)
    (overlapIntegerIso n e)

theorem integerUnionShortComplex_f (n : ℕ)
    (eSucc : H (n + 1) Circle ≅ AddCommGrpCat.of ℤ)
    (e : H n Circle ≅ AddCommGrpCat.of ℤ) :
    (integerUnionShortComplex n eSucc e).f =
      integerReassemblyArrow (n + 1) eSucc := by
  rfl

theorem integerUnionShortComplex_g (n : ℕ)
    (eSucc : H (n + 1) Circle ≅ AddCommGrpCat.of ℤ)
    (e : H n Circle ≅ AddCommGrpCat.of ℤ) :
    (integerUnionShortComplex n eSucc e).g = integerConnectingArrow n e := by
  rfl

theorem integerUnionShortComplex_exact (n : ℕ)
    (eSucc : H (n + 1) Circle ≅ AddCommGrpCat.of ℤ)
    (e : H n Circle ≅ AddCommGrpCat.of ℤ) :
    (integerUnionShortComplex n eSucc e).Exact := by
  apply transportShortComplex_exact
  exact productionMayerVietoris_exact_union leftOpen rightOpen
    leftOpen_isOpen rightOpen_isOpen leftOpen_union_rightOpen n

/-- Exactness at the overlap, with overlap and piece homology in literal
integral coordinates. -/
noncomputable def integerIntersectionShortComplex (n : ℕ)
    (e : H n Circle ≅ AddCommGrpCat.of ℤ) : ShortComplex AddCommGrpCat :=
  transportShortComplex
    (ShortComplex.mk
      (productionConnecting leftOpen rightOpen leftOpen_isOpen rightOpen_isOpen
        leftOpen_union_rightOpen n)
      (productionIntersectionArrow leftOpen rightOpen n)
      (by
        rw [← booleanIntersectionArrow_eq_production leftOpen rightOpen n]
        have hcancel :
            subcomplexMayerVietorisConnecting
                (leftRange leftOpen) (rightRange rightOpen) n ≫
              (booleanIntersectionProductionHomologyIso
                leftOpen rightOpen n).hom ≫
              (booleanIntersectionProductionHomologyIso
                leftOpen rightOpen n).inv ≫
              HomologicalComplex.homologyMap
                (shortComplex leftOpen rightOpen).f n =
            subcomplexMayerVietorisConnecting
                (leftRange leftOpen) (rightRange rightOpen) n ≫
              HomologicalComplex.homologyMap
                (shortComplex leftOpen rightOpen).f n := by
          simpa only [Category.assoc] using congrArg
            (fun q ↦ subcomplexMayerVietorisConnecting
              (leftRange leftOpen) (rightRange rightOpen) n ≫ q)
            ((booleanIntersectionProductionHomologyIso
              leftOpen rightOpen n).hom_inv_id_assoc
                (HomologicalComplex.homologyMap
                  (shortComplex leftOpen rightOpen).f n))
        have hz := (subcomplexMayerVietorisShortComplex_shortExact
          (leftRange leftOpen) (rightRange rightOpen)).δ_comp
            (n + 1) n rfl
        simp only [productionConnecting]
        calc
          _ = (booleanUnionProductionHomologyIso leftOpen rightOpen
                leftOpen_isOpen rightOpen_isOpen leftOpen_union_rightOpen
                (n + 1)).inv ≫
              (subcomplexMayerVietorisConnecting
                  (leftRange leftOpen) (rightRange rightOpen) n ≫
                (booleanIntersectionProductionHomologyIso
                  leftOpen rightOpen n).hom ≫
                (booleanIntersectionProductionHomologyIso
                  leftOpen rightOpen n).inv ≫
                HomologicalComplex.homologyMap
                  (shortComplex leftOpen rightOpen).f n) ≫
              (booleanPiecesProductionHomologyIso leftOpen rightOpen n).hom := by
                simp only [Category.assoc]
          _ = (booleanUnionProductionHomologyIso leftOpen rightOpen
                leftOpen_isOpen rightOpen_isOpen leftOpen_union_rightOpen
                (n + 1)).inv ≫
              (subcomplexMayerVietorisConnecting
                  (leftRange leftOpen) (rightRange rightOpen) n ≫
                HomologicalComplex.homologyMap
                  (shortComplex leftOpen rightOpen).f n) ≫
              (booleanPiecesProductionHomologyIso leftOpen rightOpen n).hom :=
                congrArg (fun q ↦
                  (booleanUnionProductionHomologyIso leftOpen rightOpen
                    leftOpen_isOpen rightOpen_isOpen leftOpen_union_rightOpen
                    (n + 1)).inv ≫ q ≫
                  (booleanPiecesProductionHomologyIso leftOpen rightOpen n).hom)
                  hcancel
          _ = (booleanUnionProductionHomologyIso leftOpen rightOpen
                leftOpen_isOpen rightOpen_isOpen leftOpen_union_rightOpen
                (n + 1)).inv ≫ 0 ≫
              (booleanPiecesProductionHomologyIso leftOpen rightOpen n).hom :=
                congrArg (fun q ↦
                  (booleanUnionProductionHomologyIso leftOpen rightOpen
                    leftOpen_isOpen rightOpen_isOpen leftOpen_union_rightOpen
                    (n + 1)).inv ≫ q ≫
                  (booleanPiecesProductionHomologyIso leftOpen rightOpen n).hom) hz
          _ = 0 := by simp))
    (Iso.refl _) (overlapIntegerIso n e) (piecesIntegerIso n e)

theorem integerIntersectionShortComplex_f (n : ℕ)
    (e : H n Circle ≅ AddCommGrpCat.of ℤ) :
    (integerIntersectionShortComplex n e).f = integerConnectingArrow n e := by
  rfl

theorem integerIntersectionShortComplex_g (n : ℕ)
    (e : H n Circle ≅ AddCommGrpCat.of ℤ) :
    (integerIntersectionShortComplex n e).g = intSignedFold := by
  exact productionIntersectionArrow_integer_conjugacy n e

theorem integerIntersectionShortComplex_exact (n : ℕ)
    (e : H n Circle ≅ AddCommGrpCat.of ℤ) :
    (integerIntersectionShortComplex n e).Exact := by
  apply transportShortComplex_exact
  exact productionMayerVietoris_exact_intersection leftOpen rightOpen
    leftOpen_isOpen rightOpen_isOpen leftOpen_union_rightOpen n

/-- The same intersection segment with both arrows exposed literally. -/
noncomputable def integerIntersectionLiteralShortComplex (n : ℕ)
    (e : H n Circle ≅ AddCommGrpCat.of ℤ) : ShortComplex AddCommGrpCat :=
  ShortComplex.mk (integerConnectingArrow n e) intSignedFold (by
    rw [← integerIntersectionShortComplex_f n e,
      ← integerIntersectionShortComplex_g n e]
    exact (integerIntersectionShortComplex n e).zero)

theorem integerIntersectionLiteralShortComplex_exact (n : ℕ)
    (e : H n Circle ≅ AddCommGrpCat.of ℤ) :
    (integerIntersectionLiteralShortComplex n e).Exact := by
  apply ShortComplex.exact_of_iso ?_ (integerIntersectionShortComplex_exact n e)
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simpa using integerIntersectionShortComplex_f n e)
    (by simpa using (integerIntersectionShortComplex_g n e).symm)

/-- The connecting map lands in the signed-fold kernel. Exactness says that
this canonical lift is epimorphic; it does not choose an inverse or section. -/
noncomputable def integerConnectingKernelLift (n : ℕ)
    (e : H n Circle ≅ AddCommGrpCat.of ℤ) :
    H (n + 1) ConstructionTargets.SolidTorusGluingOpenCover.BoundaryTorus ⟶
      kernel intSignedFold :=
  kernel.lift intSignedFold (integerConnectingArrow n e) (by
    exact (integerIntersectionLiteralShortComplex n e).zero)

theorem integerConnectingKernelLift_epi (n : ℕ)
    (e : H n Circle ≅ AddCommGrpCat.of ℤ) :
    Epi (integerConnectingKernelLift n e) := by
  change Epi (kernel.lift (integerIntersectionLiteralShortComplex n e).g
    (integerIntersectionLiteralShortComplex n e).f
    (integerIntersectionLiteralShortComplex n e).zero)
  exact (integerIntersectionLiteralShortComplex n e).exact_iff_epi_kernel_lift.mp
    (integerIntersectionLiteralShortComplex_exact n e)

/-- The kernel lift followed by the compiled kernel coordinate is still
epimorphic. This is the strongest coordinate normalization forced by
exactness alone. -/
noncomputable def integerConnectingKernelCoordinate (n : ℕ)
    (e : H n Circle ≅ AddCommGrpCat.of ℤ) :
    H (n + 1) ConstructionTargets.SolidTorusGluingOpenCover.BoundaryTorus ⟶ Z :=
  integerConnectingKernelLift n e ≫ (integerSignedFoldKernelIso).hom

instance integerConnectingKernelCoordinate_epi (n : ℕ)
    (e : H n Circle ≅ AddCommGrpCat.of ℤ) :
    Epi (integerConnectingKernelCoordinate n e) := by
  dsimp only [integerConnectingKernelCoordinate]
  letI := integerConnectingKernelLift_epi n e
  infer_instance

theorem integerUnionShortComplex_H1_H0_exact :
    (integerUnionShortComplex 0 circleH1GroupIsoInt circleH0GroupIsoInt).Exact :=
  integerUnionShortComplex_exact 0 circleH1GroupIsoInt circleH0GroupIsoInt

theorem integerIntersectionShortComplex_H0_exact :
    (integerIntersectionShortComplex 0 circleH0GroupIsoInt).Exact :=
  integerIntersectionShortComplex_exact 0 circleH0GroupIsoInt

#print axioms integerUnionShortComplex_exact
#print axioms integerIntersectionShortComplex_exact
#print axioms integerIntersectionLiteralShortComplex_exact
#print axioms integerConnectingKernelLift_epi
#print axioms integerConnectingKernelCoordinate_epi

end ConstructionTargets.BoundaryTorusMayerVietorisAdjacentExactness
