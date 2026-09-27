import ConstructionTargets.CoefficientSubcomplexRelativeDegreeArrowComparison
import ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisDegreewiseCriterion

noncomputable section
namespace ConstructionTargets.CoefficientSubcomplexRelativeDegreewiseExact

open CategoryTheory CategoryTheory.Limits
open ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows
open ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisComplex
open ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisDegreewiseCriterion
open ConstructionTargets.CoefficientSubcomplexRelativeDegreeQuotients
open ConstructionTargets.CoefficientSubcomplexRelativeDegreeArrowComparison
open ConstructionTargets.CoefficientSubmoduleInfQuotientDiagonal
open ConstructionTargets.CoefficientSubmoduleRelativeMayerVietorisExact

variable (R : Type) [CommRing R]
variable {S : SSet} (P Q : S.Subcomplex)

/-- The middle degree object is linearly equivalent to the product of the two
ordinary quotient modules. -/
noncomputable def piecesCoordinatesEquiv (n : ℕ) :
    ((cokernel (leftAmbient R P) ⊞ cokernel (rightAmbient R Q)).X n) ≃ₗ[R]
      (((C R S).X n ⧸ leftRange R P n) ×
        ((C R S).X n ⧸ rightRange R Q n)) :=
  (HomologicalComplex.biprodXIso
      (cokernel (leftAmbient R P)) (cokernel (rightAmbient R Q)) n).toLinearEquiv.trans
    ((ModuleCat.biprodIsoProd _ _).toLinearEquiv.trans
      ((leftDegreeIso R P n).toLinearEquiv.prodCongr
        (rightDegreeIso R Q n).toLinearEquiv))

theorem piecesCoordinatesEquiv_toLinearMap (n : ℕ) :
    (piecesCoordinatesEquiv R P Q n).toLinearMap = piecesCoordinates R P Q n := by
  ext x
  · change (((HomologicalComplex.biprodXIso
        (cokernel (leftAmbient R P)) (cokernel (rightAmbient R Q)) n).hom ≫
      (ModuleCat.biprodIsoProd _ _).hom ≫
      ModuleCat.ofHom (LinearMap.fst R _ _) ≫
      (leftDegreeIso R P n).hom) x) = _
    rw [← ModuleCat.biprodIsoProd_inv_comp_fst]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc, HomologicalComplex.biprodXIso_hom_fst]
    rfl
  · change (((HomologicalComplex.biprodXIso
        (cokernel (leftAmbient R P)) (cokernel (rightAmbient R Q)) n).hom ≫
      (ModuleCat.biprodIsoProd _ _).hom ≫
      ModuleCat.ofHom (LinearMap.snd R _ _) ≫
      (rightDegreeIso R Q n).hom) x) = _
    rw [← ModuleCat.biprodIsoProd_inv_comp_snd]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc, HomologicalComplex.biprodXIso_hom_snd]
    rfl

theorem intersectionToPieces_degree_injective (n : ℕ) :
    Function.Injective ((intersectionToPiecesRelative R P Q).f n) := by
  intro x y hxy
  apply (intersectionInfEquiv R P Q n).injective
  apply (infQuotientDiagonal_injective R (leftRange R P n) (rightRange R Q n))
  have h := DFunLike.congr_fun (intersectionToPieces_degree R P Q n) x
  have h' := DFunLike.congr_fun (intersectionToPieces_degree R P Q n) y
  calc
    _ = piecesCoordinates R P Q n
        (((intersectionToPiecesRelative R P Q).f n) x) := by simpa using h.symm
    _ = piecesCoordinates R P Q n
        (((intersectionToPiecesRelative R P Q).f n) y) := congrArg _ hxy
    _ = _ := by simpa using h'

theorem relative_degree_exact (n : ℕ) :
    Function.Exact ((intersectionToPiecesRelative R P Q).f n)
      ((piecesToUnionRelative R P Q).f n) := by
  intro y
  constructor
  · intro hy
    have htarget : piecesToSupQuotient R (leftRange R P n) (rightRange R Q n)
        (piecesCoordinates R P Q n y) = 0 := by
      have h := LinearMap.congr_fun (piecesToUnion_degree R P Q n) y
      calc
        _ = (unionSupEquiv R P Q n)
            (((piecesToUnionRelative R P Q).f n) y) := by simpa using h.symm
        _ = 0 := by simp [hy]
    rcases ((infQuotientDiagonal_piecesToSupQuotient_exact R
      (leftRange R P n) (rightRange R Q n))
        (piecesCoordinates R P Q n y)).1 htarget with ⟨z, hz⟩
    refine ⟨(intersectionInfEquiv R P Q n).symm z, ?_⟩
    apply (piecesCoordinatesEquiv R P Q n).injective
    change (piecesCoordinatesEquiv R P Q n).toLinearMap
        (((intersectionToPiecesRelative R P Q).f n)
          ((intersectionInfEquiv R P Q n).symm z)) =
      (piecesCoordinatesEquiv R P Q n).toLinearMap y
    rw [piecesCoordinatesEquiv_toLinearMap]
    calc
      _ = infQuotientDiagonal R (leftRange R P n) (rightRange R Q n)
          ((intersectionInfEquiv R P Q n)
            ((intersectionInfEquiv R P Q n).symm z)) := by
              simpa using DFunLike.congr_fun
                (intersectionToPieces_degree R P Q n)
                ((intersectionInfEquiv R P Q n).symm z)
      _ = infQuotientDiagonal R (leftRange R P n) (rightRange R Q n) z := by simp
      _ = piecesCoordinates R P Q n y := hz
  · rintro ⟨x, rfl⟩
    change (((intersectionToPiecesRelative R P Q) ≫
      (piecesToUnionRelative R P Q)).f n) x = 0
    rw [relative_arrows_zero]
    rfl

/-- The genuine relative quotient short complex is short exact. -/
theorem shortComplex_shortExact : (shortComplex R P Q).ShortExact := by
  apply shortComplex_shortExact_of_degreewise R P Q
  · exact intersectionToPieces_degree_injective R P Q
  · exact relative_degree_exact R P Q

#print axioms piecesCoordinatesEquiv_toLinearMap
#print axioms intersectionToPieces_degree_injective
#print axioms relative_degree_exact
#print axioms shortComplex_shortExact
end ConstructionTargets.CoefficientSubcomplexRelativeDegreewiseExact
