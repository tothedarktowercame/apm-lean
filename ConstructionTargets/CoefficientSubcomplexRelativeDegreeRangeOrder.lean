import ConstructionTargets.CoefficientSubcomplexRelativeDegreeQuotients

noncomputable section
namespace ConstructionTargets.CoefficientSubcomplexRelativeDegreeRangeOrder

open CategoryTheory
open ConstructionTargets.SingularExcision
open ConstructionTargets.CoefficientSubcomplexMayerVietoris
open ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows

variable (R : Type) [CommRing R]
variable {S : SSet} (P Q : S.Subcomplex)

theorem intersectionAmbient_factor_left (n : ℕ) :
    (intersectionAmbient R P Q).f n =
      ((chains R).map (subcomplexIntersectionToLeft P Q)).f n ≫
        (leftAmbient R P).f n := by
  change ((chains R).map (P ⊓ Q).ι).f n = _
  rw [← HomologicalComplex.comp_f]
  apply HomologicalComplex.congr_hom
  dsimp [leftAmbient]
  rw [← Functor.map_comp]
  rfl

theorem intersectionAmbient_factor_right (n : ℕ) :
    (intersectionAmbient R P Q).f n =
      ((chains R).map (subcomplexIntersectionToRight P Q)).f n ≫
        (rightAmbient R Q).f n := by
  change ((chains R).map (P ⊓ Q).ι).f n = _
  rw [← HomologicalComplex.comp_f]
  apply HomologicalComplex.congr_hom
  dsimp [rightAmbient]
  rw [← Functor.map_comp]
  rfl

theorem leftAmbient_factor_union (n : ℕ) :
    (leftAmbient R P).f n =
      ((chains R).map (subcomplexLeftToUnion P Q)).f n ≫
        (unionAmbient R P Q).f n := by
  change ((chains R).map P.ι).f n = _
  rw [← HomologicalComplex.comp_f]
  apply HomologicalComplex.congr_hom
  dsimp [unionAmbient]
  rw [← Functor.map_comp]
  rfl

theorem rightAmbient_factor_union (n : ℕ) :
    (rightAmbient R Q).f n =
      ((chains R).map (subcomplexRightToUnion P Q)).f n ≫
        (unionAmbient R P Q).f n := by
  change ((chains R).map Q.ι).f n = _
  rw [← HomologicalComplex.comp_f]
  apply HomologicalComplex.congr_hom
  dsimp [unionAmbient]
  rw [← Functor.map_comp]
  rfl

theorem intersectionRange_le_inf (n : ℕ) :
    LinearMap.range ((intersectionAmbient R P Q).f n).hom ≤
      LinearMap.range ((leftAmbient R P).f n).hom ⊓
        LinearMap.range ((rightAmbient R Q).f n).hom := by
  apply le_inf
  · rw [intersectionAmbient_factor_left R P Q n]
    exact LinearMap.range_comp_le_range _ _
  · rw [intersectionAmbient_factor_right R P Q n]
    exact LinearMap.range_comp_le_range _ _

theorem sup_le_unionRange (n : ℕ) :
    LinearMap.range ((leftAmbient R P).f n).hom ⊔
        LinearMap.range ((rightAmbient R Q).f n).hom ≤
      LinearMap.range ((unionAmbient R P Q).f n).hom := by
  apply sup_le
  · rw [leftAmbient_factor_union R P Q n]
    exact LinearMap.range_comp_le_range _ _
  · rw [rightAmbient_factor_union R P Q n]
    exact LinearMap.range_comp_le_range _ _

#print axioms intersectionRange_le_inf
#print axioms sup_le_unionRange
end ConstructionTargets.CoefficientSubcomplexRelativeDegreeRangeOrder
