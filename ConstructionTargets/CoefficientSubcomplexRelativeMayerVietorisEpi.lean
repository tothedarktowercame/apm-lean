import ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisComplex

noncomputable section
namespace ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisEpi

open CategoryTheory CategoryTheory.Limits
open ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows
open ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisComplex

variable (R : Type) [CommRing R]
variable {S : SSet} (P Q : S.Subcomplex)

noncomputable instance leftToUnionRelative_epi :
    Epi (leftToUnionRelative R P Q) := by
  exact epi_of_epi_fac (leftToUnionRelative_projection R P Q)

noncomputable instance rightToUnionRelative_epi :
    Epi (rightToUnionRelative R P Q) := by
  exact epi_of_epi_fac (rightToUnionRelative_projection R P Q)

theorem inl_piecesToUnionRelative :
    biprod.inl ≫ piecesToUnionRelative R P Q =
      leftToUnionRelative R P Q := by
  dsimp [piecesToUnionRelative]
  rw [biprod.inl_desc]

noncomputable instance piecesToUnionRelative_epi :
    Epi (piecesToUnionRelative R P Q) := by
  exact epi_of_epi_fac (inl_piecesToUnionRelative R P Q)

#print axioms leftToUnionRelative_epi
#print axioms rightToUnionRelative_epi
#print axioms piecesToUnionRelative_epi
end ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisEpi
