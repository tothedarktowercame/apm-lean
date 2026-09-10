import ConstructionTargets.CoefficientChainCokernelDegreeQuotient
import ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisComplex

noncomputable section
namespace ConstructionTargets.CoefficientSubcomplexRelativeDegreeQuotients

open CategoryTheory CategoryTheory.Limits
open ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows
open ConstructionTargets.CoefficientChainCokernelDegreeQuotient

variable (R : Type) [CommRing R]
variable {S : SSet} (P Q : S.Subcomplex)

noncomputable def intersectionDegreeIso (n : ℕ) :=
  cokernelDegreeQuotientIso R (intersectionAmbient R P Q) n
noncomputable def leftDegreeIso (n : ℕ) :=
  cokernelDegreeQuotientIso R (leftAmbient R P) n
noncomputable def rightDegreeIso (n : ℕ) :=
  cokernelDegreeQuotientIso R (rightAmbient R Q) n
noncomputable def unionDegreeIso (n : ℕ) :=
  cokernelDegreeQuotientIso R (unionAmbient R P Q) n

theorem intersectionDegreeIso_projection (n : ℕ) :
    (cokernel.π (intersectionAmbient R P Q)).f n ≫
      (intersectionDegreeIso R P Q n).hom =
    ModuleCat.ofHom (LinearMap.range ((intersectionAmbient R P Q).f n).hom).mkQ :=
  cokernelDegreeQuotientIso_projection R (intersectionAmbient R P Q) n

theorem leftDegreeIso_projection (n : ℕ) :
    (cokernel.π (leftAmbient R P)).f n ≫ (leftDegreeIso R P n).hom =
    ModuleCat.ofHom (LinearMap.range ((leftAmbient R P).f n).hom).mkQ :=
  cokernelDegreeQuotientIso_projection R (leftAmbient R P) n

theorem rightDegreeIso_projection (n : ℕ) :
    (cokernel.π (rightAmbient R Q)).f n ≫ (rightDegreeIso R Q n).hom =
    ModuleCat.ofHom (LinearMap.range ((rightAmbient R Q).f n).hom).mkQ :=
  cokernelDegreeQuotientIso_projection R (rightAmbient R Q) n

theorem unionDegreeIso_projection (n : ℕ) :
    (cokernel.π (unionAmbient R P Q)).f n ≫ (unionDegreeIso R P Q n).hom =
    ModuleCat.ofHom (LinearMap.range ((unionAmbient R P Q).f n).hom).mkQ :=
  cokernelDegreeQuotientIso_projection R (unionAmbient R P Q) n

#print axioms intersectionDegreeIso_projection
#print axioms leftDegreeIso_projection
#print axioms rightDegreeIso_projection
#print axioms unionDegreeIso_projection
end ConstructionTargets.CoefficientSubcomplexRelativeDegreeQuotients
