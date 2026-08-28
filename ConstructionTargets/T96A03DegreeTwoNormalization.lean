import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod

/-!
# Rank-three normalization for the t96A03 Mayer--Vietoris calculation

This file contains only the generic linear algebra which identifies a
rank-two coordinate module extended by one free coordinate with the frozen
`Fin 3 → ℤ` representation.
-/

noncomputable section

namespace ConstructionTargets.T96A03DegreeTwoNormalization

/-- Split the last coordinate of a `Fin 3`-indexed family, with the factors
ordered as the first two coordinates followed by the final coordinate. -/
def finTwoProdIntLinearEquiv :
    ((Fin 2 → ℤ) × ℤ) ≃ₗ[ℤ] (Fin 3 → ℤ) :=
  LinearEquiv.prodComm ℤ (Fin 2 → ℤ) ℤ ≪≫ₗ
    (LinearEquiv.piCongrLeft ℤ (fun _ : Option (Fin 2) => ℤ) (finSuccEquiv 2) ≪≫ₗ
      LinearEquiv.piOptionEquivProd ℤ).symm

/-- Categorical form of `finTwoProdIntLinearEquiv`, matching integral
singular homology's `ModuleCat ℤ` codomain. -/
def finTwoProdIntModuleIso :
    ModuleCat.of ℤ ((Fin 2 → ℤ) × ℤ) ≅ ModuleCat.of ℤ (Fin 3 → ℤ) :=
  finTwoProdIntLinearEquiv.toModuleIso

theorem nonempty_finTwoProdIntModuleIso :
    Nonempty
      (ModuleCat.of ℤ ((Fin 2 → ℤ) × ℤ) ≅
        ModuleCat.of ℤ (Fin 3 → ℤ)) :=
  ⟨finTwoProdIntModuleIso⟩

#print axioms finTwoProdIntLinearEquiv
#print axioms finTwoProdIntModuleIso
#print axioms nonempty_finTwoProdIntModuleIso

end ConstructionTargets.T96A03DegreeTwoNormalization
