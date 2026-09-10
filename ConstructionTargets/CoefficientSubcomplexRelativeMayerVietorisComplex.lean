import ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows

noncomputable section
namespace ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisComplex

open CategoryTheory CategoryTheory.Limits
open ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows

variable (R : Type) [CommRing R]
variable {S : SSet} (P Q : S.Subcomplex)

theorem intersectionToLeftRelative_projection :
    cokernel.π (intersectionAmbient R P Q) ≫
      intersectionToLeftRelative R P Q =
    cokernel.π (leftAmbient R P) := by
  exact cokernel.π_desc _ _ _

theorem intersectionToRightRelative_projection :
    cokernel.π (intersectionAmbient R P Q) ≫
      intersectionToRightRelative R P Q =
    cokernel.π (rightAmbient R Q) := by
  exact cokernel.π_desc _ _ _

theorem leftToUnionRelative_projection :
    cokernel.π (leftAmbient R P) ≫ leftToUnionRelative R P Q =
      cokernel.π (unionAmbient R P Q) := by
  exact cokernel.π_desc _ _ _

theorem rightToUnionRelative_projection :
    cokernel.π (rightAmbient R Q) ≫ rightToUnionRelative R P Q =
      cokernel.π (unionAmbient R P Q) := by
  exact cokernel.π_desc _ _ _

theorem relative_arrows_zero :
    intersectionToPiecesRelative R P Q ≫
      piecesToUnionRelative R P Q = 0 := by
  apply (cancel_epi (cokernel.π (intersectionAmbient R P Q))).1
  rw [comp_zero]
  dsimp [intersectionToPiecesRelative, piecesToUnionRelative]
  rw [biprod.lift_desc, Preadditive.comp_add,
    ← Category.assoc,
    intersectionToLeftRelative_projection,
    ← Category.assoc,
    leftToUnionRelative_projection,
    intersectionToRightRelative_projection,
    Preadditive.comp_neg,
    rightToUnionRelative_projection,
    add_neg_cancel]

noncomputable def shortComplex :
    ShortComplex (ChainComplex (ModuleCat R) ℕ) :=
  ShortComplex.mk (intersectionToPiecesRelative R P Q)
    (piecesToUnionRelative R P Q) (relative_arrows_zero R P Q)

theorem shortComplex_f : (shortComplex R P Q).f =
    intersectionToPiecesRelative R P Q := rfl

theorem shortComplex_g : (shortComplex R P Q).g =
    piecesToUnionRelative R P Q := rfl

#print axioms relative_arrows_zero
#print axioms shortComplex
end ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisComplex
