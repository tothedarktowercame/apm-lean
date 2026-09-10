import ConstructionTargets.CoefficientSubspaceUnionRelativeCokernelSquare
import ConstructionTargets.CoefficientSubcomplexMayerVietoris

noncomputable section
namespace ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows

open CategoryTheory CategoryTheory.Limits
open ConstructionTargets.SingularExcision
open ConstructionTargets.CoefficientSubcomplexMayerVietoris

variable (R : Type) [CommRing R]
variable {S : SSet} (P Q : S.Subcomplex)

abbrev C (S : SSet) := (chains R).obj S
abbrev intersectionC := (chains R).obj ((P ⊓ Q : S.Subcomplex) : SSet)
abbrev leftC := (chains R).obj (P : SSet)
abbrev rightC := (chains R).obj (Q : SSet)
abbrev unionC := (chains R).obj ((P ⊔ Q : S.Subcomplex) : SSet)

noncomputable def intersectionAmbient : intersectionC R P Q ⟶ C R S :=
  (chains R).map (P ⊓ Q).ι
noncomputable def leftAmbient : leftC R P ⟶ C R S := (chains R).map P.ι
noncomputable def rightAmbient : rightC R Q ⟶ C R S := (chains R).map Q.ι
noncomputable def unionAmbient : unionC R P Q ⟶ C R S :=
  (chains R).map (P ⊔ Q).ι

noncomputable def intersectionToLeftRelative :
    cokernel (intersectionAmbient R P Q) ⟶ cokernel (leftAmbient R P) :=
  cokernel.map _ _ ((chains R).map (subcomplexIntersectionToLeft P Q))
    (𝟙 _) (by
      rw [Category.comp_id]
      dsimp [intersectionAmbient, leftAmbient]
      symm
      rw [← Functor.map_comp]
      rfl)

noncomputable def intersectionToRightRelative :
    cokernel (intersectionAmbient R P Q) ⟶ cokernel (rightAmbient R Q) :=
  cokernel.map _ _ ((chains R).map (subcomplexIntersectionToRight P Q))
    (𝟙 _) (by
      rw [Category.comp_id]
      dsimp [intersectionAmbient, rightAmbient]
      symm
      rw [← Functor.map_comp]
      rfl)

noncomputable def intersectionToPiecesRelative :
    cokernel (intersectionAmbient R P Q) ⟶
      cokernel (leftAmbient R P) ⊞ cokernel (rightAmbient R Q) :=
  biprod.lift (intersectionToLeftRelative R P Q)
    (intersectionToRightRelative R P Q)

noncomputable def leftToUnionRelative :
    cokernel (leftAmbient R P) ⟶ cokernel (unionAmbient R P Q) :=
  cokernel.map _ _ ((chains R).map (subcomplexLeftToUnion P Q))
    (𝟙 _) (by
      rw [Category.comp_id]
      dsimp [leftAmbient, unionAmbient]
      symm
      rw [← Functor.map_comp]
      rfl)

noncomputable def rightToUnionRelative :
    cokernel (rightAmbient R Q) ⟶ cokernel (unionAmbient R P Q) :=
  cokernel.map _ _ ((chains R).map (subcomplexRightToUnion P Q))
    (𝟙 _) (by
      rw [Category.comp_id]
      dsimp [rightAmbient, unionAmbient]
      symm
      rw [← Functor.map_comp]
      rfl)

noncomputable def piecesToUnionRelative :
    cokernel (leftAmbient R P) ⊞ cokernel (rightAmbient R Q) ⟶
      cokernel (unionAmbient R P Q) :=
  biprod.desc (leftToUnionRelative R P Q) (-rightToUnionRelative R P Q)

#print axioms intersectionToPiecesRelative
#print axioms piecesToUnionRelative
end ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisArrows
