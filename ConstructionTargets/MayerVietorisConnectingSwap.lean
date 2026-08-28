import ConstructionTargets.ConnectingMapNegationNaturality
import ConstructionTargets.SingularExcision

/-!
# Swapping a Mayer--Vietoris cover negates its connecting map
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ConstructionTargets.MayerVietorisConnectingSwap

open ConstructionTargets.SingularExcision
open ConstructionTargets.ConnectingMapNegationNaturality

variable {S : SSet} (P Q : S.Subcomplex)

private abbrev chains :=
  (AlgebraicTopology.SSet.singularChainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)

def intersectionSSetIso :
    ((P ⊓ Q : S.Subcomplex) : SSet) ≅ ((Q ⊓ P : S.Subcomplex) : SSet) where
  hom := SSet.Subcomplex.homOfLE (by simpa [inf_comm])
  inv := SSet.Subcomplex.homOfLE (by simpa [inf_comm])
  hom_inv_id := by ext Δ x; apply Subtype.ext; rfl
  inv_hom_id := by ext Δ x; apply Subtype.ext; rfl

def intersectionChainsIso :
    chains.obj ((P ⊓ Q : S.Subcomplex) : SSet) ≅
      chains.obj ((Q ⊓ P : S.Subcomplex) : SSet) :=
  chains.mapIso (intersectionSSetIso P Q)

def unionSSetIso :
    ((P ⊔ Q : S.Subcomplex) : SSet) ≅ ((Q ⊔ P : S.Subcomplex) : SSet) where
  hom := SSet.Subcomplex.homOfLE (by simpa [sup_comm])
  inv := SSet.Subcomplex.homOfLE (by simpa [sup_comm])
  hom_inv_id := by ext Δ x; apply Subtype.ext; rfl
  inv_hom_id := by ext Δ x; apply Subtype.ext; rfl

def unionChainsIso :
    chains.obj ((P ⊔ Q : S.Subcomplex) : SSet) ≅
      chains.obj ((Q ⊔ P : S.Subcomplex) : SSet) :=
  chains.mapIso (unionSSetIso P Q)

def piecesChainsIso :
    chains.obj (P : SSet) ⊞ chains.obj (Q : SSet) ≅
      chains.obj (Q : SSet) ⊞ chains.obj (P : SSet) :=
  biprod.braiding _ _

private theorem intersectionEqToHom_left :
    (intersectionSSetIso P Q).hom ≫
      subcomplexIntersectionToLeft Q P =
        subcomplexIntersectionToRight P Q := by
  ext Δ x
  apply Subtype.ext
  rfl

private theorem intersectionEqToHom_right :
    (intersectionSSetIso P Q).hom ≫
      subcomplexIntersectionToRight Q P =
        subcomplexIntersectionToLeft P Q := by
  ext Δ x
  apply Subtype.ext
  rfl

private theorem leftToUnion_eq_unionEqToHom :
    subcomplexLeftToUnion P Q ≫
      (unionSSetIso P Q).hom =
        subcomplexRightToUnion Q P := by
  ext Δ x
  apply Subtype.ext
  rfl

private theorem rightToUnion_eq_unionEqToHom :
    subcomplexRightToUnion P Q ≫
      (unionSSetIso P Q).hom =
        subcomplexLeftToUnion Q P := by
  ext Δ x
  apply Subtype.ext
  rfl

noncomputable def swapShortComplexHom :
    subcomplexMayerVietorisShortComplex P Q ⟶
      subcomplexMayerVietorisShortComplex Q P where
  τ₁ := -(intersectionChainsIso P Q).hom
  τ₂ := (piecesChainsIso P Q).hom
  τ₃ := (unionChainsIso P Q).hom
  comm₁₂ := by
    dsimp [subcomplexMayerVietorisShortComplex, piecesChainsIso,
      intersectionChainsIso, chains]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst, Functor.mapIso_hom,
        Preadditive.neg_comp, Preadditive.comp_neg, neg_neg,
        ← Functor.map_comp]
      rw [intersectionEqToHom_left]
      exact (biprod.lift_snd _ _).symm
    · simp only [Category.assoc, biprod.lift_snd, Functor.mapIso_hom,
        Preadditive.neg_comp, Preadditive.comp_neg, neg_neg,
        ← Functor.map_comp]
      rw [intersectionEqToHom_right]
      exact (biprod.lift_fst _ _).symm
  comm₂₃ := by
    dsimp [subcomplexMayerVietorisShortComplex, piecesChainsIso,
      unionChainsIso, chains, biprod.braiding]
    apply biprod.hom_ext'
    · slice_lhs 1 2 =>
        rw [show biprod.inl ≫ biprod.lift biprod.snd biprod.fst = biprod.inr by
          apply biprod.hom_ext <;> simp]
      rw [biprod.inr_desc]
      slice_rhs 1 2 => rw [biprod.inl_desc]
      rw [← Functor.map_comp]
      rw [leftToUnion_eq_unionEqToHom]
    · slice_lhs 1 2 =>
        rw [show biprod.inr ≫ biprod.lift biprod.snd biprod.fst = biprod.inl by
          apply biprod.hom_ext <;> simp]
      rw [biprod.inl_desc]
      slice_rhs 1 2 => rw [biprod.inr_desc]
      rw [← Functor.map_comp]
      rw [rightToUnion_eq_unionEqToHom]

theorem connecting_swap (n : ℕ) :
    subcomplexMayerVietorisConnecting Q P n =
      HomologicalComplex.homologyMap (unionChainsIso P Q).inv (n + 1) ≫
        (-subcomplexMayerVietorisConnecting P Q n) ≫
          HomologicalComplex.homologyMap (intersectionChainsIso P Q).hom n := by
  apply delta_eq_neg_of_first_neg_iso_third_iso
      (swapShortComplexHom P Q)
      (subcomplexMayerVietorisShortComplex_shortExact P Q)
      (subcomplexMayerVietorisShortComplex_shortExact Q P)
      (intersectionChainsIso P Q) (unionChainsIso P Q)
      rfl rfl (n + 1) n rfl

#print axioms connecting_swap

end ConstructionTargets.MayerVietorisConnectingSwap
