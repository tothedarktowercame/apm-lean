import ConstructionTargets.ConnectingMapNegationNaturality
import ConstructionTargets.SingularExcision

/-!
# Comparing Mayer--Vietoris and relative connecting maps

The comparison is made before any topological excision specialization.  For
two simplicial subcomplexes, the union is the pushout of the two pieces over
their intersection.  Quotienting the union by the left piece therefore gives
the same relative chain complex as quotienting the right piece by the
intersection.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ConstructionTargets.PairConnectingMayerVietorisComparison

open ConstructionTargets.SingularExcision

variable {S : SSet} (P Q : S.Subcomplex)

private abbrev chains :=
  (AlgebraicTopology.SSet.singularChainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)

private abbrev intersectionToLeft := subcomplexIntersectionToLeft P Q
private abbrev intersectionToRight := subcomplexIntersectionToRight P Q
private abbrev leftToUnion := subcomplexLeftToUnion P Q
private abbrev rightToUnion := subcomplexRightToUnion P Q

noncomputable local instance intersectionToRight_mono :
    Mono (chains.map (intersectionToRight P Q)) :=
  subcomplexChainsMap_mono (show P ⊓ Q ≤ Q from inf_le_right)

/-- The union-to-relative-chain map supplied by the pushout universal
property.  It kills the left piece and is the quotient projection on the
right piece. -/
noncomputable def unionToRightRelative :
    chains.obj ((P ⊔ Q : S.Subcomplex) : SSet) ⟶
      cokernel (chains.map (intersectionToRight P Q)) :=
  (subcomplexChains_isPushout P Q).desc 0
    (cokernel.π (chains.map (intersectionToRight P Q))) (by simp)

theorem leftToUnion_unionToRightRelative :
    chains.map (leftToUnion P Q) ≫ unionToRightRelative P Q = 0 :=
  (subcomplexChains_isPushout P Q).inl_desc _ _ _

theorem rightToUnion_unionToRightRelative :
    chains.map (rightToUnion P Q) ≫ unionToRightRelative P Q =
      cokernel.π (chains.map (intersectionToRight P Q)) :=
  (subcomplexChains_isPushout P Q).inr_desc _ _ _

/-- The chain-level morphism from the Mayer--Vietoris short exact sequence to
the relative cokernel sequence for the intersection inside the right piece.
The `-𝟙` in degree one is forced by the signed Mayer--Vietoris inclusion.
-/
noncomputable def mayerVietorisToRightRelative :
    subcomplexMayerVietorisShortComplex P Q ⟶
      cokernelShortComplex (chains.map (intersectionToRight P Q)) where
  τ₁ := -𝟙 _
  τ₂ := biprod.snd
  τ₃ := unionToRightRelative P Q
  comm₁₂ := by
    dsimp [subcomplexMayerVietorisShortComplex, cokernelShortComplex, chains]
    rw [biprod.lift_snd]
    exact (Preadditive.neg_comp (𝟙 _) _).trans (by rw [Category.id_comp])
  comm₂₃ := by
    dsimp [subcomplexMayerVietorisShortComplex, cokernelShortComplex]
    apply biprod.hom_ext'
    · calc
        biprod.inl ≫ biprod.snd ≫
            cokernel.π (chains.map (intersectionToRight P Q)) = 0 := by
              rw [← Category.assoc, biprod.inl_snd, zero_comp]
        _ = chains.map (leftToUnion P Q) ≫ unionToRightRelative P Q :=
          (leftToUnion_unionToRightRelative P Q).symm
        _ = biprod.inl ≫ biprod.desc
              (chains.map (leftToUnion P Q))
              (chains.map (rightToUnion P Q)) ≫
                unionToRightRelative P Q := by
          rw [← Category.assoc, biprod.inl_desc]
    · calc
        biprod.inr ≫ biprod.snd ≫
            cokernel.π (chains.map (intersectionToRight P Q)) =
            cokernel.π (chains.map (intersectionToRight P Q)) := by
              rw [← Category.assoc, biprod.inr_snd, Category.id_comp]
        _ = chains.map (rightToUnion P Q) ≫ unionToRightRelative P Q :=
          (rightToUnion_unionToRightRelative P Q).symm
        _ = biprod.inr ≫ biprod.desc
              (chains.map (leftToUnion P Q))
              (chains.map (rightToUnion P Q)) ≫
                unionToRightRelative P Q := by
          rw [← Category.assoc, biprod.inr_desc]

/-- Naturality of connecting maps for the pushout comparison. -/
theorem relativeConnecting_naturality (n : ℕ) :
    subcomplexMayerVietorisConnecting P Q n ≫
        HomologicalComplex.homologyMap (-𝟙 _) n =
      HomologicalComplex.homologyMap (unionToRightRelative P Q) (n + 1) ≫
        (cokernelShortComplex_shortExact
          (chains.map (intersectionToRight P Q))).δ (n + 1) n rfl := by
  exact HomologicalComplex.HomologySequence.δ_naturality
    (mayerVietorisToRightRelative P Q)
    (subcomplexMayerVietorisShortComplex_shortExact P Q)
    (cokernelShortComplex_shortExact
      (chains.map (intersectionToRight P Q))) (n + 1) n rfl

/-- The pair projection followed by the relative connecting map is the
negative of the Mayer--Vietoris connecting map. -/
theorem unionToRelative_connecting_eq_neg_mayerVietoris (n : ℕ) :
    HomologicalComplex.homologyMap (unionToRightRelative P Q) (n + 1) ≫
        (cokernelShortComplex_shortExact
          (chains.map (intersectionToRight P Q))).δ (n + 1) n rfl =
      -subcomplexMayerVietorisConnecting P Q n := by
  have h := relativeConnecting_naturality P Q n
  rw [HomologicalComplex.homologyMap_neg,
    HomologicalComplex.homologyMap_id] at h
  simpa only [Category.comp_id] using h.symm

#print axioms relativeConnecting_naturality
#print axioms unionToRelative_connecting_eq_neg_mayerVietoris

end ConstructionTargets.PairConnectingMayerVietorisComparison
