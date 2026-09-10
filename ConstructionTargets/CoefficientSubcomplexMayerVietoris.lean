import ConstructionTargets.CoefficientPushoutRelative

noncomputable section
namespace ConstructionTargets.CoefficientSubcomplexMayerVietoris

open CategoryTheory CategoryTheory.Limits
open SingularExcision

variable (R : Type) [CommRing R]

abbrev chains :=
  (AlgebraicTopology.SSet.singularChainComplexFunctor (ModuleCat R)).obj
    (ModuleCat.of R R)

instance subcomplexChainsMap_component_mono {S : SSet}
    {P Q : S.Subcomplex} (h : P ≤ Q) (n : ℕ) :
    Mono (((chains R).map (SSet.Subcomplex.homOfLE h)).f n) := by
  dsimp [chains, AlgebraicTopology.SSet.singularChainComplexFunctor]
  apply Limits.MonoCoprod.mono_map'_of_injective
  intro x y hxy
  apply Subtype.ext
  simpa only [SSet.Subcomplex.homOfLE_app_val] using congrArg Subtype.val hxy

instance subcomplexChainsMap_mono {S : SSet}
    {P Q : S.Subcomplex} (h : P ≤ Q) :
    Mono ((chains R).map (SSet.Subcomplex.homOfLE h)) :=
  HomologicalComplex.mono_of_mono_f _ fun n =>
    subcomplexChainsMap_component_mono R h n

theorem subcomplexChains_isPushout {S : SSet} (P Q : S.Subcomplex) :
    IsPushout
      ((chains R).map (subcomplexIntersectionToLeft P Q))
      ((chains R).map (subcomplexIntersectionToRight P Q))
      ((chains R).map (subcomplexLeftToUnion P Q))
      ((chains R).map (subcomplexRightToUnion P Q)) := by
  let sq : SSet.Subcomplex.BicartSq (P ⊓ Q) P Q (P ⊔ Q) :=
    { sup_eq := rfl, inf_eq := rfl }
  exact sq.isPushout.map (chains R)

noncomputable def shortComplex {S : SSet} (P Q : S.Subcomplex) :
    ShortComplex (ChainComplex (ModuleCat R) ℕ) :=
  (subcomplexChains_isPushout R P Q).shortComplex

theorem shortExact {S : SSet} (P Q : S.Subcomplex) :
    (shortComplex R P Q).ShortExact := by
  let h := subcomplexChains_isPushout R P Q
  change h.shortComplex.ShortExact
  apply ShortComplex.ShortExact.mk' h.exact_shortComplex
  · dsimp only [CommSq.shortComplex_f]
    change Mono (biprod.lift
      ((chains R).map (SSet.Subcomplex.homOfLE
        (show P ⊓ Q ≤ P from inf_le_left))) _)
    letI : Mono ((chains R).map (SSet.Subcomplex.homOfLE
        (show P ⊓ Q ≤ P from inf_le_left))) :=
      subcomplexChainsMap_mono R (show P ⊓ Q ≤ P from inf_le_left)
    exact mono_of_mono_fac (biprod.lift_fst _ _)
  · exact h.epi_shortComplex_g

noncomputable def connecting {S : SSet} (P Q : S.Subcomplex) (n : ℕ) :
    ((shortComplex R P Q).X₃.homology (n + 1)) ⟶
      ((shortComplex R P Q).X₁.homology n) :=
  (shortExact R P Q).δ (n + 1) n rfl

theorem exact_intersection {S : SSet} (P Q : S.Subcomplex) (n : ℕ) :
    (ShortComplex.mk (connecting R P Q n)
      (HomologicalComplex.homologyMap (shortComplex R P Q).f n)
      ((shortExact R P Q).δ_comp (n + 1) n rfl)).Exact :=
  (shortExact R P Q).homology_exact₁ (n + 1) n rfl

theorem exact_pieces {S : SSet} (P Q : S.Subcomplex) (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (shortComplex R P Q).f n)
      (HomologicalComplex.homologyMap (shortComplex R P Q).g n)
      (by
        rw [← HomologicalComplex.homologyMap_comp]
        rw [(shortComplex R P Q).zero, HomologicalComplex.homologyMap_zero])).Exact :=
  (shortExact R P Q).homology_exact₂ n

theorem exact_union {S : SSet} (P Q : S.Subcomplex) (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (shortComplex R P Q).g (n + 1))
      (connecting R P Q n)
      ((shortExact R P Q).comp_δ (n + 1) n rfl)).Exact :=
  (shortExact R P Q).homology_exact₃ (n + 1) n rfl

#print axioms subcomplexChainsMap_component_mono
#print axioms subcomplexChainsMap_mono
#print axioms subcomplexChains_isPushout
#print axioms shortExact
#print axioms connecting
#print axioms exact_intersection
#print axioms exact_pieces
#print axioms exact_union

end ConstructionTargets.CoefficientSubcomplexMayerVietoris
