import ConstructionTargets.OrientedSimplicialChains
import ConstructionTargets.AcyclicCarriers

/-!
# Ordered faces versus singular chains

This file isolates the two topological inputs in the standard proof that the
ordered-face complex of a finite geometric simplicial complex computes singular
homology.  The carrier-invariance half, `affineComparison_homologyMap_eq`, is
here. The two directions and the final theorem
`orderedFace_singular_quasiIso` (stated exactly as
`OrientedSimplicialChains.orderedFace_singular_quasiIso`) moved to
`SimplicialSingularQuasiIso` on 2026-10-30, because their proof needs the
subdivision chain maps in `SimplicialChainMaps`, which imports this file.
-/

open Set CategoryTheory
noncomputable section

namespace ConstructionTargets.SimplicialSingularComparison

open ConstructionTargets.OrientedSimplicialChains

/-- Route C, uniqueness half: two chain maps carried face-by-face by the closed
convex hulls are chain homotopic, hence induce the same map on homology.  Notice
that the conclusion is equality, not bijectivity; this is the acyclic-carriers
transfer step and does not contain the reference quasi-isomorphism theorem. -/
theorem affineComparison_homologyMap_eq {n : ℕ}
    (o : LinearOrder (Euc n))
    (K : Geometry.SimplicialComplex ℝ (Euc n))
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) (hdd : ∀ k, d (k + 1) ≫ d k = 0)
    (cmp₁ cmp₂ : ∀ k, FaceModuleCat K k ⟶
      (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X k)
    (hcmp₁ : IsAffineComparison K cmp₁) (hcmp₂ : IsAffineComparison K cmp₂)
    (hchain₁ : ∀ k, cmp₁ (k + 1) ≫
        (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).d (k + 1) k =
      d k ≫ cmp₁ k)
    (hchain₂ : ∀ k, cmp₂ (k + 1) ≫
        (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).d (k + 1) k =
      d k ≫ cmp₂ k) :
    ∀ k,
      (HomologicalComplex.homologyMap
        (ChainComplex.ofHom _ _ hdd _ _
          (fun j => (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).d_comp_d
            (j + 2) (j + 1) j) cmp₁ hchain₁) k).hom =
      (HomologicalComplex.homologyMap
        (ChainComplex.ofHom _ _ hdd _ _
          (fun j => (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).d_comp_d
            (j + 2) (j + 1) j) cmp₂ hchain₂) k).hom := by
  open ConstructionTargets.AcyclicCarriers in
    have hzero := affineComparison_degreeZero_eq K cmp₁ cmp₂ hcmp₁ hcmp₂
    have hfill : ∀ (k : ℕ) (s : FaceIndex K k) (z : (SingularQChains K).X k),
        FaceCarriedChain K s.1 z → (SingularQChains K).d k (k - 1) z = 0 →
        0 < k → ∃ w : (SingularQChains K).X (k + 1),
          FaceCarriedChain K s.1 w ∧ (SingularQChains K).d (k + 1) k w = z := by
      intro k s z hz hcycle hk
      exact faceCarriedCycle_bounds K s (faceHull_rationallyPointlike K s) z hz hcycle hk
    obtain ⟨H⟩ := carried_chainHomotopy_exists o K d hd hdd cmp₁ cmp₂
      hcmp₁ hcmp₂ hchain₁ hchain₂ hzero hfill
    intro k
    exact congrArg (fun q ↦ q.hom) (H.homologyMap_eq k)

end ConstructionTargets.SimplicialSingularComparison
