import ConstructionTargets.OrientedSimplicialChains

/-!
# Ordered faces versus singular chains

This file isolates the two topological inputs in the standard proof that the
ordered-face complex of a finite geometric simplicial complex computes singular
homology.  The final theorem is deliberately stated exactly as
`OrientedSimplicialChains.orderedFace_singular_quasiIso`.
-/

open Set CategoryTheory
noncomputable section

namespace ConstructionTargets.SimplicialSingularComparison

open ConstructionTargets.OrientedSimplicialChains

/-- Route C, injective half for the concrete affine comparison.  The proof uses
small chains for the open-star cover and a sufficiently subdivided simplicial
approximation back to ordered faces. -/
theorem affineCmp_homologyMap_injective {n : ℕ}
    (o : LinearOrder (Euc n))
    (K : Geometry.SimplicialComplex ℝ (Euc n)) (hK : K.faces.Finite)
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) (hdd : ∀ k, d (k + 1) ≫ d k = 0) (k : ℕ) :
    Function.Injective
      (HomologicalComplex.homologyMap
        (ChainComplex.ofHom _ _ hdd _ _
          (fun j => (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).d_comp_d
            (j + 2) (j + 1) j) (affineCmp o K) (affineCmp_comm o K d hd)) k).hom := by
  sorry

/-- Route C, surjective half for the concrete affine comparison.  Subdivide a
singular cycle until it is open-star-small, approximate it by ordered faces,
and use the carrier prism plus the small-chain homology isomorphism. -/
theorem affineCmp_homologyMap_surjective {n : ℕ}
    (o : LinearOrder (Euc n))
    (K : Geometry.SimplicialComplex ℝ (Euc n)) (hK : K.faces.Finite)
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) (hdd : ∀ k, d (k + 1) ≫ d k = 0) (k : ℕ) :
    Function.Surjective
      (HomologicalComplex.homologyMap
        (ChainComplex.ofHom _ _ hdd _ _
          (fun j => (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).d_comp_d
            (j + 2) (j + 1) j) (affineCmp o K) (affineCmp_comm o K d hd)) k).hom := by
  sorry

/-- The concrete affine comparison is the reference quasi-isomorphism. -/
theorem affine_reference_quasiIso_exists {n : ℕ}
    (o : LinearOrder (Euc n))
    (K : Geometry.SimplicialComplex ℝ (Euc n)) (hK : K.faces.Finite)
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) (hdd : ∀ k, d (k + 1) ≫ d k = 0) :
    ∃ cmp₀ : ∀ k, FaceModuleCat K k ⟶
        (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X k,
      IsAffineComparison K cmp₀ ∧
      (∃ hchain₀ : ∀ k, cmp₀ (k + 1) ≫
          (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).d (k + 1) k =
        d k ≫ cmp₀ k,
        ∀ k, Function.Bijective
          (HomologicalComplex.homologyMap
            (ChainComplex.ofHom _ _ hdd _ _
              (fun k => (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).d_comp_d
              (k + 2) (k + 1) k) cmp₀ hchain₀) k).hom) := by
  refine ⟨affineCmp o K, ?_, affineCmp_comm o K d hd, ?_⟩
  · intro k s
    exact ⟨faceSimplex o s, affineCmp_single o K k s, faceSimplex_range o s⟩
  · intro k
    exact ⟨affineCmp_homologyMap_injective o K hK d hd hdd k,
      affineCmp_homologyMap_surjective o K hK d hd hdd k⟩

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
  sorry

/-- The ordered-face comparison theorem, with the statement kept identical to
`OrientedSimplicialChains.orderedFace_singular_quasiIso`. -/
theorem orderedFace_singular_quasiIso {n : ℕ}
    (o : LinearOrder (Euc n)) (K : Geometry.SimplicialComplex ℝ (Euc n)) (hK : K.faces.Finite)
    (d : ∀ k, FaceModuleCat K (k + 1) ⟶ FaceModuleCat K k)
    (hd : IsSignedDeletion o K d) (hdd : ∀ k, d (k + 1) ≫ d k = 0)
    (cmp : ∀ k, FaceModuleCat K k ⟶
      (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).X k)
    (hcmp : IsAffineComparison K cmp)
    (hchain : ∀ k, cmp (k + 1) ≫
        (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).d (k + 1) k =
      d k ≫ cmp k) :
    ∀ k, Function.Bijective
      (HomologicalComplex.homologyMap
        (ChainComplex.ofHom _ _ hdd _ _
          (fun k => (CoefficientH0.SingularChains ℚ (TopCat.of K.space)).d_comp_d
            (k + 2) (k + 1) k) cmp hchain) k).hom := by
  obtain ⟨cmp₀, hcmp₀, hchain₀, hbij⟩ :=
    affine_reference_quasiIso_exists o K hK d hd hdd
  intro k
  rw [← affineComparison_homologyMap_eq o K d hd hdd cmp₀ cmp
    hcmp₀ hcmp hchain₀ hchain k]
  exact hbij k

#print axioms orderedFace_singular_quasiIso

end ConstructionTargets.SimplicialSingularComparison
