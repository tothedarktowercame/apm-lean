import ConstructionTargets.CoefficientSingularSubdivision
noncomputable section
namespace ConstructionTargets.CoefficientVertexPrism
open CategoryTheory CategoryTheory.Limits Simplicial SingularSubdivision
variable (R : Type) [CommRing R]
def vertexPrism {ι : Type} [Fintype ι] (n : ℕ) :
    (CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)).X n ⟶
      (CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)).X (n + 1) :=
  match n with
  | 0 => 0
  | n + 1 => by
      change (∐ fun _ : Fin (n + 2) → stdSimplex ℝ ι ↦ ModuleCat.of R R) ⟶ _
      exact Limits.Sigma.desc fun v ↦
        (CoefficientVertexCone.vertexGenerator R _ (n + 1) v ≫
            (CoefficientBarycentricNaturality.vertexSubdivision R (n + 1) - 𝟙 _) -
          CoefficientVertexCone.vertexGenerator R _ (n + 1) v ≫
            (CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)).d (n + 1) n ≫ vertexPrism n) ≫
            CoefficientVertexCone.vertexCone R _ (vertexBarycenter v) (n + 1)
termination_by n

/-- The prism correction in degree `n`: there is no lower differential in
degree zero, and in positive degree it is `∂T`. -/
def vertexPrismCorrection {ι : Type} [Fintype ι] (n : ℕ) :
    (CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)).X n ⟶
      (CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)).X n :=
  match n with
  | 0 => 0
  | n + 1 => (CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)).d (n + 1) n ≫ vertexPrism R n

@[simp] theorem vertexPrism_zero {ι : Type} [Fintype ι] :
    vertexPrism R (ι := ι) 0 = 0 := by simp [vertexPrism]

@[simp, reassoc] theorem vertexGenerator_vertexPrism_succ
    {ι : Type} [Fintype ι] (n : ℕ)
    (v : Fin (n + 2) → stdSimplex ℝ ι) :
    CoefficientVertexCone.vertexGenerator R _ (n + 1) v ≫ vertexPrism R (n + 1) =
      (CoefficientVertexCone.vertexGenerator R _ (n + 1) v ≫
          (CoefficientBarycentricNaturality.vertexSubdivision R (n + 1) - 𝟙 _) -
        CoefficientVertexCone.vertexGenerator R _ (n + 1) v ≫ vertexPrismCorrection R (n + 1)) ≫
          CoefficientVertexCone.vertexCone R _ (vertexBarycenter v) (n + 1) := by
  rw [show vertexPrismCorrection R (ι := ι) (n + 1) =
      (CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)).d (n + 1) n ≫ vertexPrism R n from rfl]
  rw [vertexPrism]
  dsimp [CoefficientVertexCone.vertexGenerator]
  exact Limits.Sigma.ι_desc _ v

theorem d_comp_vertexPrismCorrection {ι : Type} [Fintype ι] (n : ℕ) :
    (CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)).d (n + 1) n ≫
      vertexPrismCorrection R n = 0 := by
  cases n with
  | zero => simp [vertexPrismCorrection]
  | succ n =>
      rw [show vertexPrismCorrection R (ι := ι) (n + 1) =
        (CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)).d (n + 1) n ≫ vertexPrism R n from rfl]
      simp only [← Category.assoc]
      rw [HomologicalComplex.d_comp_d]
      simp

/-- The prism identity `∂T + T∂ = sd - id`. -/
theorem vertexPrism_identity {ι : Type} [Fintype ι] (n : ℕ) :
    vertexPrism R (ι := ι) n ≫
        (CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)).d (n + 1) n +
      vertexPrismCorrection R n =
        CoefficientBarycentricNaturality.vertexSubdivision R n - 𝟙 ((CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)).X n) := by
  induction n with
  | zero => simp [vertexPrismCorrection, CoefficientBarycentricNaturality.vertexSubdivision]
  | succ n ih =>
      apply Limits.Sigma.hom_ext
      intro v
      change CoefficientVertexCone.vertexGenerator R _ (n + 1) v ≫
          (vertexPrism R (n + 1) ≫ _ + vertexPrismCorrection R (n + 1)) =
        CoefficientVertexCone.vertexGenerator R _ (n + 1) v ≫
          (CoefficientBarycentricNaturality.vertexSubdivision R (n + 1) - 𝟙 _)
      rw [Preadditive.comp_add, Preadditive.comp_sub, Category.comp_id]
      rw [← Category.assoc, vertexGenerator_vertexPrism_succ R]
      have hD : (CoefficientBarycentricNaturality.vertexSubdivision R (ι := ι) (n + 1) - 𝟙 _) ≫
          (CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)).d (n + 1) n =
        (CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)).d (n + 1) n ≫
          (CoefficientBarycentricNaturality.vertexSubdivision R n - 𝟙 _) := by
        rw [Preadditive.sub_comp, Preadditive.comp_sub]
        rw [CoefficientBarycentricNaturality.vertexSubdivision_comm_d R, Category.id_comp, Category.comp_id]
      have ht : vertexPrism R (ι := ι) n ≫
          (CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)).d (n + 1) n =
        (CoefficientBarycentricNaturality.vertexSubdivision R n - 𝟙 _) - vertexPrismCorrection R n := by
        rw [eq_sub_iff_add_eq]
        exact ih
      have hz :
          (CoefficientVertexCone.vertexGenerator R _ (n + 1) v ≫
              (CoefficientBarycentricNaturality.vertexSubdivision R (n + 1) - 𝟙 _) -
            CoefficientVertexCone.vertexGenerator R _ (n + 1) v ≫
              vertexPrismCorrection R (n + 1)) ≫
            (CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)).d (n + 1) n = 0 := by
        have hdc : CoefficientVertexCone.vertexGenerator R _ (n + 1) v ≫
            (CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)).d (n + 1) n ≫
            vertexPrismCorrection R n = 0 := by
          rw [d_comp_vertexPrismCorrection R]
          simp
        rw [Preadditive.sub_comp]
        rw [show vertexPrismCorrection R (ι := ι) (n + 1) =
          (CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)).d (n + 1) n ≫ vertexPrism R n from rfl]
        simp only [Category.assoc]
        rw [hD, ht]
        simp only [Preadditive.comp_sub, Category.comp_id]
        rw [hdc]
        simp
      rw [Category.assoc, CoefficientVertexCone.vertexCone_boundary R]
      rw [Preadditive.comp_sub, Category.comp_id]
      rw [← Category.assoc, hz]
      simp


theorem vertexPrism_standardEdge_identity :
    CoefficientVertexCone.vertexGenerator R _ 1 standardEdgeVertices ≫
        (vertexPrism R 1 ≫
            (CoefficientVertexCone.VertexChains R (stdSimplex ℝ (Fin 2))).d 2 1 +
          vertexPrismCorrection R 1) =
      CoefficientVertexCone.vertexGenerator R _ 1 standardEdgeVertices ≫
        (CoefficientBarycentricNaturality.vertexSubdivision R 1 -
          𝟙 ((CoefficientVertexCone.VertexChains R (stdSimplex ℝ (Fin 2))).X 1)) := by
  rw [vertexPrism_identity R]


theorem vertexPrism_natural {ι κ : Type} [Fintype ι] [Fintype κ]
    (f : stdSimplex ℝ ι → stdSimplex ℝ κ)
    (hb : ∀ (n : ℕ) (v : Fin (n + 1) → stdSimplex ℝ ι),
      f (vertexBarycenter v) = vertexBarycenter (f ∘ v)) (n : ℕ) :
    vertexPrism R (ι := ι) n ≫ CoefficientAffineNaturality.vertexMapDegree R f (n + 1) =
      CoefficientAffineNaturality.vertexMapDegree R f n ≫ vertexPrism R (ι := κ) n := by
  induction n with
  | zero => simp
  | succ n ih =>
      apply Limits.Sigma.hom_ext
      intro v
      change (CoefficientVertexCone.vertexGenerator R _ (n + 1) v ≫ vertexPrism R (n + 1)) ≫ _ =
        (CoefficientVertexCone.vertexGenerator R _ (n + 1) v ≫ CoefficientAffineNaturality.vertexMapDegree R f (n + 1)) ≫ _
      rw [vertexGenerator_vertexPrism_succ R,
        CoefficientAffineNaturality.vertexGenerator_vertexMapDegree R, vertexGenerator_vertexPrism_succ R]
      rw [Category.assoc]
      rw [← CoefficientBarycentricNaturality.vertexMapDegree_cone R]
      rw [hb (n + 1) v]
      simp only [← Category.assoc]
      congr 1
      have hc : vertexPrismCorrection R (ι := ι) (n + 1) ≫
          CoefficientAffineNaturality.vertexMapDegree R f (n + 1) =
        CoefficientAffineNaturality.vertexMapDegree R f (n + 1) ≫
          vertexPrismCorrection R (ι := κ) (n + 1) := by
        change ((CoefficientVertexCone.VertexChains R _).d (n + 1) n ≫ vertexPrism R n) ≫ _ =
          _ ≫ (CoefficientVertexCone.VertexChains R _).d (n + 1) n ≫ vertexPrism R n
        simp only [Category.assoc]
        rw [ih, ← Category.assoc, ← CoefficientAffineNaturality.vertexMapDegree_comm_d R f n]
        rw [Category.assoc]
      simp only [Preadditive.sub_comp, Preadditive.comp_sub,
        Category.comp_id, Category.assoc]
      rw [CoefficientBarycentricNaturality.vertexSubdivision_natural R f hb (n + 1), hc,
        ← Category.assoc, CoefficientAffineNaturality.vertexGenerator_vertexMapDegree R]
      rw [← Category.assoc, CoefficientAffineNaturality.vertexGenerator_vertexMapDegree R]

/-- Affine simplex maps commute with the recursive prism. -/
theorem vertexPrism_affine_natural {m : ℕ} {κ : Type} [Fintype κ]
    (u : Fin (m + 1) → stdSimplex ℝ κ) (n : ℕ) :
    vertexPrism R (ι := Fin (m + 1)) n ≫
        CoefficientAffineNaturality.vertexMapDegree R (affineSimplex u) (n + 1) =
      CoefficientAffineNaturality.vertexMapDegree R (affineSimplex u) n ≫ vertexPrism R (ι := κ) n := by
  apply vertexPrism_natural R (ι := Fin (m + 1)) (κ := κ)
  intro q v
  exact affineSimplex_vertexBarycenter u v


theorem integral_standard_edge :
    CoefficientVertexCone.vertexGenerator ℤ _ 1 standardEdgeVertices ≫
        (vertexPrism ℤ 1 ≫
            (CoefficientVertexCone.VertexChains ℤ (stdSimplex ℝ (Fin 2))).d 2 1 +
          vertexPrismCorrection ℤ 1) =
      CoefficientVertexCone.vertexGenerator ℤ _ 1 standardEdgeVertices ≫
        (CoefficientBarycentricNaturality.vertexSubdivision ℤ 1 -
          𝟙 ((CoefficientVertexCone.VertexChains ℤ (stdSimplex ℝ (Fin 2))).X 1)) :=
  vertexPrism_standardEdge_identity ℤ

theorem rational_standard_edge :
    CoefficientVertexCone.vertexGenerator ℚ _ 1 standardEdgeVertices ≫
        (vertexPrism ℚ 1 ≫
            (CoefficientVertexCone.VertexChains ℚ (stdSimplex ℝ (Fin 2))).d 2 1 +
          vertexPrismCorrection ℚ 1) =
      CoefficientVertexCone.vertexGenerator ℚ _ 1 standardEdgeVertices ≫
        (CoefficientBarycentricNaturality.vertexSubdivision ℚ 1 -
          𝟙 ((CoefficientVertexCone.VertexChains ℚ (stdSimplex ℝ (Fin 2))).X 1)) :=
  vertexPrism_standardEdge_identity ℚ

#print axioms vertexPrism_identity
#print axioms vertexPrism_natural
#print axioms vertexPrism_affine_natural
#print axioms integral_standard_edge
#print axioms rational_standard_edge
end ConstructionTargets.CoefficientVertexPrism
