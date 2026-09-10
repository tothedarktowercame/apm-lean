import ConstructionTargets.CoefficientAffineNaturality
noncomputable section
namespace ConstructionTargets.CoefficientBarycentricNaturality
open CategoryTheory CategoryTheory.Limits Simplicial ConstructionTargets.SingularSubdivision
variable (R : Type) [CommRing R]
def vertexSubdivision {ι : Type} [Fintype ι] (n : ℕ) :
    (ConstructionTargets.CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)).X n ⟶
      (ConstructionTargets.CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)).X n :=
  match n with
  | 0 => 𝟙 _
  | n + 1 => by
      change (∐ fun _ : Fin (n + 2) → stdSimplex ℝ ι ↦ ModuleCat.of R R) ⟶ _
      exact Limits.Sigma.desc fun v ↦
        ConstructionTargets.CoefficientVertexCone.vertexGenerator R _ (n + 1) v ≫
          (ConstructionTargets.CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)).d (n + 1) n ≫
          vertexSubdivision n ≫ ConstructionTargets.CoefficientVertexCone.vertexCone R _ (vertexBarycenter v) n

@[simp] theorem vertexGenerator_vertexSubdivision_zero
    {ι : Type} [Fintype ι] (v : Fin 1 → stdSimplex ℝ ι) :
    ConstructionTargets.CoefficientVertexCone.vertexGenerator R _ 0 v ≫ vertexSubdivision R 0 = ConstructionTargets.CoefficientVertexCone.vertexGenerator R _ 0 v := by
  simp [vertexSubdivision]

@[simp] theorem vertexGenerator_vertexSubdivision_succ
    {ι : Type} [Fintype ι] (n : ℕ)
    (v : Fin (n + 2) → stdSimplex ℝ ι) :
    ConstructionTargets.CoefficientVertexCone.vertexGenerator R _ (n + 1) v ≫ vertexSubdivision R (n + 1) =
      ConstructionTargets.CoefficientVertexCone.vertexGenerator R _ (n + 1) v ≫
        (ConstructionTargets.CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)).d (n + 1) n ≫
        vertexSubdivision R n ≫ ConstructionTargets.CoefficientVertexCone.vertexCone R _ (vertexBarycenter v) n := by
  dsimp [vertexSubdivision, ConstructionTargets.CoefficientVertexCone.vertexGenerator]
  exact Limits.Sigma.ι_desc _ v

/-- Subdivision commutes with the differential. -/
theorem vertexSubdivision_comm_d {ι : Type} [Fintype ι] (n : ℕ) :
    vertexSubdivision R (ι := ι) (n + 1) ≫
        (ConstructionTargets.CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)).d (n + 1) n =
      (ConstructionTargets.CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)).d (n + 1) n ≫ vertexSubdivision R n := by
  induction n with
  | zero =>
      apply Limits.Sigma.hom_ext
      intro v
      change (ConstructionTargets.CoefficientVertexCone.vertexGenerator R (stdSimplex ℝ ι) 1 v ≫ vertexSubdivision R 1) ≫
          (ConstructionTargets.CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)).d 1 0 =
        (ConstructionTargets.CoefficientVertexCone.vertexGenerator R (stdSimplex ℝ ι) 1 v ≫
          (ConstructionTargets.CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)).d 1 0) ≫ vertexSubdivision R 0
      rw [vertexGenerator_vertexSubdivision_succ R]
      simp only [vertexSubdivision, Category.assoc, Category.id_comp,
        Category.comp_id]
      rw [← Category.assoc]
      rw [ConstructionTargets.CoefficientVertexCone.vertexGenerator_boundary R]
      rw [Preadditive.sum_comp]
      rw [Fin.sum_univ_two]
      simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul,
        neg_smul]
      rw [Preadditive.neg_comp]
      simp only [← Category.assoc]
      rw [ConstructionTargets.CoefficientVertexCone.vertexGenerator_cone_zero_boundary R,
        ConstructionTargets.CoefficientVertexCone.vertexGenerator_cone_zero_boundary R]
      rw [Fin.sum_univ_two]
      simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul,
        neg_smul]
      abel
  | succ n ih =>
      apply Limits.Sigma.hom_ext
      intro v
      change (ConstructionTargets.CoefficientVertexCone.vertexGenerator R _ (n + 2) v ≫ vertexSubdivision R (n + 2)) ≫ _ =
        (ConstructionTargets.CoefficientVertexCone.vertexGenerator R _ (n + 2) v ≫ _) ≫ vertexSubdivision R (n + 1)
      rw [vertexGenerator_vertexSubdivision_succ R]
      simp only [Category.assoc]
      have hz : (ConstructionTargets.CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)).d (n + 2) (n + 1) ≫
          vertexSubdivision R (n + 1) ≫
          (ConstructionTargets.CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)).d (n + 1) n ≫
          ConstructionTargets.CoefficientVertexCone.vertexCone R _ (vertexBarycenter v) n = 0 := by
        rw [← Category.assoc
          (vertexSubdivision R (ι := ι) (n + 1))
          ((ConstructionTargets.CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)).d (n + 1) n)
          (ConstructionTargets.CoefficientVertexCone.vertexCone R _ (vertexBarycenter v) n)]
        rw [ih]
        simp only [← Category.assoc]
        rw [Category.assoc, HomologicalComplex.d_comp_d]
        simp
      have hz' : ConstructionTargets.CoefficientVertexCone.vertexGenerator R (stdSimplex ℝ ι) (n + 1 + 1) v ≫
          (ConstructionTargets.CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)).d (n + 1 + 1) (n + 1) ≫
          vertexSubdivision R (n + 1) ≫
          (ConstructionTargets.CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)).d (n + 1) n ≫
          ConstructionTargets.CoefficientVertexCone.vertexCone R _ (vertexBarycenter v) n = 0 := by
        rw [hz]
        simp
      rw [ConstructionTargets.CoefficientVertexCone.vertexCone_boundary R]
      simp only [Preadditive.comp_sub, Category.comp_id]
      simpa only [sub_zero] using congrArg
        (fun z ↦
          (ConstructionTargets.CoefficientVertexCone.vertexGenerator R (stdSimplex ℝ ι) (n + 1 + 1) v ≫
            (ConstructionTargets.CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)).d (n + 1 + 1) (n + 1) ≫
            vertexSubdivision R (n + 1)) - z) hz'


theorem vertexMapDegree_cone {V W : Type} (f : V → W) (b : V) (n : ℕ) :
    CoefficientAffineNaturality.vertexMapDegree R f n ≫ CoefficientVertexCone.vertexCone R W (f b) n =
      CoefficientVertexCone.vertexCone R V b n ≫ CoefficientAffineNaturality.vertexMapDegree R f (n + 1) := by
  apply Limits.Sigma.hom_ext
  intro v
  change (CoefficientVertexCone.vertexGenerator R V n v ≫ CoefficientAffineNaturality.vertexMapDegree R f n) ≫ _ =
    (CoefficientVertexCone.vertexGenerator R V n v ≫ CoefficientVertexCone.vertexCone R V b n) ≫ _
  rw [CoefficientAffineNaturality.vertexGenerator_vertexMapDegree R, CoefficientVertexCone.vertexGenerator_vertexCone R,
    CoefficientVertexCone.vertexGenerator_vertexCone R, CoefficientAffineNaturality.vertexGenerator_vertexMapDegree R]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl



theorem vertexSubdivision_natural {ι κ : Type} [Fintype ι] [Fintype κ]
    (f : stdSimplex ℝ ι → stdSimplex ℝ κ)
    (hb : ∀ (n : ℕ) (v : Fin (n + 1) → stdSimplex ℝ ι),
      f (vertexBarycenter v) = vertexBarycenter (f ∘ v)) (n : ℕ) :
    vertexSubdivision R (ι := ι) n ≫ CoefficientAffineNaturality.vertexMapDegree R f n =
      CoefficientAffineNaturality.vertexMapDegree R f n ≫ vertexSubdivision R (ι := κ) n := by
  induction n with
  | zero => simp [vertexSubdivision]
  | succ n ih =>
      apply Limits.Sigma.hom_ext
      intro v
      change (CoefficientVertexCone.vertexGenerator R (stdSimplex ℝ ι) (n + 1) v ≫
          vertexSubdivision R (n + 1)) ≫ _ =
        (CoefficientVertexCone.vertexGenerator R (stdSimplex ℝ ι) (n + 1) v ≫
          CoefficientAffineNaturality.vertexMapDegree R f (n + 1)) ≫ _
      rw [vertexGenerator_vertexSubdivision_succ R,
        CoefficientAffineNaturality.vertexGenerator_vertexMapDegree R, vertexGenerator_vertexSubdivision_succ R]
      simp only [← Category.assoc]
      rw [Category.assoc]
      rw [← vertexMapDegree_cone R]
      simp only [← Category.assoc]
      rw [show
        ((CoefficientVertexCone.vertexGenerator R (stdSimplex ℝ ι) (n + 1) v ≫
            (CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)).d (n + 1) n) ≫
              vertexSubdivision R n) ≫ CoefficientAffineNaturality.vertexMapDegree R f n =
          ((CoefficientVertexCone.vertexGenerator R (stdSimplex ℝ ι) (n + 1) v ≫
            (CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)).d (n + 1) n) ≫
              CoefficientAffineNaturality.vertexMapDegree R f n) ≫ vertexSubdivision R n by
            simp only [Category.assoc, ih]]
      rw [show
        (CoefficientVertexCone.vertexGenerator R (stdSimplex ℝ ι) (n + 1) v ≫
            (CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)).d (n + 1) n) ≫
              CoefficientAffineNaturality.vertexMapDegree R f n =
          (CoefficientVertexCone.vertexGenerator R (stdSimplex ℝ ι) (n + 1) v ≫
            CoefficientAffineNaturality.vertexMapDegree R f (n + 1)) ≫
              (CoefficientVertexCone.VertexChains R (stdSimplex ℝ κ)).d (n + 1) n by
            simp only [Category.assoc, CoefficientAffineNaturality.vertexMapDegree_comm_d R]]
      rw [CoefficientAffineNaturality.vertexGenerator_vertexMapDegree R]
      rw [hb (n + 1) v]

/-- Affine simplex maps commute with subdivision on ordered-vertex chains. -/
theorem vertexSubdivision_affine_natural {m : ℕ} {κ : Type} [Fintype κ]
    (u : Fin (m + 1) → stdSimplex ℝ κ) (n : ℕ) :
    vertexSubdivision R (ι := Fin (m + 1)) n ≫
        CoefficientAffineNaturality.vertexMapDegree R (affineSimplex u) n =
      CoefficientAffineNaturality.vertexMapDegree R (affineSimplex u) n ≫
        vertexSubdivision R (ι := κ) n := by
  apply vertexSubdivision_natural R (ι := Fin (m + 1)) (κ := κ)
  intro q v
  exact affineSimplex_vertexBarycenter u v



@[reassoc] theorem singularPostcomposition_comp {X Y Z : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) :
    CoefficientH0.singularPostcomposition R f ≫ CoefficientH0.singularPostcomposition R g =
      CoefficientH0.singularPostcomposition R (g.comp f) := by
  dsimp [CoefficientH0.singularPostcomposition]
  rw [← Functor.map_comp]

@[reassoc] theorem subdividedFace_transport {X : Type} [TopologicalSpace X] (n : ℕ)
    (σ : C(stdSimplex ℝ (Fin (n + 2)), X)) (i : Fin (n + 2)) :
    CoefficientVertexCone.vertexGenerator R _ n
          (standardSimplexVertices (n + 1) ∘ i.succAbove) ≫
        vertexSubdivision R n ≫ CoefficientAffineRealization.vertexRealizationDegree R n ≫
        (CoefficientH0.singularPostcomposition R σ).f n =
      CoefficientVertexCone.vertexGenerator R _ n (standardSimplexVertices n) ≫
        vertexSubdivision R n ≫ CoefficientAffineRealization.vertexRealizationDegree R n ≫
        (CoefficientH0.singularPostcomposition R (σ.comp (faceAffine n i))).f n := by
  rw [← faceAffine_standardSimplexVertices]
  rw [← CoefficientAffineNaturality.vertexGenerator_vertexMapDegree R]
  unfold faceAffine
  simp only [← Category.assoc]
  rw [show
    (CoefficientVertexCone.vertexGenerator R _ n (standardSimplexVertices n) ≫
        CoefficientAffineNaturality.vertexMapDegree R (affineSimplex
          (fun j => standardSimplexVertices (n + 1) (i.succAbove j))) n) ≫
        vertexSubdivision R n =
      (CoefficientVertexCone.vertexGenerator R _ n (standardSimplexVertices n) ≫
        vertexSubdivision R n) ≫
        CoefficientAffineNaturality.vertexMapDegree R (affineSimplex
          (fun j => standardSimplexVertices (n + 1) (i.succAbove j))) n by
      simp only [Category.assoc, vertexSubdivision_affine_natural R]]
  simp only [Category.assoc]
  simp only [← Category.assoc]
  rw [show
    ((CoefficientVertexCone.vertexGenerator R _ n (standardSimplexVertices n) ≫ vertexSubdivision R n) ≫
        CoefficientAffineNaturality.vertexMapDegree R (affineSimplex
          (fun j => standardSimplexVertices (n + 1) (i.succAbove j))) n) ≫
        CoefficientAffineRealization.vertexRealizationDegree R n =
      ((CoefficientVertexCone.vertexGenerator R _ n (standardSimplexVertices n) ≫ vertexSubdivision R n) ≫
        CoefficientAffineRealization.vertexRealizationDegree R n) ≫
        (CoefficientH0.singularPostcomposition R (affineSimplex
          (fun j => standardSimplexVertices (n + 1) (i.succAbove j)))).f n by
      simp only [Category.assoc, CoefficientAffineNaturality.vertexRealization_affine_natural R]]
  rw [Category.assoc]
  rw [← HomologicalComplex.comp_f, singularPostcomposition_comp]



def degree {X : Type} [TopologicalSpace X] (n : ℕ) :
    (ConstructionTargets.CoefficientH0.SingularChains R (TopCat.of X)).X n ⟶
    (ConstructionTargets.CoefficientH0.SingularChains R (TopCat.of X)).X n := by
  change (∐ fun _ : SingularSimplex (TopCat.of X) n ↦ ModuleCat.of R R) ⟶ _
  exact Limits.Sigma.desc fun s =>
    ConstructionTargets.CoefficientVertexCone.vertexGenerator R _ n (standardSimplexVertices n) ≫
    vertexSubdivision R n ≫
    ConstructionTargets.CoefficientAffineRealization.vertexRealizationDegree R n ≫
    (ConstructionTargets.CoefficientH0.singularPostcomposition R (continuousMapOfSingularSimplex n s)).f n

@[simp] theorem generator_degree {X : Type} [TopologicalSpace X] (n : ℕ)
    (σ : SingularSimplex (TopCat.of X) n) :
    CoefficientH0.singularGenerator R (TopCat.of X) n σ ≫ degree R n =
      CoefficientVertexCone.vertexGenerator R _ n (standardSimplexVertices n) ≫
        vertexSubdivision R n ≫ CoefficientAffineRealization.vertexRealizationDegree R n ≫
        (CoefficientH0.singularPostcomposition R (continuousMapOfSingularSimplex n σ)).f n := by
  dsimp [CoefficientH0.singularGenerator, degree]
  exact Limits.Sigma.ι_desc _ σ

theorem actual_subdivided_face {X : Type} [TopologicalSpace X] (n : ℕ)
    (σ : C(stdSimplex ℝ (Fin (n+2)), X)) (i : Fin (n+2)) :
    CoefficientVertexCone.vertexGenerator R _ n
      (standardSimplexVertices (n+1) ∘ i.succAbove) ≫
      vertexSubdivision R n ≫ CoefficientAffineRealization.vertexRealizationDegree R n ≫
      (CoefficientH0.singularPostcomposition R σ).f n =
    CoefficientH0.singularGenerator R (TopCat.of X) n
      ((TopCat.toSSet.obj (TopCat.of X)).δ i
        (singularSimplexOfContinuousMap (TopCat.of X) (n+1) σ)) ≫ degree R n := by
  rw [singularSimplexOfContinuousMap_face, generator_degree]
  simp only [continuousMapOfSingularSimplex_ofContinuousMap]
  exact subdividedFace_transport R n σ i

theorem integral_edge_face (i : Fin 2) :
    CoefficientVertexCone.vertexGenerator ℤ _ 0
      (standardSimplexVertices 1 ∘ i.succAbove) ≫
      vertexSubdivision ℤ 0 ≫ CoefficientAffineRealization.vertexRealizationDegree ℤ 0 ≫
      (CoefficientH0.singularPostcomposition ℤ
        (ContinuousMap.id (stdSimplex ℝ (Fin 2)))).f 0 =
    CoefficientH0.singularGenerator ℤ (TopCat.of (stdSimplex ℝ (Fin 2))) 0
      ((TopCat.toSSet.obj (TopCat.of (stdSimplex ℝ (Fin 2)))).δ i
        (singularSimplexOfContinuousMap (TopCat.of (stdSimplex ℝ (Fin 2))) 1
          (ContinuousMap.id (stdSimplex ℝ (Fin 2))))) ≫ degree ℤ 0 :=
  actual_subdivided_face ℤ 0 (ContinuousMap.id (stdSimplex ℝ (Fin 2))) i

theorem rational_edge_face (i : Fin 2) :
    CoefficientVertexCone.vertexGenerator ℚ _ 0
      (standardSimplexVertices 1 ∘ i.succAbove) ≫
      vertexSubdivision ℚ 0 ≫ CoefficientAffineRealization.vertexRealizationDegree ℚ 0 ≫
      (CoefficientH0.singularPostcomposition ℚ
        (ContinuousMap.id (stdSimplex ℝ (Fin 2)))).f 0 =
    CoefficientH0.singularGenerator ℚ (TopCat.of (stdSimplex ℝ (Fin 2))) 0
      ((TopCat.toSSet.obj (TopCat.of (stdSimplex ℝ (Fin 2)))).δ i
        (singularSimplexOfContinuousMap (TopCat.of (stdSimplex ℝ (Fin 2))) 1
          (ContinuousMap.id (stdSimplex ℝ (Fin 2))))) ≫ degree ℚ 0 :=
  actual_subdivided_face ℚ 0 (ContinuousMap.id (stdSimplex ℝ (Fin 2))) i

#print axioms vertexSubdivision_comm_d
#print axioms vertexMapDegree_cone
#print axioms vertexSubdivision_natural
#print axioms vertexSubdivision_affine_natural
#print axioms subdividedFace_transport
#print axioms actual_subdivided_face
#print axioms integral_edge_face
#print axioms rational_edge_face
end ConstructionTargets.CoefficientBarycentricNaturality
