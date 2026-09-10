import ConstructionTargets.CoefficientBarycentricNaturality
noncomputable section
namespace ConstructionTargets.CoefficientSingularSubdivision
open CategoryTheory CategoryTheory.Limits Simplicial SingularSubdivision
variable (R : Type) [CommRing R]
theorem singularSubdivisionDegree_comm_d {X : Type} [TopologicalSpace X]
    (n : ℕ) :
    CoefficientBarycentricNaturality.degree R (X := X) (n + 1) ≫
        (CoefficientH0.SingularChains R (TopCat.of X)).d (n + 1) n =
      (CoefficientH0.SingularChains R (TopCat.of X)).d (n + 1) n ≫
        CoefficientBarycentricNaturality.degree R n := by
  apply Limits.Sigma.hom_ext
  intro s
  let σ := continuousMapOfSingularSimplex (n + 1) s
  have hs : singularSimplexOfContinuousMap (TopCat.of X) (n + 1) σ = s :=
    (TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋n + 1⦌)).symm_apply_apply s
  change (CoefficientH0.singularGenerator R (TopCat.of X) (n + 1) s ≫
      CoefficientBarycentricNaturality.degree R (n + 1)) ≫ _ =
    (CoefficientH0.singularGenerator R (TopCat.of X) (n + 1) s ≫ _) ≫
      CoefficientBarycentricNaturality.degree R n
  rw [← hs, CoefficientBarycentricNaturality.generator_degree R]
  simp only [continuousMapOfSingularSimplex_ofContinuousMap, Category.assoc]
  rw [(CoefficientH0.singularPostcomposition R σ).comm]
  slice_lhs 3 4 =>
    change (CoefficientAffineRealization.vertexRealization R (ι := Fin (n + 1 + 1))).f (n + 1) ≫ _
    rw [(CoefficientAffineRealization.vertexRealization R (ι := Fin (n + 1 + 1))).comm]
  slice_lhs 2 3 => rw [CoefficientBarycentricNaturality.vertexSubdivision_comm_d R]
  simp only [← Category.assoc]
  rw [CoefficientVertexCone.vertexGenerator_boundary R, Preadditive.sum_comp]
  simp_rw [Preadditive.zsmul_comp]
  rw [CoefficientH0.singularGenerator_boundary R, Preadditive.sum_comp]
  simp only [Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [Preadditive.zsmul_comp]
  rw [singularSimplexOfContinuousMap_face]
  slice_rhs 1 2 => rw [Preadditive.zsmul_comp]
  rw [CoefficientBarycentricNaturality.generator_degree R]
  simp only [continuousMapOfSingularSimplex_ofContinuousMap,
    Preadditive.zsmul_comp]
  congr 1
  exact CoefficientBarycentricNaturality.subdividedFace_transport R n σ i

def singularSubdivision {X : Type} [TopologicalSpace X] :
    CoefficientH0.SingularChains R (TopCat.of X) ⟶ CoefficientH0.SingularChains R (TopCat.of X) where
  f := CoefficientBarycentricNaturality.degree R
  comm' i j h := by
    obtain rfl := h
    exact singularSubdivisionDegree_comm_d R j


theorem singularSubdivision_natural {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ) :
    (CoefficientH0.singularPostcomposition R f).f n ≫ CoefficientBarycentricNaturality.degree R n =
      CoefficientBarycentricNaturality.degree R n ≫ (CoefficientH0.singularPostcomposition R f).f n := by
  apply Limits.Sigma.hom_ext
  intro s
  let σ := continuousMapOfSingularSimplex n s
  have hs : singularSimplexOfContinuousMap (TopCat.of X) n σ = s :=
    (TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋n⦌)).symm_apply_apply s
  rw [← hs]
  change (CoefficientH0.singularGenerator R (TopCat.of X) n
    (singularSimplexOfContinuousMap (TopCat.of X) n σ) ≫
      (CoefficientH0.singularPostcomposition R f).f n) ≫ _ = _
  rw [CoefficientH0.singularGenerator_singularPostcomposition R]
  rw [CoefficientBarycentricNaturality.generator_degree R]
  simp only [continuousMapOfSingularSimplex_ofContinuousMap]
  change _ = (CoefficientH0.singularGenerator R (TopCat.of X) n
    (singularSimplexOfContinuousMap (TopCat.of X) n σ) ≫
      CoefficientBarycentricNaturality.degree R n) ≫ _
  rw [CoefficientBarycentricNaturality.generator_degree R]
  simp only [continuousMapOfSingularSimplex_ofContinuousMap]
  have hcomp := congrArg (fun q => q.f n)
    (CoefficientBarycentricNaturality.singularPostcomposition_comp R σ f)
  change (CoefficientH0.singularPostcomposition R σ).f n ≫
    (CoefficientH0.singularPostcomposition R f).f n =
      (CoefficientH0.singularPostcomposition R (f.comp σ)).f n at hcomp
  simp only [Category.assoc]
  rw [hcomp]


theorem standardVertexRealization_postcomposition
    {X : Type} [TopologicalSpace X] (n : ℕ)
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    CoefficientVertexCone.vertexGenerator R _ n (standardSimplexVertices n) ≫
        CoefficientAffineRealization.vertexRealizationDegree R n ≫ (CoefficientH0.singularPostcomposition R σ).f n =
      CoefficientH0.singularGenerator R (TopCat.of X) n
        (singularSimplexOfContinuousMap (TopCat.of X) n σ) := by
  simp only [← Category.assoc]
  rw [CoefficientAffineRealization.vertexGenerator_vertexRealizationDegree R]
  dsimp [CoefficientAffineRealization.affineGenerator]
  rw [CoefficientH0.singularGenerator_singularPostcomposition R]
  rw [affineSimplex_standardSimplexVertices]
  rfl
theorem singularSubdivisionDegree_zero
    {X : Type} [TopologicalSpace X] :
    CoefficientBarycentricNaturality.degree R (X := X) 0 = 𝟙 _ := by
  apply Limits.Sigma.hom_ext
  intro s
  change CoefficientH0.singularGenerator R (TopCat.of X) 0 s ≫ CoefficientBarycentricNaturality.degree R 0 =
    CoefficientH0.singularGenerator R (TopCat.of X) 0 s ≫ 𝟙 _
  rw [CoefficientBarycentricNaturality.generator_degree R]
  slice_lhs 1 2 => rw [CoefficientBarycentricNaturality.vertexGenerator_vertexSubdivision_zero R]
  rw [Category.assoc]
  rw [standardVertexRealization_postcomposition]
  have hs : singularSimplexOfContinuousMap (TopCat.of X) 0
      (continuousMapOfSingularSimplex 0 s) = s :=
    (TopCat.toSSetObjEquiv (TopCat.of X)
      (Opposite.op ⦋0⦌)).symm_apply_apply s
  rw [hs]
  rw [Category.comp_id]



theorem naturality {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) :
    CoefficientH0.singularPostcomposition R f ≫ singularSubdivision R =
      singularSubdivision R ≫ CoefficientH0.singularPostcomposition R f := by
  ext n : 1
  exact singularSubdivision_natural R f n

theorem generator_formula {X : Type} [TopologicalSpace X] (n : ℕ)
    (s : SingularSimplex (TopCat.of X) n) :
    CoefficientH0.singularGenerator R _ n s ≫ (singularSubdivision R).f n =
      CoefficientVertexCone.vertexGenerator R _ n (standardSimplexVertices n) ≫
        CoefficientBarycentricNaturality.vertexSubdivision R n ≫
        CoefficientAffineRealization.vertexRealizationDegree R n ≫
        (CoefficientH0.singularPostcomposition R (continuousMapOfSingularSimplex n s)).f n :=
  CoefficientBarycentricNaturality.generator_degree R n s

theorem edge_formula {X : Type} [TopologicalSpace X]
    (σ : C(stdSimplex ℝ (Fin 2), X)) :
    CoefficientH0.singularGenerator R _ 1 (singularSimplexOfContinuousMap _ 1 σ) ≫
      (singularSubdivision R).f 1 =
    (CoefficientAffineRealization.affineGenerator R
      (prependVertex (vertexBarycenter (standardSimplexVertices 1))
        (standardSimplexVertices 1 ∘ (0 : Fin 2).succAbove)) -
     CoefficientAffineRealization.affineGenerator R
      (prependVertex (vertexBarycenter (standardSimplexVertices 1))
        (standardSimplexVertices 1 ∘ (1 : Fin 2).succAbove))) ≫
      (CoefficientH0.singularPostcomposition R σ).f 1 := by
  rw [generator_formula]
  simp only [continuousMapOfSingularSimplex_ofContinuousMap, ← Category.assoc]
  rw [CoefficientBarycentricNaturality.vertexGenerator_vertexSubdivision_succ]
  simp only [← Category.assoc]
  rw [CoefficientVertexCone.vertexGenerator_boundary]
  simp only [Nat.reduceAdd, Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    one_smul, neg_smul, Preadditive.add_comp, Preadditive.neg_comp,
    CoefficientBarycentricNaturality.vertexSubdivision, Category.comp_id]
  simp only [CoefficientVertexCone.vertexGenerator_vertexCone,
    CoefficientAffineRealization.vertexGenerator_vertexRealizationDegree, sub_eq_add_neg,
    Preadditive.add_comp, Preadditive.neg_comp]

theorem edge_boundary {X : Type} [TopologicalSpace X]
    (σ : C(stdSimplex ℝ (Fin 2), X)) :
    (CoefficientH0.singularGenerator R _ 1 (singularSimplexOfContinuousMap _ 1 σ) ≫
      (singularSubdivision R).f 1) ≫
      (CoefficientH0.SingularChains R (TopCat.of X)).d 1 0 =
    CoefficientH0.singularGenerator R _ 0
      ((TopCat.toSSet.obj (TopCat.of X)).δ 0 (singularSimplexOfContinuousMap _ 1 σ)) -
    CoefficientH0.singularGenerator R _ 0
      ((TopCat.toSSet.obj (TopCat.of X)).δ 1 (singularSimplexOfContinuousMap _ 1 σ)) := by
  rw [Category.assoc, (singularSubdivision R).comm]
  change _ ≫ _ ≫ CoefficientBarycentricNaturality.degree R 0 = _
  rw [singularSubdivisionDegree_zero, Category.comp_id, CoefficientH0.singularGenerator_boundary]
  simp [Fin.sum_univ_two, sub_eq_add_neg]


theorem integral_edge_formula :
    CoefficientH0.singularGenerator ℤ _ 1 (singularSimplexOfContinuousMap _ 1 (ContinuousMap.id (stdSimplex ℝ (Fin 2)))) ≫
      (singularSubdivision ℤ).f 1 =
    (CoefficientAffineRealization.affineGenerator ℤ
      (prependVertex (vertexBarycenter (standardSimplexVertices 1))
        (standardSimplexVertices 1 ∘ (0 : Fin 2).succAbove)) -
     CoefficientAffineRealization.affineGenerator ℤ
      (prependVertex (vertexBarycenter (standardSimplexVertices 1))
        (standardSimplexVertices 1 ∘ (1 : Fin 2).succAbove))) ≫
      (CoefficientH0.singularPostcomposition ℤ (ContinuousMap.id (stdSimplex ℝ (Fin 2)))).f 1 :=
  edge_formula ℤ (ContinuousMap.id (stdSimplex ℝ (Fin 2)))

theorem integral_edge_boundary :
    (CoefficientH0.singularGenerator ℤ _ 1 (singularSimplexOfContinuousMap _ 1 (ContinuousMap.id (stdSimplex ℝ (Fin 2)))) ≫
      (singularSubdivision ℤ).f 1) ≫
      (CoefficientH0.SingularChains ℤ (TopCat.of (stdSimplex ℝ (Fin 2)))).d 1 0 =
    CoefficientH0.singularGenerator ℤ _ 0
      ((TopCat.toSSet.obj (TopCat.of (stdSimplex ℝ (Fin 2)))).δ 0 (singularSimplexOfContinuousMap _ 1 (ContinuousMap.id (stdSimplex ℝ (Fin 2))))) -
    CoefficientH0.singularGenerator ℤ _ 0
      ((TopCat.toSSet.obj (TopCat.of (stdSimplex ℝ (Fin 2)))).δ 1 (singularSimplexOfContinuousMap _ 1 (ContinuousMap.id (stdSimplex ℝ (Fin 2))))) :=
  edge_boundary ℤ (ContinuousMap.id (stdSimplex ℝ (Fin 2)))

theorem rational_edge_formula :
    CoefficientH0.singularGenerator ℚ _ 1 (singularSimplexOfContinuousMap _ 1 (ContinuousMap.id (stdSimplex ℝ (Fin 2)))) ≫
      (singularSubdivision ℚ).f 1 =
    (CoefficientAffineRealization.affineGenerator ℚ
      (prependVertex (vertexBarycenter (standardSimplexVertices 1))
        (standardSimplexVertices 1 ∘ (0 : Fin 2).succAbove)) -
     CoefficientAffineRealization.affineGenerator ℚ
      (prependVertex (vertexBarycenter (standardSimplexVertices 1))
        (standardSimplexVertices 1 ∘ (1 : Fin 2).succAbove))) ≫
      (CoefficientH0.singularPostcomposition ℚ (ContinuousMap.id (stdSimplex ℝ (Fin 2)))).f 1 :=
  edge_formula ℚ (ContinuousMap.id (stdSimplex ℝ (Fin 2)))

theorem rational_edge_boundary :
    (CoefficientH0.singularGenerator ℚ _ 1 (singularSimplexOfContinuousMap _ 1 (ContinuousMap.id (stdSimplex ℝ (Fin 2)))) ≫
      (singularSubdivision ℚ).f 1) ≫
      (CoefficientH0.SingularChains ℚ (TopCat.of (stdSimplex ℝ (Fin 2)))).d 1 0 =
    CoefficientH0.singularGenerator ℚ _ 0
      ((TopCat.toSSet.obj (TopCat.of (stdSimplex ℝ (Fin 2)))).δ 0 (singularSimplexOfContinuousMap _ 1 (ContinuousMap.id (stdSimplex ℝ (Fin 2))))) -
    CoefficientH0.singularGenerator ℚ _ 0
      ((TopCat.toSSet.obj (TopCat.of (stdSimplex ℝ (Fin 2)))).δ 1 (singularSimplexOfContinuousMap _ 1 (ContinuousMap.id (stdSimplex ℝ (Fin 2))))) :=
  edge_boundary ℚ (ContinuousMap.id (stdSimplex ℝ (Fin 2)))

#print axioms singularSubdivision
#print axioms singularSubdivisionDegree_comm_d
#print axioms singularSubdivisionDegree_zero
#print axioms naturality
#print axioms generator_formula
#print axioms edge_formula
#print axioms edge_boundary
#print axioms integral_edge_formula
#print axioms integral_edge_boundary
#print axioms rational_edge_formula
#print axioms rational_edge_boundary
end ConstructionTargets.CoefficientSingularSubdivision
