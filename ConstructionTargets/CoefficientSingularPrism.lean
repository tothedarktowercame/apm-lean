import ConstructionTargets.CoefficientVertexPrism
noncomputable section
namespace ConstructionTargets.CoefficientSingularPrism
open CategoryTheory CategoryTheory.Limits Simplicial SingularSubdivision
variable (R : Type) [CommRing R]
def singularPrismDegree {X : Type} [TopologicalSpace X] (n : ℕ) :
    (CoefficientH0.SingularChains R (TopCat.of X)).X n ⟶ (CoefficientH0.SingularChains R (TopCat.of X)).X (n + 1) := by
  change (∐ fun _ : SingularSimplex (TopCat.of X) n ↦ ModuleCat.of R R) ⟶ _
  exact Limits.Sigma.desc fun σ =>
    CoefficientVertexCone.vertexGenerator R _ n (standardSimplexVertices n) ≫ CoefficientVertexPrism.vertexPrism R n ≫
      CoefficientAffineRealization.vertexRealizationDegree R (n + 1) ≫
      (CoefficientH0.singularPostcomposition R (continuousMapOfSingularSimplex n σ)).f (n + 1)

@[simp, reassoc] theorem singularGenerator_singularPrismDegree
    {X : Type} [TopologicalSpace X] (n : ℕ)
    (σ : SingularSimplex (TopCat.of X) n) :
    CoefficientH0.singularGenerator R (TopCat.of X) n σ ≫ singularPrismDegree R n =
      CoefficientVertexCone.vertexGenerator R _ n (standardSimplexVertices n) ≫ CoefficientVertexPrism.vertexPrism R n ≫
        CoefficientAffineRealization.vertexRealizationDegree R (n + 1) ≫
        (CoefficientH0.singularPostcomposition R (continuousMapOfSingularSimplex n σ)).f (n + 1) := by
  dsimp [CoefficientH0.singularGenerator, singularPrismDegree]
  exact Limits.Sigma.ι_desc _ σ

theorem prismFace_transport {X : Type} [TopologicalSpace X] (n : ℕ)
    (σ : C(stdSimplex ℝ (Fin (n + 2)), X)) (i : Fin (n + 2)) :
    CoefficientVertexCone.vertexGenerator R _ n
          (standardSimplexVertices (n + 1) ∘ i.succAbove) ≫
        CoefficientVertexPrism.vertexPrism R n ≫ CoefficientAffineRealization.vertexRealizationDegree R (n + 1) ≫
        (CoefficientH0.singularPostcomposition R σ).f (n + 1) =
      CoefficientVertexCone.vertexGenerator R _ n (standardSimplexVertices n) ≫
        CoefficientVertexPrism.vertexPrism R n ≫ CoefficientAffineRealization.vertexRealizationDegree R (n + 1) ≫
        (CoefficientH0.singularPostcomposition R (σ.comp (faceAffine n i))).f (n + 1) := by
  rw [← faceAffine_standardSimplexVertices]
  rw [← CoefficientAffineNaturality.vertexGenerator_vertexMapDegree R]
  unfold faceAffine
  simp only [← Category.assoc]
  slice_lhs 2 3 => rw [← CoefficientVertexPrism.vertexPrism_affine_natural R]
  slice_lhs 3 4 => rw [← CoefficientAffineNaturality.vertexRealization_affine_natural R]
  slice_lhs 4 5 =>
    rw [← HomologicalComplex.comp_f, CoefficientBarycentricNaturality.singularPostcomposition_comp]
  simp only [Category.assoc]

def singularPrismCorrection {X : Type} [TopologicalSpace X] (n : ℕ) :
    (CoefficientH0.SingularChains R (TopCat.of X)).X n ⟶
      (CoefficientH0.SingularChains R (TopCat.of X)).X n :=
  match n with
  | 0 => 0
  | n + 1 => (CoefficientH0.SingularChains R (TopCat.of X)).d (n + 1) n ≫
      singularPrismDegree R n

theorem singularGenerator_prismCorrection_succ
    {X : Type} [TopologicalSpace X] (n : ℕ)
    (σ : C(stdSimplex ℝ (Fin (n + 2)), X)) :
    CoefficientH0.singularGenerator R (TopCat.of X) (n + 1)
          (singularSimplexOfContinuousMap (TopCat.of X) (n + 1) σ) ≫
        singularPrismCorrection R (n + 1) =
      CoefficientVertexCone.vertexGenerator R _ (n + 1) (standardSimplexVertices (n + 1)) ≫
        CoefficientVertexPrism.vertexPrismCorrection R (n + 1) ≫ CoefficientAffineRealization.vertexRealizationDegree R (n + 1) ≫
        (CoefficientH0.singularPostcomposition R σ).f (n + 1) := by
  change CoefficientH0.singularGenerator R _ _ _ ≫
      ((CoefficientH0.SingularChains R (TopCat.of X)).d (n + 1) n ≫ singularPrismDegree R n) = _
  rw [show CoefficientVertexPrism.vertexPrismCorrection R (ι := Fin (n + 2)) (n + 1) =
    (CoefficientVertexCone.VertexChains R (stdSimplex ℝ (Fin (n + 2)))).d (n + 1) n ≫
      CoefficientVertexPrism.vertexPrism R n from rfl]
  simp only [← Category.assoc]
  rw [CoefficientH0.singularGenerator_boundary, Preadditive.sum_comp]
  rw [CoefficientVertexCone.vertexGenerator_boundary, Preadditive.sum_comp]
  rw [Preadditive.sum_comp, Preadditive.sum_comp]
  simp_rw [Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [singularSimplexOfContinuousMap_face]
  rw [singularGenerator_singularPrismDegree]
  simp only [continuousMapOfSingularSimplex_ofContinuousMap]
  exact (prismFace_transport R n σ i).symm

theorem singularGenerator_prism_boundary
    {X : Type} [TopologicalSpace X] (n : ℕ)
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    CoefficientH0.singularGenerator R (TopCat.of X) n
          (singularSimplexOfContinuousMap (TopCat.of X) n σ) ≫
        singularPrismDegree R n ≫
        (CoefficientH0.SingularChains R (TopCat.of X)).d (n + 1) n =
      CoefficientVertexCone.vertexGenerator R _ n (standardSimplexVertices n) ≫ CoefficientVertexPrism.vertexPrism R n ≫
        (CoefficientVertexCone.VertexChains R (stdSimplex ℝ (Fin (n + 1)))).d (n + 1) n ≫
        CoefficientAffineRealization.vertexRealizationDegree R n ≫ (CoefficientH0.singularPostcomposition R σ).f n := by
  simp only [← Category.assoc]
  rw [singularGenerator_singularPrismDegree]
  simp only [continuousMapOfSingularSimplex_ofContinuousMap, Category.assoc]
  rw [(CoefficientH0.singularPostcomposition R σ).comm]
  slice_lhs 3 4 =>
    change (CoefficientAffineRealization.vertexRealization R (ι := Fin (n + 1))).f (n + 1) ≫ _
    rw [(CoefficientAffineRealization.vertexRealization R (ι := Fin (n + 1))).comm]
  simp only [CoefficientAffineRealization.vertexRealization, Category.assoc]

theorem singularGenerator_prismCorrection
    {X : Type} [TopologicalSpace X] (n : ℕ)
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    CoefficientH0.singularGenerator R (TopCat.of X) n
          (singularSimplexOfContinuousMap (TopCat.of X) n σ) ≫
        singularPrismCorrection R n =
      CoefficientVertexCone.vertexGenerator R _ n (standardSimplexVertices n) ≫
        CoefficientVertexPrism.vertexPrismCorrection R n ≫ CoefficientAffineRealization.vertexRealizationDegree R n ≫
        (CoefficientH0.singularPostcomposition R σ).f n := by
  cases n with
  | zero => simp [singularPrismCorrection, CoefficientVertexPrism.vertexPrismCorrection]
  | succ n => exact singularGenerator_prismCorrection_succ R n σ

theorem singularPrism_identity {X : Type} [TopologicalSpace X] (n : ℕ) :
    singularPrismDegree R (X := X) n ≫
        (CoefficientH0.SingularChains R (TopCat.of X)).d (n + 1) n +
      singularPrismCorrection R n = CoefficientBarycentricNaturality.degree R n - 𝟙 _ := by
  apply Limits.Sigma.hom_ext
  intro s
  let σ := continuousMapOfSingularSimplex n s
  have hs : singularSimplexOfContinuousMap (TopCat.of X) n σ = s :=
    (TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋n⦌)).symm_apply_apply s
  rw [← hs]
  change CoefficientH0.singularGenerator R (TopCat.of X) n
      (singularSimplexOfContinuousMap (TopCat.of X) n σ) ≫
        (_ + _) = CoefficientH0.singularGenerator R (TopCat.of X) n
      (singularSimplexOfContinuousMap (TopCat.of X) n σ) ≫ (_ - _)
  rw [Preadditive.comp_add, Preadditive.comp_sub, Category.comp_id]
  rw [singularGenerator_prism_boundary R]
  rw [singularGenerator_prismCorrection R]
  rw [CoefficientBarycentricNaturality.generator_degree]
  simp only [continuousMapOfSingularSimplex_ofContinuousMap]
  rw [← CoefficientSingularSubdivision.standardVertexRealization_postcomposition R]
  have h := CoefficientVertexPrism.vertexPrism_identity R (ι := Fin (n + 1)) n
  apply_fun (fun f => CoefficientVertexCone.vertexGenerator R _ n (standardSimplexVertices n) ≫
    f ≫ CoefficientAffineRealization.vertexRealizationDegree R n ≫ (CoefficientH0.singularPostcomposition R σ).f n) at h
  simpa only [Preadditive.comp_add, Preadditive.comp_sub,
    Preadditive.add_comp, Preadditive.sub_comp, Category.comp_id,
    Category.id_comp, Category.assoc] using h

/-- All types here are in universe zero; the sign is subdivision minus identity. -/
def prismComponents {X : Type} [TopologicalSpace X] (i j : ℕ) :
    (CoefficientH0.SingularChains R (TopCat.of X)).X i ⟶
      (CoefficientH0.SingularChains R (TopCat.of X)).X j :=
  if h : i + 1 = j then singularPrismDegree R i ≫ eqToHom (congrArg _ h) else 0

@[simp] theorem prismComponents_succ {X : Type} [TopologicalSpace X] (i : ℕ) :
    prismComponents R (X := X) i (i+1) = singularPrismDegree R i := by
  simp [prismComponents]

/-- The positive prism satisfies dT + Td = subdivision - identity. -/
def subdivisionHomotopy {X : Type} [TopologicalSpace X] :
    Homotopy (CoefficientSingularSubdivision.singularSubdivision R (X := X)) (𝟙 _) where
  hom := prismComponents R
  zero i j h := by
    have hij : i + 1 ≠ j := by simpa using h
    simp [prismComponents, hij]
  comm n := by
    rw [Homotopy.prevD_chainComplex]
    rw [prismComponents_succ]
    cases n with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, zero_add]
      have h := singularPrism_identity R (X := X) 0
      simp only [singularPrismCorrection, add_zero] at h
      exact (sub_eq_iff_eq_add.mp h.symm)
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex, prismComponents_succ]
      have h := singularPrism_identity R (X := X) (n+1)
      change _ + (CoefficientH0.SingularChains R (TopCat.of X)).d (n+1) n ≫
        singularPrismDegree R n = _ at h
      change CoefficientBarycentricNaturality.degree R (n+1) = _ + 𝟙 _
      simpa only [add_comm] using (sub_eq_iff_eq_add.mp h.symm)


theorem actual_prism_face {X : Type} [TopologicalSpace X] (n : ℕ)
    (σ : C(stdSimplex ℝ (Fin (n+2)), X)) (i : Fin (n+2)) :
    CoefficientVertexCone.vertexGenerator R _ n
      (standardSimplexVertices (n+1) ∘ i.succAbove) ≫
      CoefficientVertexPrism.vertexPrism R n ≫
      CoefficientAffineRealization.vertexRealizationDegree R (n+1) ≫
      (CoefficientH0.singularPostcomposition R σ).f (n+1) =
    CoefficientH0.singularGenerator R (TopCat.of X) n
      ((TopCat.toSSet.obj (TopCat.of X)).δ i
        (singularSimplexOfContinuousMap (TopCat.of X) (n+1) σ)) ≫
      singularPrismDegree R n := by
  rw [singularSimplexOfContinuousMap_face, singularGenerator_singularPrismDegree]
  simp only [continuousMapOfSingularSimplex_ofContinuousMap]
  exact prismFace_transport R n σ i

theorem degree_zero {X : Type} [TopologicalSpace X] :
    singularPrismDegree R (X := X) 0 ≫
      (CoefficientH0.SingularChains R (TopCat.of X)).d 1 0 =
      (CoefficientSingularSubdivision.singularSubdivision R).f 0 - 𝟙 _ := by
  simpa only [singularPrismCorrection, add_zero] using singularPrism_identity R (X := X) 0

theorem standard_edge_equation :
    CoefficientH0.singularGenerator R _ 1
      (singularSimplexOfContinuousMap _ 1 (ContinuousMap.id (stdSimplex ℝ (Fin 2)))) ≫
      (singularPrismDegree R 1 ≫
        (CoefficientH0.SingularChains R (TopCat.of (stdSimplex ℝ (Fin 2)))).d 2 1 +
       (CoefficientH0.SingularChains R (TopCat.of (stdSimplex ℝ (Fin 2)))).d 1 0 ≫
        singularPrismDegree R 0) =
    CoefficientH0.singularGenerator R _ 1
      (singularSimplexOfContinuousMap _ 1 (ContinuousMap.id (stdSimplex ℝ (Fin 2)))) ≫
      ((CoefficientSingularSubdivision.singularSubdivision R).f 1 - 𝟙 _) := by
  change CoefficientH0.singularGenerator R _ 1 _ ≫
    (singularPrismDegree R 1 ≫ _ + singularPrismCorrection R 1) = _
  rw [singularPrism_identity]
  rfl


theorem integral_standard_edge :
    CoefficientH0.singularGenerator ℤ _ 1
      (singularSimplexOfContinuousMap _ 1 (ContinuousMap.id (stdSimplex ℝ (Fin 2)))) ≫
      (singularPrismDegree ℤ 1 ≫
        (CoefficientH0.SingularChains ℤ (TopCat.of (stdSimplex ℝ (Fin 2)))).d 2 1 +
       (CoefficientH0.SingularChains ℤ (TopCat.of (stdSimplex ℝ (Fin 2)))).d 1 0 ≫
        singularPrismDegree ℤ 0) =
    CoefficientH0.singularGenerator ℤ _ 1
      (singularSimplexOfContinuousMap _ 1 (ContinuousMap.id (stdSimplex ℝ (Fin 2)))) ≫
      ((CoefficientSingularSubdivision.singularSubdivision ℤ).f 1 - 𝟙 _) := standard_edge_equation ℤ

theorem rational_standard_edge :
    CoefficientH0.singularGenerator ℚ _ 1
      (singularSimplexOfContinuousMap _ 1 (ContinuousMap.id (stdSimplex ℝ (Fin 2)))) ≫
      (singularPrismDegree ℚ 1 ≫
        (CoefficientH0.SingularChains ℚ (TopCat.of (stdSimplex ℝ (Fin 2)))).d 2 1 +
       (CoefficientH0.SingularChains ℚ (TopCat.of (stdSimplex ℝ (Fin 2)))).d 1 0 ≫
        singularPrismDegree ℚ 0) =
    CoefficientH0.singularGenerator ℚ _ 1
      (singularSimplexOfContinuousMap _ 1 (ContinuousMap.id (stdSimplex ℝ (Fin 2)))) ≫
      ((CoefficientSingularSubdivision.singularSubdivision ℚ).f 1 - 𝟙 _) := standard_edge_equation ℚ


#print axioms prismFace_transport
#print axioms singularPrism_identity
#print axioms subdivisionHomotopy
#print axioms actual_prism_face
#print axioms degree_zero
#print axioms integral_standard_edge
#print axioms rational_standard_edge
end ConstructionTargets.CoefficientSingularPrism
