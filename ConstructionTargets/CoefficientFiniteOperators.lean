import ConstructionTargets.CoefficientFiniteRealization
import ConstructionTargets.CoefficientSingularPrism
noncomputable section
namespace ConstructionTargets.CoefficientFiniteOperators
open CategoryTheory CategoryTheory.Limits Simplicial SingularSubdivision
variable (R : Type) [CommRing R]
def realize {V : Type} {n : ℕ}
    (c : FiniteVertexChain V n) :
    ModuleCat.of R R ⟶ (CoefficientVertexCone.VertexChains R V).X n :=
  c.sum fun v z => z • CoefficientVertexCone.vertexGenerator R V n v

@[simp] theorem realize_single {V : Type} {n : ℕ}
    (v : Fin (n + 1) → V) (z : ℤ) :
    realize R (Finsupp.single v z) =
      z • CoefficientVertexCone.vertexGenerator R V n v := by
  simp [realize]

@[simp] theorem realize_zero {V : Type} {n : ℕ} :
    realize R (0 : FiniteVertexChain V n) = 0 := by
  simp [realize]

@[simp] theorem realize_add {V : Type} {n : ℕ}
    (c d : FiniteVertexChain V n) :
    realize R (c + d) =
      realize R c + realize R d := by
  classical
  simp [realize, Finsupp.sum_add_index,
    add_smul]

theorem realize_finset_sum {V α : Type} {n : ℕ}
    (s : Finset α) (f : α → FiniteVertexChain V n) :
    realize R (∑ a ∈ s, f a) =
      ∑ a ∈ s, realize R (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

@[simp] theorem realize_zsmul {V : Type} {n : ℕ}
    (z : ℤ) (c : FiniteVertexChain V n) :
    realize R (z • c) =
      z • realize R c := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add v k c hvc hk ih =>
      simp only [smul_add, realize_add R,
        Finsupp.smul_single, realize_single R, ih,
        smul_smul]
      simp

@[simp] theorem realize_neg {V : Type} {n : ℕ}
    (c : FiniteVertexChain V n) :
    realize R (-c) = -realize R c := by
  simpa only [neg_one_zsmul] using realize_zsmul R (-1) c

@[simp] theorem realize_sub {V : Type} {n : ℕ}
    (c d : FiniteVertexChain V n) :
    realize R (c - d) =
      realize R c - realize R d := by
  simp [sub_eq_add_neg]

theorem realize_bind {V W : Type} {m n : ℕ}
    (c : FiniteVertexChain V m)
    (f : (Fin (m + 1) → V) → FiniteVertexChain W n)
    (F : (CoefficientVertexCone.VertexChains R V).X m ⟶ (CoefficientVertexCone.VertexChains R W).X n)
    (hF : ∀ v, realize R (f v) =
      CoefficientVertexCone.vertexGenerator R V m v ≫ F) :
    realize R (FiniteVertexChain.bind c f) =
      realize R c ≫ F := by
  classical
  induction c using Finsupp.induction with
  | zero => simp [FiniteVertexChain.bind]
  | single_add v z c hvc hz ih =>
      simp only [FiniteVertexChain.bind_add,
        FiniteVertexChain.bind_single,
        realize_add R, realize_single R,
        realize_zsmul R,
        Preadditive.add_comp, Preadditive.zsmul_comp, hF, ih]

theorem realize_cone {V : Type} {n : ℕ} (b : V)
    (c : FiniteVertexChain V n) :
    realize R (FiniteVertexChain.cone b c) =
      realize R c ≫ CoefficientVertexCone.vertexCone R V b n := by
  classical
  induction c using Finsupp.induction with
  | zero => simp [FiniteVertexChain.cone]
  | single_add v z c hvc hz ih =>
      change realize R
        (Finsupp.embDomain (prependVertexEmbedding b) c) = _ at ih
      simp only [FiniteVertexChain.cone, Finsupp.embDomain_add,
        realize_add R,
        Finsupp.embDomain_single, realize_single R,
        Preadditive.add_comp,
        Preadditive.zsmul_comp, CoefficientVertexCone.vertexGenerator_vertexCone R]
      rw [ih]
      simp only [prependVertexEmbedding_apply]

theorem realize_boundary {V : Type} {n : ℕ}
    (v : Fin (n + 2) → V) :
    realize R (FiniteVertexChain.boundary v) =
      CoefficientVertexCone.vertexGenerator R V (n + 1) v ≫ (CoefficientVertexCone.VertexChains R V).d (n + 1) n := by
  rw [CoefficientVertexCone.vertexGenerator_boundary R]
  rw [show FiniteVertexChain.boundary v =
      ∑ i ∈ (Finset.univ : Finset (Fin (n + 2))),
        Finsupp.single (v ∘ i.succAbove) ((-1 : ℤ) ^ (i : ℕ)) by
    simp [FiniteVertexChain.boundary]]
  rw [realize_finset_sum R]
  simp

theorem finiteVertexSubdivision_realize {ι : Type} [Fintype ι] (n : ℕ)
    (v : Fin (n + 1) → stdSimplex ℝ ι) :
    realize R (finiteVertexSubdivision n v) =
      CoefficientVertexCone.vertexGenerator R _ n v ≫ CoefficientBarycentricNaturality.vertexSubdivision R n := by
  induction n with
  | zero => simp [finiteVertexSubdivision]
  | succ n ih =>
      rw [finiteVertexSubdivision_succ]
      rw [realize_cone R]
      rw [realize_bind R _ _ (CoefficientBarycentricNaturality.vertexSubdivision R n) ih]
      rw [realize_boundary R]
      simp only [Category.assoc]
      rw [← CoefficientBarycentricNaturality.vertexGenerator_vertexSubdivision_succ R]

theorem finiteVertexPrism_realize {ι : Type} [Fintype ι]
    (n : ℕ) (v : Fin (n + 1) → stdSimplex ℝ ι) :
    realize R (finiteVertexPrism n v) =
      CoefficientVertexCone.vertexGenerator R _ n v ≫ CoefficientVertexPrism.vertexPrism R n := by
  induction n with
  | zero => simp [finiteVertexPrism]
  | succ n ih =>
      rw [finiteVertexPrism_succ, realize_cone R]
      simp only [realize_sub R,
        finiteVertexSubdivision_realize R,
        realize_single R]
      rw [realize_bind R _ _ (CoefficientVertexPrism.vertexPrism R n) ih]
      rw [realize_boundary R]
      simp only [Category.assoc]
      symm
      rw [CoefficientVertexPrism.vertexGenerator_vertexPrism_succ R]
      simp only [Preadditive.comp_sub, Category.comp_id, one_zsmul]
      rfl

theorem postcomposeFiniteVertexChain_realize
    {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (n : ℕ) (σ : C(stdSimplex ℝ ι, X))
    (c : FiniteVertexChain (stdSimplex ℝ ι) n) :
    CoefficientFiniteRealization.finiteSingularChainRealize R n (postcomposeFiniteVertexChain σ c) =
      realize R c ≫ CoefficientAffineRealization.vertexRealizationDegree R n ≫
        (CoefficientH0.singularPostcomposition R σ).f n := by
  classical
  induction c using Finsupp.induction with
  | zero => simp [postcomposeFiniteVertexChain, CoefficientFiniteRealization.finiteSingularChainRealize,
      realize]
  | single_add v z c hvc hz ih =>
      simp only [postcomposeFiniteVertexChain, Finsupp.mapDomain_add,
        Finsupp.mapDomain_single, CoefficientFiniteRealization.finiteSingularChainRealize_add R,
        CoefficientFiniteRealization.finiteSingularChainRealize_single R, realize_add R,
        realize_single R, Preadditive.add_comp]
      congr 1
      simp only [Preadditive.zsmul_comp]
      congr 1
      simp only [← Category.assoc]
      rw [CoefficientAffineRealization.vertexGenerator_vertexRealizationDegree R]
      dsimp [CoefficientAffineRealization.affineGenerator]
      rw [CoefficientH0.singularGenerator_singularPostcomposition R]


theorem subdivision_realize {X : Type} [TopologicalSpace X] (n : ℕ)
    (σ : C(stdSimplex ℝ (Fin (n+1)), X)) :
    CoefficientFiniteRealization.finiteSingularChainRealize R n
      (postcomposeFiniteVertexChain σ (finiteVertexSubdivision n (standardSimplexVertices n))) =
    CoefficientH0.singularGenerator R (TopCat.of X) n
      (singularSimplexOfContinuousMap (TopCat.of X) n σ) ≫
      (CoefficientSingularSubdivision.singularSubdivision R).f n := by
  rw [postcomposeFiniteVertexChain_realize, finiteVertexSubdivision_realize]
  rw [CoefficientSingularSubdivision.generator_formula]
  simp only [continuousMapOfSingularSimplex_ofContinuousMap, Category.assoc]

theorem prism_realize {X : Type} [TopologicalSpace X] (n : ℕ)
    (σ : C(stdSimplex ℝ (Fin (n+1)), X)) :
    CoefficientFiniteRealization.finiteSingularChainRealize R (n+1) (postcomposedPrism n σ) =
    CoefficientH0.singularGenerator R (TopCat.of X) n
      (singularSimplexOfContinuousMap (TopCat.of X) n σ) ≫
      CoefficientSingularPrism.singularPrismDegree R n := by
  unfold postcomposedPrism
  rw [postcomposeFiniteVertexChain_realize, finiteVertexPrism_realize]
  rw [CoefficientSingularPrism.singularGenerator_singularPrismDegree]
  simp only [continuousMapOfSingularSimplex_ofContinuousMap, Category.assoc]
  rfl

theorem integral_subdivision_edge :
    CoefficientFiniteRealization.finiteSingularChainRealize ℤ 1
      (postcomposeFiniteVertexChain (ContinuousMap.id (stdSimplex ℝ (Fin 2))) (finiteVertexSubdivision 1 (standardSimplexVertices 1))) =
    CoefficientH0.singularGenerator ℤ (TopCat.of (stdSimplex ℝ (Fin 2))) 1
      (singularSimplexOfContinuousMap (TopCat.of (stdSimplex ℝ (Fin 2))) 1 (ContinuousMap.id (stdSimplex ℝ (Fin 2)))) ≫
      (CoefficientSingularSubdivision.singularSubdivision ℤ).f 1 := subdivision_realize ℤ 1 (ContinuousMap.id _)

theorem integral_prism_edge :
    CoefficientFiniteRealization.finiteSingularChainRealize ℤ (1+1) (postcomposedPrism 1 (ContinuousMap.id (stdSimplex ℝ (Fin 2)))) =
    CoefficientH0.singularGenerator ℤ (TopCat.of (stdSimplex ℝ (Fin 2))) 1
      (singularSimplexOfContinuousMap (TopCat.of (stdSimplex ℝ (Fin 2))) 1 (ContinuousMap.id (stdSimplex ℝ (Fin 2)))) ≫
      CoefficientSingularPrism.singularPrismDegree ℤ 1 := prism_realize ℤ 1 (ContinuousMap.id _)

theorem rational_subdivision_edge :
    CoefficientFiniteRealization.finiteSingularChainRealize ℚ 1
      (postcomposeFiniteVertexChain (ContinuousMap.id (stdSimplex ℝ (Fin 2))) (finiteVertexSubdivision 1 (standardSimplexVertices 1))) =
    CoefficientH0.singularGenerator ℚ (TopCat.of (stdSimplex ℝ (Fin 2))) 1
      (singularSimplexOfContinuousMap (TopCat.of (stdSimplex ℝ (Fin 2))) 1 (ContinuousMap.id (stdSimplex ℝ (Fin 2)))) ≫
      (CoefficientSingularSubdivision.singularSubdivision ℚ).f 1 := subdivision_realize ℚ 1 (ContinuousMap.id _)

theorem rational_prism_edge :
    CoefficientFiniteRealization.finiteSingularChainRealize ℚ (1+1) (postcomposedPrism 1 (ContinuousMap.id (stdSimplex ℝ (Fin 2)))) =
    CoefficientH0.singularGenerator ℚ (TopCat.of (stdSimplex ℝ (Fin 2))) 1
      (singularSimplexOfContinuousMap (TopCat.of (stdSimplex ℝ (Fin 2))) 1 (ContinuousMap.id (stdSimplex ℝ (Fin 2)))) ≫
      CoefficientSingularPrism.singularPrismDegree ℚ 1 := prism_realize ℚ 1 (ContinuousMap.id _)

#print axioms finiteVertexSubdivision_realize
#print axioms finiteVertexPrism_realize
#print axioms postcomposeFiniteVertexChain_realize
#print axioms subdivision_realize
#print axioms prism_realize
#print axioms integral_subdivision_edge
#print axioms rational_prism_edge
end ConstructionTargets.CoefficientFiniteOperators
