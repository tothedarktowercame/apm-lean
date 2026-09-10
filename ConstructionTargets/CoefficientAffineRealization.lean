import ConstructionTargets.CoefficientVertexCone
noncomputable section
namespace ConstructionTargets.CoefficientAffineRealization
open CategoryTheory CategoryTheory.Limits Simplicial SingularSubdivision
open CoefficientH0 CoefficientVertexCone
variable (R : Type) [CommRing R]
def affineGenerator {m : ℕ} {ι : Type} [Fintype ι]
    (v : Fin (m + 1) → stdSimplex ℝ ι) :
    ModuleCat.of R R ⟶
      (SingularChains R (TopCat.of (stdSimplex ℝ ι))).X m :=
  singularGenerator R _ m
    (singularSimplexOfContinuousMap _ m (affineSimplex v))

theorem affineGenerator_boundary {m : ℕ} {ι : Type} [Fintype ι]
    (v : Fin (m + 2) → stdSimplex ℝ ι) :
    affineGenerator R v ≫
        (SingularChains R (TopCat.of (stdSimplex ℝ ι))).d (m + 1) m =
      ∑ i : Fin (m + 2), (-1 : ℤ) ^ (i : ℕ) •
        affineGenerator R (v ∘ i.succAbove) := by
  rw [show affineGenerator R v = singularGenerator R _ (m + 1)
      (singularSimplexOfContinuousMap _ (m + 1) (affineSimplex v)) from rfl]
  rw [singularGenerator_boundary R]
  simp_rw [singularSimplexOfContinuousMap_affine_face]
  rfl

def vertexRealizationDegree {ι : Type} [Fintype ι] (n : ℕ) :
    (CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)).X n ⟶
      (SingularChains R (TopCat.of (stdSimplex ℝ ι))).X n := by
  change (∐ fun _ : Fin (n + 1) → stdSimplex ℝ ι ↦ ModuleCat.of R R) ⟶ _
  exact Limits.Sigma.desc fun v ↦ affineGenerator R v

@[simp, reassoc] theorem vertexGenerator_vertexRealizationDegree
    {ι : Type} [Fintype ι] (n : ℕ)
    (v : Fin (n + 1) → stdSimplex ℝ ι) :
    CoefficientVertexCone.vertexGenerator R _ n v ≫ vertexRealizationDegree R n = affineGenerator R v := by
  dsimp [CoefficientVertexCone.vertexGenerator, vertexRealizationDegree]
  exact Limits.Sigma.ι_desc _ v

/-- Affine realization is a chain map. -/
def vertexRealization {ι : Type} [Fintype ι] :
    CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι) ⟶
      SingularChains R (TopCat.of (stdSimplex ℝ ι)) where
  f := vertexRealizationDegree R
  comm' n m h := by
    obtain rfl := h
    apply Limits.Sigma.hom_ext
    intro v
    change (CoefficientVertexCone.vertexGenerator R _ (m + 1) v ≫ vertexRealizationDegree R (m + 1)) ≫ _ =
      (CoefficientVertexCone.vertexGenerator R _ (m + 1) v ≫ _) ≫ vertexRealizationDegree R m
    rw [vertexGenerator_vertexRealizationDegree R, affineGenerator_boundary R]
    rw [CoefficientVertexCone.vertexGenerator_boundary R, Preadditive.sum_comp]
    simp_rw [Preadditive.zsmul_comp,
      vertexGenerator_vertexRealizationDegree R]


example : CoefficientVertexCone.VertexChains ℤ (stdSimplex ℝ (Fin 2)) ⟶
    SingularChains ℤ (TopCat.of (stdSimplex ℝ (Fin 2))) := vertexRealization ℤ
example : CoefficientVertexCone.VertexChains ℚ (stdSimplex ℝ (Fin 2)) ⟶
    SingularChains ℚ (TopCat.of (stdSimplex ℝ (Fin 2))) := vertexRealization ℚ
#print axioms affineGenerator_boundary
#print axioms vertexGenerator_vertexRealizationDegree
#print axioms vertexRealization
end ConstructionTargets.CoefficientAffineRealization
