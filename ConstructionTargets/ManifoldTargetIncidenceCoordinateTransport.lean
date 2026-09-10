import ConstructionTargets.ManifoldTargetFiberChartExtension
open Set
open scoped ContDiff Manifold
noncomputable section
namespace ConstructionTargets.ManifoldTargetIncidenceCoordinateTransport
variable {E G F M N P : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold 𝓘(ℝ,G) ∞ N]
  [TopologicalSpace P] [ChartedSpace F P] [IsManifold 𝓘(ℝ,F) ∞ P]
  (f : M → P) (g : N → P)
  (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f)
  (hg : ContMDiff 𝓘(ℝ,G) 𝓘(ℝ,F) ∞ g)
  (x : M) (y : N) (h : f x = g y)

include hg h in
omit [TopologicalSpace M] in
theorem right_smooth :
    ContDiffOn ℝ ∞ ((chartAt F (f x)) ∘ g ∘ (chartAt G y).symm)
      ((chartAt G y).target ∩ (chartAt G y).symm ⁻¹' (g ⁻¹' (chartAt F (f x)).source)) := by
  rw [h]
  exact ManifoldTargetFiberChartExtension.representative_smooth g hg y

include hg h in
omit [TopologicalSpace M] [IsManifold 𝓘(ℝ,G) ∞ N] [IsManifold 𝓘(ℝ,F) ∞ P] in
theorem right_derivative :
    fderiv ℝ ((chartAt F (f x)) ∘ g ∘ (chartAt G y).symm) ((chartAt G y) y) =
      mfderiv 𝓘(ℝ,G) 𝓘(ℝ,F) g y := by
  rw [h]
  exact ManifoldTargetFiberChartExtension.representative_derivative g hg y

include hf hg h in
omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,G) ∞ N] [IsManifold 𝓘(ℝ,F) ∞ P] in
theorem coordinate_transversality
    (ht : LinearMap.range (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x).toLinearMap ⊔
      LinearMap.range (mfderiv 𝓘(ℝ,G) 𝓘(ℝ,F) g y).toLinearMap = ⊤) :
    LinearMap.range (fderiv ℝ ((chartAt F (f x)) ∘ f ∘ (chartAt E x).symm)
      ((chartAt E x) x)).toLinearMap ⊔
    LinearMap.range (fderiv ℝ ((chartAt F (f x)) ∘ g ∘ (chartAt G y).symm)
      ((chartAt G y) y)).toLinearMap = ⊤ := by
  rw [ManifoldTargetFiberChartExtension.representative_derivative f hf x,
    right_derivative f g hg x y h]
  exact ht
#print axioms right_smooth
#print axioms right_derivative
#print axioms coordinate_transversality
end ConstructionTargets.ManifoldTargetIncidenceCoordinateTransport
