import ConstructionTargets.ChartedSpaceModelTransport
import Mathlib.Geometry.Manifold.Diffeomorph
open Set
open scoped ContDiff Manifold
noncomputable section
namespace ConstructionTargets.ChartedSpaceModelSmoothTransport
open ChartedSpaceModelTransport
variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

lemma overlap (e : E ≃L[ℝ] F) (x y : M) :
    ContDiffOn ℝ ∞ ((chart e.toHomeomorph y) ∘ (chart e.toHomeomorph x).symm)
      ((chart e.toHomeomorph x).symm ≫ₕ chart e.toHomeomorph y).source := by
  have h := ((contDiffGroupoid ∞ 𝓘(ℝ,E)).compatible
    (chart_mem_atlas E x) (chart_mem_atlas E y)).1
  simp only [mfld_simps] at h
  have h' := e.contDiff.comp_contDiffOn
    (h.comp e.symm.contDiff.contDiffOn (s := e.symm ⁻¹' ((chartAt E x).symm ≫ₕ chartAt E y).source)
      (by intro z hz; simpa [mfld_simps] using hz))
  simpa [ChartedSpaceModelTransport.chart, Function.comp_def, mfld_simps] using h'

theorem isManifold (e : E ≃L[ℝ] F) :
    letI := chartedSpace (M := M) e.toHomeomorph
    IsManifold 𝓘(ℝ,F) ∞ M := by
  letI := chartedSpace (M := M) e.toHomeomorph
  apply isManifold_of_contDiffOn
  intro a b ha hb
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  simpa only [mfld_simps] using overlap e x y
theorem smooth_id_forward (e : E ≃L[ℝ] F) :
    letI := chartedSpace (M := M) e.toHomeomorph
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ (id : M → M) := by
  letI := chartedSpace (M := M) e.toHomeomorph
  letI := isManifold (M := M) e
  apply contMDiff_iff.mpr
  refine ⟨continuous_id, ?_⟩
  intro x y
  have h := ((contDiffGroupoid ∞ 𝓘(ℝ,E)).compatible
    (chart_mem_atlas E x) (chart_mem_atlas E y)).1
  have h' := e.contDiff.comp_contDiffOn h
  simp only [extChartAt, mfld_simps]
  rw [ChartedSpaceModelTransport.chartAt_eq]
  simpa [ChartedSpaceModelTransport.chart, Function.comp_def, mfld_simps] using h'
theorem smooth_id_backward (e : E ≃L[ℝ] F) :
    letI := chartedSpace (M := M) e.toHomeomorph
    ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ (id : M → M) := by
  letI := chartedSpace (M := M) e.toHomeomorph
  letI := isManifold (M := M) e
  apply contMDiff_iff.mpr
  refine ⟨continuous_id, ?_⟩
  intro x y
  have h := ((contDiffGroupoid ∞ 𝓘(ℝ,E)).compatible
    (chart_mem_atlas E x) (chart_mem_atlas E y)).1
  have h' := h.comp e.symm.contDiff.contDiffOn
    (s := e.symm ⁻¹' ((chartAt E x).symm ≫ₕ chartAt E y).source)
    (by intro z hz; simpa [mfld_simps] using hz)
  simp only [extChartAt, mfld_simps]
  rw [ChartedSpaceModelTransport.chartAt_eq]
  simpa [ChartedSpaceModelTransport.chart, Function.comp_def, mfld_simps] using h'
section Product
variable {A B X Y : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B]
  [TopologicalSpace X] [ChartedSpace A X] [IsManifold 𝓘(ℝ,A) ∞ X]
  [TopologicalSpace Y] [ChartedSpace B Y] [IsManifold 𝓘(ℝ,B) ∞ Y]

theorem product_isManifold :
    letI := ChartedSpaceModelTransport.productChartedSpace (E := A) (G := B) (M := X) (N := Y)
    IsManifold 𝓘(ℝ,WithLp 2 (A × B)) ∞ (X × Y) := by
  letI : ChartedSpace (A × B) (X × Y) := prodChartedSpace A X B Y
  haveI : IsManifold 𝓘(ℝ,A × B) ∞ (X × Y) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod (I := 𝓘(ℝ,A)) (I' := 𝓘(ℝ,B)) X Y
  exact isManifold (M := X × Y) (WithLp.prodContinuousLinearEquiv 2 ℝ A B).symm
end Product
#print axioms overlap
#print axioms isManifold
#print axioms smooth_id_forward
#print axioms smooth_id_backward
#print axioms product_isManifold
end ConstructionTargets.ChartedSpaceModelSmoothTransport
