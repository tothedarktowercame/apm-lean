import ConstructionTargets.ChartedSpaceModelSmoothTransport
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import ConstructionTargets.TransverseDifferenceRegularity
open Set Filter
open scoped ContDiff Manifold Topology
noncomputable section
namespace ConstructionTargets.ChartedSpaceModelDerivativeTransport
open ChartedSpaceModelTransport ChartedSpaceModelSmoothTransport
variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem derivative_forward (e : E ≃L[ℝ] F) (x : M) :
    letI := chartedSpace (M := M) e.toHomeomorph
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) (id : M → M) x = e.toContinuousLinearMap := by
  letI := chartedSpace (M := M) e.toHomeomorph
  letI := ChartedSpaceModelSmoothTransport.isManifold (M := M) e
  have hd := (smooth_id_forward (M := M) e).mdifferentiable (by simp) x
  rw [mfderiv, if_pos hd]
  simp only [writtenInExtChartAt, extChartAt, mfld_simps]
  rw [ChartedSpaceModelTransport.chartAt_eq]
  have he : (fun z => e (chartAt E x ((chartAt E x).symm z))) =ᶠ[𝓝 (chartAt E x x)] e := by
    filter_upwards [(chartAt E x).open_target.mem_nhds
      ((chartAt E x).map_source (mem_chart_source E x))] with z hz
    rw [(chartAt E x).right_inv hz]
  simpa [ChartedSpaceModelTransport.chart, Function.comp_def, mfld_simps] using
    he.fderiv_eq.trans e.fderiv
theorem derivative_backward (e : E ≃L[ℝ] F) (x : M) :
    letI := chartedSpace (M := M) e.toHomeomorph
    mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) (id : M → M) x = e.symm.toContinuousLinearMap := by
  letI := chartedSpace (M := M) e.toHomeomorph
  letI := ChartedSpaceModelSmoothTransport.isManifold (M := M) e
  have hd := (smooth_id_backward (M := M) e).mdifferentiable (by simp) x
  rw [mfderiv, if_pos hd]
  simp only [writtenInExtChartAt, extChartAt, mfld_simps]
  rw [ChartedSpaceModelTransport.chartAt_eq]
  have he : (fun z => chartAt E x ((chartAt E x).symm (e.symm z))) =ᶠ[𝓝 (e (chartAt E x x))] e.symm := by
    have ht : e.symm ⁻¹' (chartAt E x).target ∈ 𝓝 (e (chartAt E x x)) :=
      ((chartAt E x).open_target.preimage e.symm.continuous).mem_nhds
        (by simp [mem_chart_source])
    filter_upwards [ht] with z hz
    exact (chartAt E x).right_inv hz
  simpa [ChartedSpaceModelTransport.chart, Function.comp_def, mfld_simps] using
    he.fderiv_eq.trans e.symm.fderiv

theorem derivative_inverse (e : E ≃L[ℝ] F) (x : M) :
    letI := chartedSpace (M := M) e.toHomeomorph
    (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) (id : M → M) x).comp
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) (id : M → M) x) = ContinuousLinearMap.id ℝ E ∧
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) (id : M → M) x).comp
      (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) (id : M → M) x) = ContinuousLinearMap.id ℝ F := by
  letI := chartedSpace (M := M) e.toHomeomorph
  rw [derivative_forward e x, derivative_backward e x]
  constructor
  · ext v; change e.symm (e v) = v; exact e.symm_apply_apply v
  · ext v; change e (e.symm v) = v; exact e.apply_symm_apply v
section Map
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem map_smooth (e : E ≃L[ℝ] F) (f : M → V)
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,V) ∞ f) :
    letI := chartedSpace (M := M) e.toHomeomorph
    ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,V) ∞ f := by
  letI := chartedSpace (M := M) e.toHomeomorph
  exact hf.comp (smooth_id_backward (M := M) e)

theorem map_derivative (e : E ≃L[ℝ] F) (f : M → V)
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,V) ∞ f) (x : M) :
    letI := chartedSpace (M := M) e.toHomeomorph
    mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) f x =
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) f x).comp e.symm.toContinuousLinearMap := by
  letI := chartedSpace (M := M) e.toHomeomorph
  have h := mfderiv_comp x (hf.mdifferentiable (by simp) x)
    ((smooth_id_backward (M := M) e).mdifferentiable (by simp) x)
  rw [derivative_backward e x] at h
  exact h

theorem map_surjective (e : E ≃L[ℝ] F) (f : M → V)
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,V) ∞ f) (x : M)
    (hs : Function.Surjective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,V) f x)) :
    letI := chartedSpace (M := M) e.toHomeomorph
    Function.Surjective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) f x) := by
  letI := chartedSpace (M := M) e.toHomeomorph
  rw [map_derivative e f hf x]
  exact hs.comp e.symm.surjective
end Map
section Product
variable {A B V X Y : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X] [ChartedSpace A X] [IsManifold 𝓘(ℝ,A) ∞ X]
  [TopologicalSpace Y] [ChartedSpace B Y] [IsManifold 𝓘(ℝ,B) ∞ Y]

lemma product_original_manifold :
    letI : ChartedSpace (A × B) (X × Y) := prodChartedSpace A X B Y
    IsManifold 𝓘(ℝ,A × B) ∞ (X × Y) := by
  letI : ChartedSpace (A × B) (X × Y) := prodChartedSpace A X B Y
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,A)) (I' := 𝓘(ℝ,B)) X Y

theorem product_identity_smooth :
    letI := productChartedSpace (E := A) (G := B) (M := X) (N := Y)
    ContMDiff (𝓘(ℝ,A).prod 𝓘(ℝ,B)) 𝓘(ℝ,WithLp 2 (A × B)) ∞ (id : X × Y → X × Y) ∧
    ContMDiff 𝓘(ℝ,WithLp 2 (A × B)) (𝓘(ℝ,A).prod 𝓘(ℝ,B)) ∞ (id : X × Y → X × Y) := by
  letI : ChartedSpace (A × B) (X × Y) := prodChartedSpace A X B Y
  letI := product_original_manifold (A := A) (B := B) (X := X) (Y := Y)
  constructor
  · simpa only [modelWithCornersSelf_prod] using smooth_id_forward (M := X × Y)
      (WithLp.prodContinuousLinearEquiv 2 ℝ A B).symm
  · simpa only [modelWithCornersSelf_prod] using smooth_id_backward (M := X × Y)
      (WithLp.prodContinuousLinearEquiv 2 ℝ A B).symm

theorem product_identity_derivative (p : X × Y) :
    letI := productChartedSpace (E := A) (G := B) (M := X) (N := Y)
    mfderiv (𝓘(ℝ,A).prod 𝓘(ℝ,B)) 𝓘(ℝ,WithLp 2 (A × B)) (id : X × Y → X × Y) p =
      (WithLp.prodContinuousLinearEquiv 2 ℝ A B).symm.toContinuousLinearMap ∧
    mfderiv 𝓘(ℝ,WithLp 2 (A × B)) (𝓘(ℝ,A).prod 𝓘(ℝ,B)) (id : X × Y → X × Y) p =
      (WithLp.prodContinuousLinearEquiv 2 ℝ A B).toContinuousLinearMap := by
  letI : ChartedSpace (A × B) (X × Y) := prodChartedSpace A X B Y
  letI := product_original_manifold (A := A) (B := B) (X := X) (Y := Y)
  constructor
  · simpa only [modelWithCornersSelf_prod] using
      derivative_forward (WithLp.prodContinuousLinearEquiv 2 ℝ A B).symm p
  · simpa only [modelWithCornersSelf_prod] using
      derivative_backward (WithLp.prodContinuousLinearEquiv 2 ℝ A B).symm p

theorem difference_smooth (f : X → V) (g : Y → V)
    (hf : ContMDiff 𝓘(ℝ,A) 𝓘(ℝ,V) ∞ f)
    (hg : ContMDiff 𝓘(ℝ,B) 𝓘(ℝ,V) ∞ g) :
    letI := productChartedSpace (E := A) (G := B) (M := X) (N := Y)
    ContMDiff 𝓘(ℝ,WithLp 2 (A × B)) 𝓘(ℝ,V) ∞
      (TransverseDifferenceRegularity.difference f g) := by
  letI : ChartedSpace (A × B) (X × Y) := prodChartedSpace A X B Y
  letI := product_original_manifold (A := A) (B := B) (X := X) (Y := Y)
  apply map_smooth (WithLp.prodContinuousLinearEquiv 2 ℝ A B).symm
  simpa only [modelWithCornersSelf_prod] using TransverseDifferenceRegularity.smooth f g hf hg

theorem difference_derivative (f : X → V) (g : Y → V)
    (hf : ContMDiff 𝓘(ℝ,A) 𝓘(ℝ,V) ∞ f)
    (hg : ContMDiff 𝓘(ℝ,B) 𝓘(ℝ,V) ∞ g) (p : X × Y) :
    letI := productChartedSpace (E := A) (G := B) (M := X) (N := Y)
    mfderiv 𝓘(ℝ,WithLp 2 (A × B)) 𝓘(ℝ,V)
      (TransverseDifferenceRegularity.difference f g) p =
    (mfderiv (𝓘(ℝ,A).prod 𝓘(ℝ,B)) 𝓘(ℝ,V)
      (TransverseDifferenceRegularity.difference f g) p).comp
      (WithLp.prodContinuousLinearEquiv 2 ℝ A B).toContinuousLinearMap := by
  letI : ChartedSpace (A × B) (X × Y) := prodChartedSpace A X B Y
  letI := product_original_manifold (A := A) (B := B) (X := X) (Y := Y)
  have h : ContMDiff 𝓘(ℝ,A × B) 𝓘(ℝ,V) ∞ (TransverseDifferenceRegularity.difference f g) := by
    simpa only [modelWithCornersSelf_prod] using TransverseDifferenceRegularity.smooth f g hf hg
  simpa only [modelWithCornersSelf_prod] using
    map_derivative (WithLp.prodContinuousLinearEquiv 2 ℝ A B).symm _ h p

theorem difference_regular (f : X → V) (g : Y → V)
    (hf : ContMDiff 𝓘(ℝ,A) 𝓘(ℝ,V) ∞ f)
    (hg : ContMDiff 𝓘(ℝ,B) 𝓘(ℝ,V) ∞ g)
    (ht : ∀ x y, f x = g y →
      LinearMap.range (mfderiv 𝓘(ℝ,A) 𝓘(ℝ,V) f x).toLinearMap ⊔
      LinearMap.range (mfderiv 𝓘(ℝ,B) 𝓘(ℝ,V) g y).toLinearMap = ⊤) :
    letI := productChartedSpace (E := A) (G := B) (M := X) (N := Y)
    ∀ p, TransverseDifferenceRegularity.difference f g p = 0 →
      Function.Surjective (mfderiv 𝓘(ℝ,WithLp 2 (A × B)) 𝓘(ℝ,V)
        (TransverseDifferenceRegularity.difference f g) p) := by
  letI := productChartedSpace (E := A) (G := B) (M := X) (N := Y)
  intro p hp
  rw [difference_derivative f g hf hg p]
  exact (TransverseDifferenceRegularity.regular f g hf hg ht p hp).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ A B).surjective
end Product
#print axioms derivative_forward
#print axioms derivative_backward
#print axioms derivative_inverse
#print axioms map_smooth
#print axioms map_derivative
#print axioms map_surjective
#print axioms product_original_manifold
#print axioms product_identity_smooth
#print axioms product_identity_derivative
#print axioms difference_smooth
#print axioms difference_derivative
#print axioms difference_regular
end ConstructionTargets.ChartedSpaceModelDerivativeTransport
