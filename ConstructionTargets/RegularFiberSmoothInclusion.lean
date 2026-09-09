import ConstructionTargets.RegularFiberGlobalAtlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
open Set
open scoped ContDiff Manifold
noncomputable section
namespace ConstructionTargets.RegularFiberSmoothInclusion
open RegularFiberFixedModelOverlaps RegularFiberGlobalAtlas
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (f : E → F) (c : F) (hsm : ContDiff ℝ ∞ f)
  (hreg : ∀ x, f x = c → Function.Surjective (fderiv ℝ f x))
theorem smooth_inclusion :
    letI := chartedSpace f c hsm hreg
    ContMDiff 𝓘(ℝ, Model (E := E) (F := F)) 𝓘(ℝ,E) ∞
      (Subtype.val : {x : E // f x = c} → E) := by
  letI := chartedSpace f c hsm hreg
  letI := isManifold f c hsm hreg
  apply contMDiff_iff.mpr
  refine ⟨continuous_subtype_val, ?_⟩
  intro x y
  let d := selected f c hsm hreg x
  have hb : ContDiffOn ℝ ∞ (fun z => (d.chart.symm z).val) d.chart.target :=
    d.backward_smooth.congr (fun z hz => d.backward_eq z hz)
  simpa [extChartAt, chartAt, d] using hb
#print axioms smooth_inclusion
end ConstructionTargets.RegularFiberSmoothInclusion
