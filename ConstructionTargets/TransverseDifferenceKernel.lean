import ConstructionTargets.TransverseDifferenceRegularity
import ConstructionTargets.RegularFiberFixedModel
open scoped ContDiff Manifold
noncomputable section
namespace ConstructionTargets.TransverseDifferenceKernel
open TransverseDifferenceRegularity
variable {E G F M N : Type*}
 [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
 [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
 [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
 [TopologicalSpace M] [ChartedSpace E M]
 [TopologicalSpace N] [ChartedSpace G N]
 (f : M → F) (g : N → F)
 (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f)
 (hg : ContMDiff 𝓘(ℝ,G) 𝓘(ℝ,F) ∞ g)
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ G] [FiniteDimensional ℝ F] in
include hf hg in
lemma mem_kernel (p : M × N) (v : E × G) :
 v ∈ (mfderiv (𝓘(ℝ,E).prod 𝓘(ℝ,G)) 𝓘(ℝ,F) (difference f g) p).ker ↔
 mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f p.1 v.1 = mfderiv 𝓘(ℝ,G) 𝓘(ℝ,F) g p.2 v.2 := by
 change (mfderiv (𝓘(ℝ,E).prod 𝓘(ℝ,G)) 𝓘(ℝ,F) (difference f g) p) v = 0 ↔ _
 rw [derivative f g hf hg]
 exact @sub_eq_zero F _ _ _
omit [FiniteDimensional ℝ F] in
include hf hg in
lemma kernel_dimension
 (ht : ∀ x y, f x = g y →
 LinearMap.range (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x).toLinearMap ⊔
 LinearMap.range (mfderiv 𝓘(ℝ,G) 𝓘(ℝ,F) g y).toLinearMap = ⊤)
 (p : M × N) (hp : f p.1 = g p.2) :
 Module.finrank ℝ (mfderiv (𝓘(ℝ,E).prod 𝓘(ℝ,G)) 𝓘(ℝ,F) (difference f g) p).ker =
 Module.finrank ℝ E + Module.finrank ℝ G - Module.finrank ℝ F := by
 have hs := regular f g hf hg ht p (sub_eq_zero.mpr hp)
 have h := RegularFiberFixedModel.kernel_dimension (E := E × G) (F := F)
   (mfderiv (𝓘(ℝ,E).prod 𝓘(ℝ,G)) 𝓘(ℝ,F) (difference f g) p) hs
 simpa only [Module.finrank_prod] using h
#print axioms mem_kernel
#print axioms kernel_dimension
end ConstructionTargets.TransverseDifferenceKernel
