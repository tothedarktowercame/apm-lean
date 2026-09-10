import Mathlib
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import ConstructionTargets.TransverseLinearPair
open scoped ContDiff Manifold
noncomputable section
namespace ConstructionTargets.TransverseDifferenceRegularity
variable {E G F M N : Type*}
 [NormedAddCommGroup E] [NormedSpace ℝ E]
 [NormedAddCommGroup G] [NormedSpace ℝ G]
 [NormedAddCommGroup F] [NormedSpace ℝ F]
 [TopologicalSpace M] [ChartedSpace E M]
 [TopologicalSpace N] [ChartedSpace G N]
 (f : M → F) (g : N → F)
 (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f)
 (hg : ContMDiff 𝓘(ℝ,G) 𝓘(ℝ,F) ∞ g)
def difference (p : M × N) : F := f p.1 - g p.2
include hf hg in
lemma smooth : ContMDiff (𝓘(ℝ,E).prod 𝓘(ℝ,G)) 𝓘(ℝ,F) ∞ (difference f g) :=
 (hf.comp contMDiff_fst).sub (hg.comp contMDiff_snd)
include hf hg in
lemma derivative (p : M × N) (v : E × G) :
 (mfderiv (𝓘(ℝ,E).prod 𝓘(ℝ,G)) 𝓘(ℝ,F) (difference f g) p v : F) =
 @HSub.hSub F F F _ (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f p.1 v.1) (mfderiv 𝓘(ℝ,G) 𝓘(ℝ,F) g p.2 v.2) := by
 have hF : MDifferentiableAt (𝓘(ℝ,E).prod 𝓘(ℝ,G)) 𝓘(ℝ,F) (f ∘ Prod.fst) p := (hf.mdifferentiable (by simp) p.1).comp p mdifferentiableAt_fst
 have hG : MDifferentiableAt (𝓘(ℝ,E).prod 𝓘(ℝ,G)) 𝓘(ℝ,F) (g ∘ Prod.snd) p := (hg.mdifferentiable (by simp) p.2).comp p mdifferentiableAt_snd
 change (mfderiv (𝓘(ℝ,E).prod 𝓘(ℝ,G)) 𝓘(ℝ,F) ((f ∘ Prod.fst) - (g ∘ Prod.snd)) p) v = _
 rw [mfderiv_sub hF hG]
 rw [mfderiv_comp p (hf.mdifferentiable (by simp) p.1) mdifferentiableAt_fst,
   mfderiv_comp p (hg.mdifferentiable (by simp) p.2) mdifferentiableAt_snd]
 simp only [mfderiv_fst, mfderiv_snd]
 rfl
include hf hg in
lemma regular (ht : ∀ x y, f x = g y →
 LinearMap.range (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x).toLinearMap ⊔
 LinearMap.range (mfderiv 𝓘(ℝ,G) 𝓘(ℝ,F) g y).toLinearMap = ⊤) :
 ∀ p, difference f g p = 0 → Function.Surjective
   (mfderiv (𝓘(ℝ,E).prod 𝓘(ℝ,G)) 𝓘(ℝ,F) (difference f g) p) := by
 intro p hp w
 have ht' := ht p.1 p.2 (sub_eq_zero.mp hp)
 obtain ⟨⟨a,b⟩, hab⟩ := (TransverseLinearPair.isTransversePair_iff_surjective_coprod _ _).mp ht' w
 refine ⟨(a,-b), ?_⟩
 rw [derivative f g hf hg]
 rw [map_neg]
 exact (@sub_neg_eq_add F _ _ _).trans hab
omit [NormedSpace ℝ F] [TopologicalSpace M] [TopologicalSpace N] in
lemma fiber_eq : {p : M × N | difference f g p = 0} = {p | f p.1 = g p.2} := by
 ext p
 exact sub_eq_zero
#print axioms smooth
#print axioms derivative
#print axioms regular
#print axioms fiber_eq
end ConstructionTargets.TransverseDifferenceRegularity
