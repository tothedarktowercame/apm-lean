import Mathlib
import ConstructionTargets.TransverseLinearPair
open Set
open scoped ContDiff
noncomputable section
namespace ConstructionTargets.LocalTransverseDifference
variable {E G F : Type*}
 [NormedAddCommGroup E] [NormedSpace ℝ E]
 [NormedAddCommGroup G] [NormedSpace ℝ G]
 [NormedAddCommGroup F] [NormedSpace ℝ F]
 (f : E → F) (g : G → F)
def difference (z : E × G) := f z.1 - g z.2

theorem smooth_on {U : Set E} {V : Set G}
 (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g V) :
 ContDiffOn ℝ ∞ (difference f g) (U ×ˢ V) := by
 exact (hf.comp contDiffOn_fst (fun _ h => h.1)).sub
   (hg.comp contDiffOn_snd (fun _ h => h.2))

theorem derivative (x : E) (y : G)
 (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g y) (v : E × G) :
 fderiv ℝ (difference f g) (x,y) v = fderiv ℝ f x v.1 - fderiv ℝ g y v.2 := by
 have h1 : HasFDerivAt (fun z : E × G => f z.1)
   ((fderiv ℝ f x).comp (ContinuousLinearMap.fst ℝ E G)) (x,y) :=
   hf.hasFDerivAt.comp (x,y) hasFDerivAt_fst
 have h2 : HasFDerivAt (fun z : E × G => g z.2)
   ((fderiv ℝ g y).comp (ContinuousLinearMap.snd ℝ E G)) (x,y) :=
   hg.hasFDerivAt.comp (x,y) hasFDerivAt_snd
 have h := h1.sub h2
 rw [show fderiv ℝ (difference f g) (x,y) = _ from h.fderiv]
 rfl

theorem surjective (x : E) (y : G)
 (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g y)
 (ht : LinearMap.range (fderiv ℝ f x).toLinearMap ⊔
   LinearMap.range (fderiv ℝ g y).toLinearMap = ⊤) :
 Function.Surjective (fderiv ℝ (difference f g) (x,y)) := by
 intro w
 obtain ⟨⟨a,b⟩,hab⟩ := (TransverseLinearPair.isTransversePair_iff_surjective_coprod _ _).mp ht w
 refine ⟨(a,-b),?_⟩
 rw [derivative f g x y hf hg, map_neg, sub_neg_eq_add]
 exact hab
#print axioms smooth_on
#print axioms derivative
#print axioms surjective
end ConstructionTargets.LocalTransverseDifference
