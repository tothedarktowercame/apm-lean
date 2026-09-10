import ConstructionTargets.ManifoldTargetIncidenceTangent
open Set Filter
open scoped ContDiff Manifold Topology
noncomputable section
namespace ConstructionTargets.IncidenceParameterProjection
variable {E G F M N P : Type*}
 [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
 [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G] [CompleteSpace G]
 [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
 [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
 [TopologicalSpace N] [ChartedSpace G N] [IsManifold 𝓘(ℝ,G) ∞ N]
 [TopologicalSpace P] [ChartedSpace F P] [IsManifold 𝓘(ℝ,F) ∞ P]
local instance : ChartedSpace (E × G) (M × N) := prodChartedSpace E M G N
local instance : IsManifold 𝓘(ℝ,E × G) ∞ (M × N) := by
 rw [modelWithCornersSelf_prod]
 exact IsManifold.prod M N
open ManifoldTargetIncidenceSmoothCharts ManifoldTargetIncidenceGlobalAtlas
variable (f : M → P) (g : N → P)
 (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f) (hg : ContMDiff 𝓘(ℝ,G) 𝓘(ℝ,F) ∞ g)
 (ht : ∀ x y, f x = g y → LinearMap.range (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x).toLinearMap ⊔
       LinearMap.range (mfderiv 𝓘(ℝ,G) 𝓘(ℝ,F) g y).toLinearMap = ⊤)
open ManifoldTargetIncidenceTangent

def projection (x : {z : M × N // f z.1 = g z.2}) : N := x.val.2

theorem smooth :
 letI := normalizedAtlas f g hf hg ht
 ContMDiff 𝓘(ℝ,Space (E := E) (G := G) (F := F)) 𝓘(ℝ,G) ∞ (projection f g) := by
 letI := normalizedAtlas f g hf hg ht
 exact contMDiff_snd.comp (normalized_smooth_inclusion f g hf hg ht)

theorem derivative (x : {z : M × N // f z.1 = g z.2}) :
 letI := normalizedAtlas f g hf hg ht
 mfderiv 𝓘(ℝ,Space (E := E) (G := G) (F := F)) 𝓘(ℝ,G) (projection f g) x =
 (ContinuousLinearMap.snd ℝ E G).comp (inclusionLinear f g hf hg ht x) := by
 letI := normalizedAtlas f g hf hg ht
 have hi := (normalized_smooth_inclusion f g hf hg ht).mdifferentiable (by simp) x
 have h := mfderiv_comp x (mdifferentiableAt_snd (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,G))) hi
 rw [mfderiv_snd] at h
 exact h

theorem regularity_iff (x : {z : M × N // f z.1 = g z.2}) :
 letI := normalizedAtlas f g hf hg ht
 Function.Surjective (mfderiv 𝓘(ℝ,Space (E := E) (G := G) (F := F)) 𝓘(ℝ,G) (projection f g) x) ↔
 Function.Surjective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x.val.1) := by
 letI := normalizedAtlas f g hf hg ht
 rw [derivative f g hf hg ht x]
 let L : Space (E := E) (G := G) (F := F) →L[ℝ] (E × G) := inclusionLinear f g hf hg ht x
 let A : E →L[ℝ] F := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x.val.1
 let B : G →L[ℝ] F := mfderiv 𝓘(ℝ,G) 𝓘(ℝ,F) g x.val.2
 have heq (v : E × G) : v ∈ LinearMap.range L.toLinearMap ↔ A v.1 = B v.2 :=
  (tangent_equalizer f g hf hg ht x).2 v
 change Function.Surjective ((ContinuousLinearMap.snd ℝ E G).comp L) ↔ Function.Surjective A
 constructor
 · intro hs w
   have htr : LinearMap.range A.toLinearMap ⊔ LinearMap.range B.toLinearMap = ⊤ := ht x.val.1 x.val.2 x.property
   obtain ⟨⟨a,b⟩,hab⟩ := (TransverseLinearPair.isTransversePair_iff_surjective_coprod A.toLinearMap B.toLinearMap).mp htr w
   obtain ⟨v,hv⟩ := hs b
   have hh := (heq (L v)).mp ⟨v,rfl⟩
   change (L v).2 = b at hv
   rw [hv] at hh
   refine ⟨(a : E) + (L v).1,?_⟩
   rw [map_add]
   rw [hh]
   exact hab
 · intro hs b
   obtain ⟨a,ha⟩ := hs (B b)
   obtain ⟨v,hv⟩ := (heq (a,b)).mpr ha
   refine ⟨v,?_⟩
   exact congrArg Prod.snd hv

#print axioms smooth
#print axioms derivative
#print axioms regularity_iff
end ConstructionTargets.IncidenceParameterProjection
