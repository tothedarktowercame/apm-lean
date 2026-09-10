import ConstructionTargets.ManifoldTargetIncidenceImmersion
import ConstructionTargets.TransverseLinearPair
import ConstructionTargets.RegularFiberFixedModel
open Set Filter
open scoped ContDiff Manifold Topology
noncomputable section
namespace ConstructionTargets.ManifoldTargetIncidenceTangent
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
abbrev inclusionLinear (x : {z : M × N // f z.1 = g z.2}) :=
 letI := normalizedAtlas f g hf hg ht
 mfderiv 𝓘(ℝ,Space (E := E) (G := G) (F := F)) (𝓘(ℝ,E).prod 𝓘(ℝ,G))
   (Subtype.val : {z : M × N // f z.1 = g z.2} → M × N) x

def differenceLinear (x : {z : M × N // f z.1 = g z.2}) : (E × G) →L[ℝ] F :=
 let A : E →L[ℝ] F := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x.val.1
 let B : G →L[ℝ] F := mfderiv 𝓘(ℝ,G) 𝓘(ℝ,F) g x.val.2
 A.comp (ContinuousLinearMap.fst ℝ E G) - B.comp (ContinuousLinearMap.snd ℝ E G)

theorem range_le (x : {z : M × N // f z.1 = g z.2}) :
 LinearMap.range (inclusionLinear f g hf hg ht x).toLinearMap ≤ (differenceLinear (E := E) (G := G) (F := F) f g x).ker := by
 letI := normalizedAtlas f g hf hg ht
 letI := normalized_isManifold f g hf hg ht
 have hi := (normalized_smooth_inclusion f g hf hg ht).mdifferentiable (by simp) x
 have h1 := mfderiv_comp x (mdifferentiableAt_fst (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,G))) hi
 have h2 := mfderiv_comp x (mdifferentiableAt_snd (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,G))) hi
 have hf1 := mfderiv_comp x (hf.mdifferentiable (by simp) x.val.1)
   (mdifferentiableAt_fst.comp x hi)
 have hg2 := mfderiv_comp x (hg.mdifferentiable (by simp) x.val.2)
   (mdifferentiableAt_snd.comp x hi)
 have he : f ∘ (Prod.fst ∘ (Subtype.val : {z : M × N // f z.1 = g z.2} → M × N)) =
   g ∘ (Prod.snd ∘ Subtype.val) := by funext y; exact y.property
 rw [he] at hf1
 rw [hg2, h1, h2, mfderiv_fst, mfderiv_snd] at hf1
 rintro v ⟨w,rfl⟩
 change (differenceLinear (E := E) (G := G) (F := F) f g x) ((inclusionLinear f g hf hg ht x) w) = 0
 simp only [differenceLinear, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
 apply sub_eq_zero.mpr
 exact (congrArg (fun L => L w) hf1).symm

omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ G] [CompleteSpace G]
 [FiniteDimensional ℝ F] [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,G) ∞ N]
 [IsManifold 𝓘(ℝ,F) ∞ P] in
include ht in
theorem difference_surjective (x : {z : M × N // f z.1 = g z.2}) :
 Function.Surjective (differenceLinear (E := E) (G := G) (F := F) f g x) := by
 intro w
 obtain ⟨⟨a,b⟩,hab⟩ := (TransverseLinearPair.isTransversePair_iff_surjective_coprod _ _).mp
   (ht x.val.1 x.val.2 x.property) w
 refine ⟨(a,-b),?_⟩
 let A : E →L[ℝ] F := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x.val.1
 let B : G →L[ℝ] F := mfderiv 𝓘(ℝ,G) 𝓘(ℝ,F) g x.val.2
 change A (a : E) - B (-(b : G)) = w
 calc
  A (a : E) - B (-(b : G)) = A a - -(B b) := congrArg (fun t : F => A a - t) (map_neg B (b : G))
  _ = A a + B b := sub_neg_eq_add _ _
  _ = w := hab

theorem inclusion_range (x : {z : M × N // f z.1 = g z.2}) :
 LinearMap.range (inclusionLinear f g hf hg ht x).toLinearMap =
 (differenceLinear (E := E) (G := G) (F := F) f g x).ker := by
 letI : FiniteDimensional ℝ (TangentSpace (𝓘(ℝ,E).prod 𝓘(ℝ,G)) x.val) :=
  inferInstanceAs (FiniteDimensional ℝ (E × G))
 apply Submodule.eq_of_le_of_finrank_eq (range_le f g hf hg ht x)
 have hj := ManifoldTargetIncidenceImmersion.normalized_injective f g hf hg ht x
 rw [LinearMap.finrank_range_of_inj hj]
 have hk := RegularFiberFixedModel.kernel_dimension
   (differenceLinear (E := E) (G := G) (F := F) f g x) (difference_surjective f g ht x)
 change Module.finrank ℝ (Space (E := E) (G := G) (F := F)) = _
 simpa [Space, Module.finrank_prod] using hk.symm

theorem tangent_equalizer (x : {z : M × N // f z.1 = g z.2}) :
 letI := normalizedAtlas f g hf hg ht
 Function.Injective (mfderiv 𝓘(ℝ,Space (E := E) (G := G) (F := F)) (𝓘(ℝ,E).prod 𝓘(ℝ,G))
   (Subtype.val : {z : M × N // f z.1 = g z.2} → M × N) x) ∧
 ∀ v : E × G, v ∈ LinearMap.range (inclusionLinear f g hf hg ht x).toLinearMap ↔
   mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x.val.1 v.1 = mfderiv 𝓘(ℝ,G) 𝓘(ℝ,F) g x.val.2 v.2 := by
 refine ⟨ManifoldTargetIncidenceImmersion.normalized_injective f g hf hg ht x, ?_⟩
 intro v
 rw [inclusion_range f g hf hg ht x]
 change (differenceLinear (E := E) (G := G) (F := F) f g x) v = 0 ↔ _
 exact sub_eq_zero

#print axioms range_le
#print axioms difference_surjective
#print axioms inclusion_range
#print axioms tangent_equalizer
end ConstructionTargets.ManifoldTargetIncidenceTangent
