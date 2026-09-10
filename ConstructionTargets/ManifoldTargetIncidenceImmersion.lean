import ConstructionTargets.ManifoldTargetIncidenceGlobalAtlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
open Set Filter
open scoped ContDiff Manifold Topology
noncomputable section
namespace ConstructionTargets.ManifoldTargetIncidenceImmersion
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
omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ G] [CompleteSpace G]
 [FiniteDimensional ℝ F] [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,G) ∞ N]
 [TopologicalSpace P] [ChartedSpace F P] [IsManifold 𝓘(ℝ,F) ∞ P] in
lemma backward_injective (d : IncidenceChart (E := E) (G := G) (F := F) f g)
    (z : Model (E := E) (G := G) (F := F)) (hz : z ∈ d.chart.target) :
    Function.Injective (mfderiv 𝓘(ℝ,Model (E := E) (G := G) (F := F)) 𝓘(ℝ,E × G) d.backward z) := by
  have hm : MapsTo d.backward d.chart.target d.ambient := by
    intro w hw
    rw [← d.backward_eq w hw]
    have ht := d.chart.map_target hw
    rwa [d.source_eq] at ht
  have hd := (d.backward_smooth.contMDiffAt (d.chart.open_target.mem_nhds hz)).mdifferentiableAt (by simp)
  have hf := d.forward_smooth.mdifferentiableOn (by simp) _ (hm hz)
  have hc := mfderivWithin_comp z hf hd.mdifferentiableWithinAt hm
    (d.chart.open_target.uniqueMDiffWithinAt hz)
  simp only [mfderivWithin_of_mem_nhds (d.chart.open_target.mem_nhds hz)] at hc
  have he : d.forward ∘ d.backward =ᶠ[𝓝 z] id := by
    filter_upwards [d.chart.open_target.mem_nhds hz] with w hw
    change d.forward (d.backward w) = w
    rw [← d.backward_eq w hw, ← d.forward_eq _ (d.chart.map_target hw), d.chart.right_inv hw]
  rw [he.mfderiv_eq, mfderiv_id] at hc
  intro a b hab
  have h := congrArg (fun L : Model (E := E) (G := G) (F := F) →L[ℝ] Model (E := E) (G := G) (F := F) => L a) hc
  have h' := congrArg (fun L : Model (E := E) (G := G) (F := F) →L[ℝ] Model (E := E) (G := G) (F := F) => L b) hc
  change a = (mfderivWithin 𝓘(ℝ,E × G) 𝓘(ℝ,Model (E := E) (G := G) (F := F)) d.forward d.ambient (d.backward z)) ((mfderiv 𝓘(ℝ,Model (E := E) (G := G) (F := F)) 𝓘(ℝ,E × G) d.backward z) a) at h
  change b = (mfderivWithin 𝓘(ℝ,E × G) 𝓘(ℝ,Model (E := E) (G := G) (F := F)) d.forward d.ambient (d.backward z)) ((mfderiv 𝓘(ℝ,Model (E := E) (G := G) (F := F)) 𝓘(ℝ,E × G) d.backward z) b) at h'
  rw [hab] at h
  exact h.trans h'.symm
lemma derivative_eq (x : {z : M × N // f z.1 = g z.2}) :
    letI := chartedSpace f g hf hg ht
    mfderiv 𝓘(ℝ,Model (E := E) (G := G) (F := F)) 𝓘(ℝ,E × G) Subtype.val x =
      mfderiv 𝓘(ℝ,Model (E := E) (G := G) (F := F)) 𝓘(ℝ,E × G)
        (selected f g hf hg ht x).backward ((selected f g hf hg ht x).chart x) := by
  letI := chartedSpace f g hf hg ht
  let d := selected f g hf hg ht x
  have hz : d.chart x ∈ d.chart.target := d.chart.map_source (selected_center f g hf hg ht x)
  have hx : d.backward (d.chart x) = x.val := by
    rw [← d.backward_eq _ hz, d.chart.left_inv (selected_center f g hf hg ht x)]
  have hd := (smooth_inclusion f g hf hg ht).mdifferentiable (by simp) x
  have hb := (d.backward_smooth.contMDiffAt (d.chart.open_target.mem_nhds hz)).mdifferentiableAt (by simp)
  change _ = mfderiv _ _ d.backward (d.chart x)
  rw [mfderiv, if_pos hd, mfderiv, if_pos hb]
  simp only [writtenInExtChartAt, mfld_simps]
  simp only [hx]
  apply Filter.EventuallyEq.fderivWithin_eq
  · filter_upwards [Filter.mem_of_superset (d.chart.open_target.mem_nhds hz) (fun z hz => hz) |> mem_nhdsWithin_of_mem_nhds] with z hz'
    exact congrArg (chartAt (E × G) x.val) (d.backward_eq z hz')
  · exact congrArg (chartAt (E × G) x.val) (d.backward_eq (d.chart x) hz)

theorem inclusion_injective (x : {z : M × N // f z.1 = g z.2}) :
    letI := chartedSpace f g hf hg ht
    Function.Injective (mfderiv 𝓘(ℝ,Model (E := E) (G := G) (F := F)) 𝓘(ℝ,E × G) Subtype.val x) := by
  letI := chartedSpace f g hf hg ht
  rw [derivative_eq f g hf hg ht x]
  exact backward_injective f g _ _
    ((selected f g hf hg ht x).chart.map_source (selected_center f g hf hg ht x))

def Immersion (n : ℕ)
 (c : ChartedSpace (EuclideanSpace ℝ (Fin n)) {z : M × N // f z.1 = g z.2}) : Prop :=
 letI := c
 ∀ x : {z : M × N // f z.1 = g z.2},
 Function.Injective (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) (𝓘(ℝ,E).prod 𝓘(ℝ,G))
   (Subtype.val : {z : M × N // f z.1 = g z.2} → M × N) x)

theorem normalized_injective (x : {z : M × N // f z.1 = g z.2}) :
 letI := normalizedAtlas f g hf hg ht
 Function.Injective (mfderiv 𝓘(ℝ,Space (E := E) (G := G) (F := F)) (𝓘(ℝ,E).prod 𝓘(ℝ,G))
   (Subtype.val : {z : M × N // f z.1 = g z.2} → M × N) x) := by
 have h : Immersion (E := E) (G := G) f g _ (normalizedAtlas f g hf hg ht) := by
  apply cast_property (index_eq (E := E) (G := G) (F := F)) (chartedSpace f g hf hg ht)
    (Immersion (E := E) (G := G) f g)
  intro y
  have h := inclusion_injective f g hf hg ht y
  rwa [modelWithCornersSelf_prod] at h
 exact h x
#print axioms backward_injective
#print axioms derivative_eq
#print axioms inclusion_injective
#print axioms normalized_injective
end ConstructionTargets.ManifoldTargetIncidenceImmersion
