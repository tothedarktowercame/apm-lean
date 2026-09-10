import ConstructionTargets.SardGenuineSmoothOpenDomainLocalization
import ConstructionTargets.RegularFiberFixedModelOverlaps
import ConstructionTargets.LocalTransverseDifference
open Set Filter
open scoped ContDiff Topology
noncomputable section
namespace ConstructionTargets.LocalTransverseExtensionChart
variable {E G F : Type*}
 [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
 [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G] [CompleteSpace G]
 [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
theorem exists_chart (f : E → F) (g : G → F) (U : Set E) (V : Set G)
 (hU : IsOpen U) (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g V)
 (x : E) (y : G) (hx : x ∈ U) (hy : y ∈ V) (hxy : f x = g y)
 (ht : LinearMap.range (fderiv ℝ f x).toLinearMap ⊔ LinearMap.range (fderiv ℝ g y).toLinearMap = ⊤) :
 ∃ (a : E → F) (b : G → F), ContDiff ℝ ∞ a ∧ ContDiff ℝ ∞ b ∧
 a =ᶠ[𝓝 x] f ∧ b =ᶠ[𝓝 y] g ∧
 ∃ (hz : LocalTransverseDifference.difference a b (x,y) = 0)
 (d : RegularFiberFixedModelOverlaps.FiberChart (LocalTransverseDifference.difference a b) 0),
 (⟨(x,y),hz⟩ : {z // LocalTransverseDifference.difference a b z = 0}) ∈ d.chart.source := by
 letI : MeasurableSpace F := borel F
 letI : BorelSpace F := ⟨rfl⟩
 obtain ⟨a,ha,hea⟩ := SardGenuineSmoothOpenDomainLocalizationProbe.exists_smooth_extension_near f U hU hf x hx
 obtain ⟨b,hb,heb⟩ := SardGenuineSmoothOpenDomainLocalizationProbe.exists_smooth_extension_near g V hV hg y hy
 have hz : LocalTransverseDifference.difference a b (x,y) = 0 := by
  change a x - b y = 0
  rw [hea.eq_of_nhds, heb.eq_of_nhds, hxy, sub_self]
 have hs : ContDiff ℝ ∞ (LocalTransverseDifference.difference a b) :=
  (ha.comp contDiff_fst).sub (hb.comp contDiff_snd)
 have ht' : LinearMap.range (fderiv ℝ a x).toLinearMap ⊔ LinearMap.range (fderiv ℝ b y).toLinearMap = ⊤ := by
  rw [hea.fderiv_eq, heb.fderiv_eq]
  exact ht
 have hd := LocalTransverseDifference.surjective a b x y
   (ha.differentiable (by simp) x) (hb.differentiable (by simp) y) ht'
 obtain ⟨d,hdc⟩ := RegularFiberFixedModelOverlaps.exists_chart
   (LocalTransverseDifference.difference a b) 0 hs ⟨(x,y),hz⟩ hd
 exact ⟨a,b,ha,hb,hea,heb,hz,d,hdc⟩
#print axioms exists_chart
end ConstructionTargets.LocalTransverseExtensionChart
