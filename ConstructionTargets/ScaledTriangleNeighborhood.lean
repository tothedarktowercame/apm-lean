import Mathlib
import ConstructionTargets.StandardTriangleEmbedding
noncomputable section
open Set Topology
namespace ConstructionTargets.ScaledTriangleNeighborhood
open StandardTriangleEmbedding

theorem norm_parametrization (z : Simplex) : ‖parametrization z‖ ≤ 1 := by
 have hs := z.2.2
 rw [Fin.sum_univ_three] at hs
 have h0 := z.2.1 0
 have h1 := z.2.1 1
 have h2 := z.2.1 2
 rw [Prod.norm_def, max_le_iff]
 change |z.1 1 - 1/3| ≤ 1 ∧ |z.1 2 - 1/3| ≤ 1
 constructor <;> rw [abs_le] <;> constructor <;> linarith

def scaled (a : ℝ × ℝ) (r : ℝ) (z : Simplex) : ℝ × ℝ := a + r • parametrization z

theorem exists_triangle (U : Set (ℝ × ℝ)) (hU : IsOpen U) (a : ℝ × ℝ) (ha : a ∈ U) :
 ∃ r : ℝ, 0 < r ∧ IsClosedEmbedding (scaled a r) ∧
 IsCompact (Set.range (scaled a r)) ∧ Set.range (scaled a r) ⊆ U ∧
 IsOpen (scaled a r '' interiorParameters) ∧ a ∈ scaled a r '' interiorParameters := by
 obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hU a ha
 let r := ε/2
 have hr : 0 < r := half_pos hε
 let H : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  (Homeomorph.smulOfNeZero r (ne_of_gt hr)).trans (Homeomorph.addLeft a)
 have he : scaled a r = H ∘ parametrization := rfl
 have hc : Continuous (scaled a r) := by rw [he]; exact H.continuous.comp continuous_parametrization
 refine ⟨r,hr,hc.isClosedEmbedding (H.injective.comp injective_parametrization),isCompact_range hc,?_,?_,?_⟩
 · rintro _ ⟨z,rfl⟩
   apply hball
   rw [Metric.mem_ball, dist_eq_norm]
   have heq : scaled a r z - a = r • parametrization z := by simp [scaled]
   rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
   have hb := mul_le_mul_of_nonneg_left (norm_parametrization z) (le_of_lt hr)
   dsimp [r] at *
   linarith
 · rw [he, Set.image_comp, interior_image]
   exact H.isOpenMap _ open_interior
 · obtain ⟨z,hz,hzero⟩ := center_mem
   refine ⟨z,hz,?_⟩
   simp [scaled,hzero]

#print axioms norm_parametrization
#print axioms exists_triangle
end ConstructionTargets.ScaledTriangleNeighborhood
