import ConstructionTargets.SphereCapGraphDensity

noncomputable section
namespace ConstructionTargets.SphereCapL2Image

open SphereCapHeight Metric Set
open ConstructionTargets.GraphMetricComparison

abbrev Ambient (d : ℕ) := WithLp 2 (E d × ℝ)

def upperCap (d : ℕ) : Set (Ambient d) := {z | ‖z‖ = 1 ∧ 0 < z.snd}
def lowerCap (d : ℕ) : Set (Ambient d) := {z | ‖z‖ = 1 ∧ z.snd < 0}

lemma norm_eq_one_of_sq {d : ℕ} {z : Ambient d} (h : ‖z‖ ^ 2 = 1) : ‖z‖ = 1 := by
  nlinarith [norm_nonneg z]

lemma upper_graph_subset_cap (d : ℕ) : Graph d (upper d) (domain d) ⊆ upperCap d := by
  intro z hz
  have he : point d (upper d) z.fst = z := point_recover d (upper d) (domain d) ⟨z, hz⟩
  have hs := upper_norm_sq hz.1
  change ‖point d (upper d) z.fst‖ ^ 2 = 1 at hs
  rw [he] at hs
  refine ⟨norm_eq_one_of_sq hs, ?_⟩
  rw [hz.2]
  exact upper_pos hz.1

lemma lower_graph_subset_cap (d : ℕ) : Graph d (lower d) (domain d) ⊆ lowerCap d := by
  intro z hz
  have he : point d (lower d) z.fst = z := point_recover d (lower d) (domain d) ⟨z, hz⟩
  have hs := lower_norm_sq hz.1
  change ‖point d (lower d) z.fst‖ ^ 2 = 1 at hs
  rw [he] at hs
  refine ⟨norm_eq_one_of_sq hs, ?_⟩
  rw [hz.2]
  exact lower_neg hz.1

lemma upperCap_fst_mem {d : ℕ} {z : Ambient d} (hz : z ∈ upperCap d) : z.fst ∈ domain d := by
  rw [domain, mem_ball_zero_iff]
  have hsq := WithLp.prod_norm_sq_eq_of_L2 z
  rw [hz.1] at hsq
  have hsnd : 0 < ‖z.snd‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (ne_of_gt hz.2))
  nlinarith [sq_nonneg ‖z.fst‖]

lemma lowerCap_fst_mem {d : ℕ} {z : Ambient d} (hz : z ∈ lowerCap d) : z.fst ∈ domain d := by
  rw [domain, mem_ball_zero_iff]
  have hsq := WithLp.prod_norm_sq_eq_of_L2 z
  rw [hz.1] at hsq
  have hsnd : 0 < ‖z.snd‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (ne_of_lt hz.2))
  nlinarith [sq_nonneg ‖z.fst‖]

lemma upperCap_snd {d : ℕ} {z : Ambient d} (hz : z ∈ upperCap d) :
    z.snd = upper d z.fst := by
  have hsq := WithLp.prod_norm_sq_eq_of_L2 z
  rw [hz.1, one_pow, Real.norm_eq_abs, sq_abs] at hsq
  have hr : z.snd ^ 2 = 1 - ‖z.fst‖ ^ 2 := by linarith
  rw [SphereCapHeight.upper, ← hr, Real.sqrt_sq (le_of_lt hz.2)]

lemma lowerCap_snd {d : ℕ} {z : Ambient d} (hz : z ∈ lowerCap d) :
    z.snd = lower d z.fst := by
  have hsq := WithLp.prod_norm_sq_eq_of_L2 z
  rw [hz.1, one_pow, Real.norm_eq_abs, sq_abs] at hsq
  have hr : z.snd ^ 2 = 1 - ‖z.fst‖ ^ 2 := by linarith
  rw [SphereCapHeight.lower, SphereCapHeight.upper, ← hr,
    Real.sqrt_sq_eq_abs, abs_of_neg hz.2]
  simp

lemma upper_graph_eq_cap (d : ℕ) : Graph d (upper d) (domain d) = upperCap d := by
  apply Set.Subset.antisymm (upper_graph_subset_cap d)
  intro z hz
  exact ⟨upperCap_fst_mem hz, upperCap_snd hz⟩

lemma lower_graph_eq_cap (d : ℕ) : Graph d (lower d) (domain d) = lowerCap d := by
  apply Set.Subset.antisymm (lower_graph_subset_cap d)
  intro z hz
  exact ⟨lowerCap_fst_mem hz, lowerCap_snd hz⟩

example : Graph 2 (upper 2) (domain 2) = upperCap 2 := upper_graph_eq_cap 2
example : Graph 2 (lower 2) (domain 2) = lowerCap 2 := lower_graph_eq_cap 2
example : Graph 3 (upper 3) (domain 3) = upperCap 3 := upper_graph_eq_cap 3
example : Graph 3 (lower 3) (domain 3) = lowerCap 3 := lower_graph_eq_cap 3

#print axioms upperCap_fst_mem
#print axioms lowerCap_fst_mem
#print axioms upperCap_snd
#print axioms lowerCap_snd
#print axioms upper_graph_eq_cap
#print axioms lower_graph_eq_cap

end ConstructionTargets.SphereCapL2Image
