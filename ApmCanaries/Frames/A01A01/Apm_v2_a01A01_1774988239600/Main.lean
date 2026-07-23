import Mathlib
import ApmCanaries.Frames.A01A01.Apm_v2_a01A01_1774988239600.Scratch

noncomputable section

namespace ApmCanaries.Frames.A01A01.Apm_v2_a01A01_1774988239600.Main

/- Authoritative frame-local Lean development.
   Keep exploratory detours in Scratch.lean.
   Promote reusable lemmas explicitly into ApmCanaries.Local. -/

open Filter Topology

lemma nat_cast_le_pow_three_div_two {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) ≤ ((3 : ℝ) / 2) ^ n := by
  refine Nat.le_induction ?base ?step hn
  · norm_num
  · intro k hk hbound
    have hk' : (2 : ℕ) ≤ k := by exact Nat.succ_le_succ_iff.mp hk
    have hineq : (k.succ : ℝ) ≤ (3 / 2) * k := by
      have hkpos : (0 : ℝ) < k := by exact_mod_cast lt_of_le_of_lt hk' (by norm_num)
      have hk_ge : (1 : ℝ) ≤ k / 2 := by
        have : (2 : ℝ) ≤ k := by exact_mod_cast hk'
        have htwo : (0 : ℝ) < 2 := by norm_num
        exact (div_le_iff (show (0 : ℝ) < 2 by norm_num)).2 (by linarith)
      have : (k : ℝ) / 2 ≤ k := by
        have hk_nonneg : 0 ≤ (k : ℝ) := by positivity
        exact (div_le_iff (by norm_num : (0 : ℝ) < 2)).1 (by linarith)
      have hk_half : (k : ℝ) / 2 ≤ k := this
      have hk_half_pos : 1 ≤ (k : ℝ) / 2 := by
        refine (div_le_iff (by norm_num : (0 : ℝ) < 2)).1 ?_
        have : (2 : ℝ) ≤ k := by exact_mod_cast hk'
        linarith
      have hk_ge' : ((k : ℝ) / 2) + 1 ≤ k := by
        have : ((k : ℝ) / 2) + 1 ≤ k / 2 + k / 2 := by
          have hk_nonneg : 0 ≤ (k : ℝ) := by positivity
          have haux : (0 : ℝ) ≤ k / 2 := by exact (div_nonneg hk_nonneg (show (0 : ℝ) ≤ 2 by norm_num))
          have h : ((k : ℝ) / 2) + 1 ≤ (k : ℝ) := by
            have hk'' : 1 ≤ k / 2 := hk_half_pos
            have : k / 2 + 1 ≤ k / 2 + k / 2 := add_le_add_left hk_half_pos (k / 2)
            simpa using this
          simpa [two_mul, add_comm, add_left_comm] using h
        simpa using this
      have hk_final : (k.succ : ℝ) ≤ (3 / 2) * k := by
        have htemp : (k.succ : ℝ) = (k : ℝ) + 1 := by push_cast; ring
        have hineq' : (k : ℝ) + 1 ≤ (3 / 2) * k := by
          have hk_nn : (0 : ℝ) ≤ k := by positivity
          have hk2 : k ≤ 2 * k := by have := (by positivity : (0 : ℝ) ≤ k); nlinarith
          have hk_half' : ((k : ℝ) / 2) ≤ k := hk_half
          have hk_half_pos' : 1 ≤ (k : ℝ) / 2 := hk_half_pos
          calc
            (k : ℝ) + 1 = (k : ℝ) / 2 + (k : ℝ) / 2 + 1 := by ring
            _ ≤ (k : ℝ) / 2 + (k : ℝ) / 2 + (k : ℝ) / 2 := by
              have : 1 ≤ (k : ℝ) / 2 := hk_half_pos
              nlinarith
            _ = (3 / 2) * k := by field_simp [two_mul]
        simpa [htemp] using hineq'
      have hk_ge'' : ((3 : ℝ) / 2) * k ≤ ((3 : ℝ) / 2) * ((3 : ℝ) / 2) ^ k := by
        have hk_nonneg : 0 ≤ ((3 : ℝ) / 2) := by norm_num
        have hnonneg : 0 ≤ ((3 : ℝ) / 2) ^ k := pow_nonneg (by norm_num) _
        exact mul_le_mul_of_nonneg_left hbound (by norm_num)
      have hk_succ : (k.succ : ℝ) ≤ ((3 : ℝ) / 2) ^ (k.succ) := by
        have : ((3 : ℝ) / 2) ^ (k.succ) = ((3 : ℝ) / 2) * ((3 : ℝ) / 2) ^ k := by
          simp [pow_succ]
        have := le_trans hk_final hk_ge''
        simpa [this]
      simpa using hk_succ

lemma tendsto_nat_div_two_pow :
    Tendsto (fun n : ℕ => ((n : ℝ) / (2 : ℝ) ^ n)) atTop (𝓝 (0 : ℝ)) := by
  have hgeom : Tendsto (fun n : ℕ => ((3 : ℝ) / 4) ^ n) atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hbound : ∀ᶠ n in atTop,
      ‖(n : ℝ) / (2 : ℝ) ^ n‖ ≤ ((3 : ℝ) / 4) ^ n := by
    refine (eventually_ge_atTop (2 : ℕ)).mp ?_
    refine Filter.eventually_of_forall ?_
    intro n hn
    have hn' : 0 ≤ ((n : ℝ) / (2 : ℝ) ^ n) := by
      have : 0 ≤ (n : ℝ) := by positivity
      have : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) _
      exact div_nonneg (by positivity) (le_of_lt this)
    have hpow : (n : ℝ) ≤ ((3 : ℝ) / 2) ^ n := nat_cast_le_pow_three_div_two hn
    have hx : ((3 : ℝ) / 4) ^ n = (((3 : ℝ) / 2) ^ n) / ((2 : ℝ) ^ n) := by
      field_simp [pow_add, pow_succ, pow_two]
    have : (n : ℝ) / (2 : ℝ) ^ n ≤ ((3 : ℝ) / 4) ^ n := by
      have hpos : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) _
      have hpow' := (div_le_div_of_nonneg_right hpow (le_of_lt hpos))
      simpa [hx]
    have habs := abs_of_nonneg hn'
    simpa [habs] using this
  refine tendsto_of_norm_tendsto_zero ?_
  refine tendsto_of_tendsto_of_tendsto_of_le' hgeom ?_ ?_
  · exact hbound
  · exact Filter.eventually_of_forall fun _ => by positivity

end ApmCanaries.Frames.A01A01.Apm_v2_a01A01_1774988239600.Main
