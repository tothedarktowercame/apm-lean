import ConstructionTargets.C1GraphPartition
import Mathlib.Topology.Instances.ENNReal.Lemmas

noncomputable section
namespace ConstructionTargets.ENNRealMultiplicativeSqueeze

open Filter Set
open scoped ENNReal Topology

theorem upper_tendsto (d : ℕ) (B : ℝ≥0∞) :
    Tendsto (fun ε : ℝ => (ENNReal.ofReal (1 + ε)) ^ d * B)
      (𝓝[Set.Ioo 0 1] 0) (𝓝 B) := by
  have hbase : Tendsto (fun ε : ℝ => ENNReal.ofReal (1 + ε))
      (𝓝[Set.Ioo 0 1] 0) (𝓝 1) := by
    have hr := ((show Tendsto (fun ε : ℝ => (1 : ℝ) + ε) (𝓝 0) (𝓝 (1 + 0)) from
      tendsto_const_nhds.add tendsto_id).mono_left
        (@nhdsWithin_le_nhds ℝ _ 0 (Set.Ioo 0 1)))
    have hr' : Tendsto (fun ε : ℝ => 1 + ε) (𝓝[Set.Ioo 0 1] 0) (𝓝 1) := by
      simpa using hr
    have hc := (ENNReal.continuous_ofReal.tendsto (1 : ℝ)).comp hr'
    simpa only [add_zero, Function.comp_apply, ENNReal.ofReal_one] using hc
  simpa using ENNReal.Tendsto.mul (a := (1 : ℝ≥0∞) ^ d) (b := B)
    (ENNReal.Tendsto.pow hbase)
    (Or.inl (by simp)) tendsto_const_nhds (Or.inr (by simp))

theorem lower_tendsto (d : ℕ) (B : ℝ≥0∞) :
    Tendsto (fun ε : ℝ => (ENNReal.ofReal (1 - ε)) ^ d * B)
      (𝓝[Set.Ioo 0 1] 0) (𝓝 B) := by
  have hbase : Tendsto (fun ε : ℝ => ENNReal.ofReal (1 - ε))
      (𝓝[Set.Ioo 0 1] 0) (𝓝 1) := by
    have hr := ((show Tendsto (fun ε : ℝ => (1 : ℝ) - ε) (𝓝 0) (𝓝 (1 - 0)) from
      tendsto_const_nhds.sub tendsto_id).mono_left
        (@nhdsWithin_le_nhds ℝ _ 0 (Set.Ioo 0 1)))
    have hr' : Tendsto (fun ε : ℝ => 1 - ε) (𝓝[Set.Ioo 0 1] 0) (𝓝 1) := by
      simpa using hr
    have hc := (ENNReal.continuous_ofReal.tendsto (1 : ℝ)).comp hr'
    simpa only [sub_zero, Function.comp_apply, ENNReal.ofReal_one] using hc
  simpa using ENNReal.Tendsto.mul (a := (1 : ℝ≥0∞) ^ d) (b := B)
    (ENNReal.Tendsto.pow hbase)
    (Or.inl (by simp)) tendsto_const_nhds (Or.inr (by simp))

theorem eq_of_bounds (d : ℕ) (A B : ℝ≥0∞)
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 →
      (ENNReal.ofReal (1 - ε)) ^ d * B ≤ A ∧
      A ≤ (ENNReal.ofReal (1 + ε)) ^ d * B) : A = B := by
  letI : NeBot (𝓝[Set.Ioo (0 : ℝ) 1] 0) := left_nhdsWithin_Ioo_neBot zero_lt_one
  apply le_antisymm
  · apply ge_of_tendsto (upper_tendsto d B)
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (h ε hε.1 hε.2).2
  · apply le_of_tendsto (lower_tendsto d B)
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (h ε hε.1 hε.2).1

#print axioms ConstructionTargets.ENNRealMultiplicativeSqueeze.upper_tendsto
#print axioms ConstructionTargets.ENNRealMultiplicativeSqueeze.lower_tendsto
#print axioms ConstructionTargets.ENNRealMultiplicativeSqueeze.eq_of_bounds

end ConstructionTargets.ENNRealMultiplicativeSqueeze
