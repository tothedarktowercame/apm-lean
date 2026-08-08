import Mathlib

/-!
# APM a97A03

## Statement repairs

None. The conventional implicit condition `a ≤ b` in the notation `[a,b]`
is made explicit.

## Encoding questions

The interval-domain function is represented by an ambient function `ℝ → ℝ`
whose relevant behavior is restricted to `Set.Icc a b`. At the two endpoints
the derivative is encoded by `derivWithin`; this differs from the unrestricted
derivative only on a Lebesgue-null set and faithfully expresses the a.e. claim.
-/

open MeasureTheory Filter

theorem apm_a97a03 (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : AbsolutelyContinuousOnInterval f a b) :
    (∃ B : ℝ, 0 < B ∧ ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      |f x - f y| ≤ B * |x - y|) ↔
    (∃ C : ℝ, 0 < C ∧
      ∀ᵐ x : ℝ ∂(volume.restrict (Set.Icc a b)),
        |derivWithin f (Set.Icc a b) x| ≤ C) := by
  constructor
  · rintro ⟨B, hB, hbound⟩
    let L : NNReal := ⟨B, hB.le⟩
    have hlip : LipschitzOnWith L f (Set.Icc a b) := by
      intro x hx y hy
      rw [edist_dist, edist_dist]
      have hL : (L : ENNReal) = ENNReal.ofReal B := by
        rw [ENNReal.coe_nnreal_eq]
        congr
      rw [hL]
      simpa [Real.dist_eq, ENNReal.ofReal_mul hB.le] using
        ENNReal.ofReal_le_ofReal (hbound x hx y hy)
    refine ⟨B, hB, ?_⟩
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
    simpa [Real.norm_eq_abs] using
      norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hx.1 hx.2) hlip
  · rintro ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    intro x hx y hy
    have hsub : Set.uIcc x y ⊆ Set.Icc a b := Set.uIcc_subset_Icc hx hy
    have hfac : AbsolutelyContinuousOnInterval f x y := hf.mono (by
      rw [Set.uIcc_of_le hab]
      exact hsub)
    have hae : ∀ᵐ t : ℝ, t ∈ Set.uIoc x y → ‖deriv f t‖ ≤ C := by
      have hb : ∀ᵐ t : ℝ, t ∈ Set.Icc a b →
          |derivWithin f (Set.Icc a b) t| ≤ C :=
        (ae_restrict_iff' measurableSet_Icc).mp hbound
      filter_upwards [hb, volume.ae_ne a, volume.ae_ne b] with t ht hta htb htu
      have hi : t ∈ Set.Ioo a b := by
        have hmem := hsub (Set.uIoc_subset_uIcc htu)
        exact ⟨hmem.1.lt_of_ne hta.symm, hmem.2.lt_of_ne htb⟩
      rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hi.1 hi.2)]
      simpa [Real.norm_eq_abs] using ht (Set.Ioo_subset_Icc_self hi)
    have hint := intervalIntegral.norm_integral_le_of_norm_le_const_ae hae
    rw [hfac.integral_deriv_eq_sub] at hint
    simpa [Real.norm_eq_abs, abs_sub_comm] using hint
