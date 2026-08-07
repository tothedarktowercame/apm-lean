import Mathlib

open Filter MeasureTheory Set

noncomputable section

/-!
# APM a00J02

## Statement repairs

None.

## Encoding notes

The function on `[0,1]` is represented by a function on `ℝ`, restricted to that
interval. Absolute continuity is encoded by Mathlib's
`AbsolutelyContinuousOnInterval`, and the square-integrability hypothesis uses
the ordinary derivative `deriv f`.
-/

/-- FTC: for absolutely continuous f with f(0) = 0,
    f x = ∫ t in 0..x, deriv f t for x ∈ [0,1].
    Uses `AbsolutelyContinuousOnInterval.mono` to restrict to subinterval [0,x],
    then `integral_deriv_eq_sub`. -/
lemma ftc_a00j02 (f : ℝ → ℝ)
    (hf_ac : AbsolutelyContinuousOnInterval f 0 1)
    (hf_zero : f 0 = 0)
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    f x = ∫ t in (0)..x, deriv f t := by
  have hsub : uIcc 0 x ⊆ uIcc 0 1 := by
    intro y hy
    rw [mem_uIcc] at hy ⊢
    rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨h1, le_trans h2 hx1⟩
    · left
      have hy0 : y = 0 := by linarith
      constructor <;> linarith
  have hac := hf_ac.mono hsub
  have h := hac.integral_deriv_eq_sub
  rw [hf_zero] at h
  linarith

/-- Absolute continuity of the Lebesgue integral:
    ∫ t in Icc 0 x, g t → 0 as x → 0⁺ when g ≥ 0 is integrable on Icc 0 1.
    This follows from continuity of the indefinite set-integral primitive;
    nonnegativity is not needed for this stronger library result. -/
lemma tendsto_setIntegral_Icc_zero
    (g : ℝ → ℝ)
    (hg_nn : 0 ≤ g)
    (hg : IntegrableOn g (Icc (0 : ℝ) 1) volume) :
    Tendsto (fun x => ∫ t in Icc (0 : ℝ) x, g t ∂volume)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  clear hg_nn
  -- Routed around the explicit DCT assembly using Mathlib's already-proved
  -- continuity of the set-integral primitive.
  have hcont := intervalIntegral.continuousOn_primitive_Icc hg
  have hzero := hcont 0 (by simp : (0 : ℝ) ∈ Icc 0 1)
  have hIic : Iic (1 : ℝ) ∈ nhds 0 := Iic_mem_nhds zero_lt_one
  have heq : nhdsWithin 0 (Ioi (0 : ℝ) ∩ Iic 1) = nhdsWithin 0 (Ioi 0) :=
    nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds hIic)
  rw [← heq]
  have hsub : Ioi (0 : ℝ) ∩ Iic 1 ⊆ Icc 0 1 := by
    intro x hx
    exact ⟨hx.1.le, hx.2⟩
  simpa using hzero.mono_left (nhdsWithin_mono 0 hsub)

/-- Cauchy-Schwarz bound: for x ∈ (0,1],
    |∫ t in Icc 0 x, deriv f t| ≤ √x · (∫ t in Icc 0 x, |deriv f t|²)^{1/2}.
    The proof applies Mathlib's p=q=2 Hölder inequality on the restricted
    measure, following the `MemLp` setup used by sibling a02J01. -/
lemma cauchy_schwarz_bound (f : ℝ → ℝ) (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hf_deriv_sq :
      IntegrableOn (fun x ↦ |deriv f x| ^ 2) (Icc (0 : ℝ) 1) volume) :
    |∫ t in Icc (0 : ℝ) x, deriv f t ∂volume| ≤
      Real.sqrt x * Real.sqrt (∫ t in Icc (0 : ℝ) x, |deriv f t| ^ 2 ∂volume) := by
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) x)
  have hsub : Icc (0 : ℝ) x ⊆ Icc (0 : ℝ) 1 :=
    Icc_subset_Icc_right hx1
  have hsq_int : Integrable (fun t => |deriv f t| ^ 2) μ :=
    hf_deriv_sq.mono_set hsub
  have habs_meas : AEStronglyMeasurable (fun t => |deriv f t|) μ := by
    exact hsq_int.1.aemeasurable.sqrt.aestronglyMeasurable.congr
      (ae_of_all _ fun t => by simp [Real.sqrt_sq_eq_abs])
  have habs_mem : MemLp (fun t => |deriv f t|) 2 μ := by
    rw [memLp_two_iff_integrable_sq habs_meas]
    exact hsq_int
  have habs_mem' : MemLp (fun t => |deriv f t|) (ENNReal.ofReal 2) μ := by
    norm_num
    exact habs_mem
  have hone_mem : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal 2) μ :=
    memLp_const 1
  have hholder :=
    integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := μ) (f := fun t => |deriv f t|) (g := fun _ : ℝ => 1)
      Real.HolderConjugate.two_two
      (ae_of_all _ fun _ => abs_nonneg _) (ae_of_all _ fun _ => zero_le_one)
      habs_mem' hone_mem
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hholder
  have hone : (∫ _ : ℝ, (1 : ℝ) ^ (2 : ℝ) ∂μ) = x := by
    simp [μ, hx0.le]
  have habs :
      (∫ t : ℝ, |deriv f t| ^ (2 : ℝ) ∂μ) =
        ∫ t in Icc (0 : ℝ) x, |deriv f t| ^ 2 ∂volume := by
    congr 1
    funext t
    norm_num
  have hnorm := norm_integral_le_integral_norm (μ := μ) (fun t => deriv f t)
  change |∫ t in Icc (0 : ℝ) x, deriv f t ∂volume| ≤ _
  calc
    |∫ t, deriv f t ∂μ| ≤ ∫ t, ‖deriv f t‖ ∂μ := hnorm
    _ = ∫ t, |deriv f t| * 1 ∂μ := by simp [Real.norm_eq_abs]
    _ ≤ Real.sqrt (∫ t, |deriv f t| ^ (2 : ℝ) ∂μ) *
          Real.sqrt (∫ _ : ℝ, (1 : ℝ) ^ (2 : ℝ) ∂μ) := hholder
    _ = Real.sqrt x *
          Real.sqrt (∫ t in Icc (0 : ℝ) x, |deriv f t| ^ 2 ∂volume) := by
      rw [hone, habs, mul_comm]

theorem apm_a00j02
    (f : ℝ → ℝ)
    (hf_ac : AbsolutelyContinuousOnInterval f 0 1)
    (hf_zero : f 0 = 0)
    (hf_deriv_sq :
      IntegrableOn (fun x ↦ |deriv f x| ^ 2) (Icc (0 : ℝ) 1) volume) :
    Tendsto (fun x ↦ f x / Real.sqrt x)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  let G : ℝ → ℝ := fun x =>
    ∫ t in Icc (0 : ℝ) x, |deriv f t| ^ 2 ∂volume
  have hG : Tendsto G (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    tendsto_setIntegral_Icc_zero (fun t => |deriv f t| ^ 2)
      (fun _ => sq_nonneg _) hf_deriv_sq
  have hsqrt : Tendsto (fun x => Real.sqrt (G x))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using (Real.continuous_sqrt.tendsto 0).comp hG
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg (f x / Real.sqrt x)) ?_ hsqrt
  have hlt1 : Iio (1 : ℝ) ∈ nhds 0 := Iio_mem_nhds zero_lt_one
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds hlt1] with x hx hxo1
  have hx0 : 0 < x := hx
  have hx1 : x ≤ 1 := hxo1.le
  have hfx : f x = ∫ t in Icc (0 : ℝ) x, deriv f t ∂volume := by
    calc
      f x = ∫ t in (0 : ℝ)..x, deriv f t := ftc_a00j02 f hf_ac hf_zero x hx0.le hx1
      _ = ∫ t in Icc (0 : ℝ) x, deriv f t ∂volume := by
        rw [intervalIntegral.integral_of_le hx0.le, integral_Icc_eq_integral_Ioc]
  have hcs := cauchy_schwarz_bound f x hx0 hx1 hf_deriv_sq
  have hspos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  rw [Real.norm_eq_abs, hfx, abs_div, abs_of_pos hspos]
  exact (div_le_iff₀ hspos).2 (by simpa [G, mul_comm] using hcs)

end
