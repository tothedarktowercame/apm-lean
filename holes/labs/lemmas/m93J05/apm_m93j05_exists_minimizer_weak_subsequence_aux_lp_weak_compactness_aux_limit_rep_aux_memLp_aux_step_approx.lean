import Mathlib

open MeasureTheory Filter

/-! Revised 2026-10-13: part (c)'s lower semicontinuity was encoded backwards, as
`(∀ᶠ n, r ≤ J (s n)) → r ≤ J f`, i.e. `liminf J(sₙ) ≤ J f`, false for weakly convergent sequences
(sₙ = sin (2π (N+n) x) ⇀ 0, J(sₙ) ≥ c > 0 = J 0 with g = 0). It now reads
`(∃ᶠ n, J (s n) ≤ r) → J f ≤ r`, i.e. `J f ≤ liminf J(sₙ)`. -/

noncomputable def apm_m93j05_cosCoeff (f : ℝ → ℝ) (j : ℕ) : ℝ :=
  2 * ∫ θ in Set.Icc (0 : ℝ) 1, f θ * Real.cos (j * 2 * Real.pi * θ)

noncomputable def apm_m93j05_sinCoeff (f : ℝ → ℝ) (j : ℕ) : ℝ :=
  2 * ∫ θ in Set.Icc (0 : ℝ) 1, f θ * Real.sin (j * 2 * Real.pi * θ)

noncomputable def apm_m93j05_trunc (N : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := fun θ =>
  (∫ x in Set.Icc (0 : ℝ) 1, f x) +
    ∑ j ∈ Finset.Icc 1 N,
      (apm_m93j05_cosCoeff f j * Real.cos (j * 2 * Real.pi * θ) +
       apm_m93j05_sinCoeff f j * Real.sin (j * 2 * Real.pi * θ))

noncomputable def apm_m93j05_J (N : ℕ) (p : ℝ) (g f : ℝ → ℝ) : ℝ :=
  Real.rpow (eLpNorm (fun x => f x - apm_m93j05_trunc N f x)
      (ENNReal.ofReal p) (volume.restrict (Set.Icc 0 1))).toReal p +
    (eLpNorm (apm_m93j05_trunc N f) 2
      (volume.restrict (Set.Icc 0 1))).toReal ^ 2 +
    ∫ x in Set.Icc (0 : ℝ) 1, f x * g x

lemma apm_m93j05_fourier_projection_aux_integral_Icc_eq_interval
    (f : ℝ → ℝ) :
    (∫ x in Set.Icc (0 : ℝ) 1, f x) = ∫ x in (0 : ℝ)..1, f x := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le zero_le_one]

lemma apm_m93j05_fourier_projection_aux_cos_mean_zero
    (j : ℕ) (hj : j ≠ 0) :
    ∫ x in Set.Icc (0 : ℝ) 1, Real.cos (j * 2 * Real.pi * x) = 0 := by
  rw [apm_m93j05_fourier_projection_aux_integral_Icc_eq_interval]
  let a : ℝ := j * 2 * Real.pi
  have ha : a ≠ 0 := by
    dsimp [a]
    positivity
  have hd : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Real.sin (a * y) / a)
      (Real.cos (a * x)) x := by
    intro x
    convert ((Real.hasDerivAt_sin (a * x)).comp x
      ((hasDerivAt_id x).const_mul a)).div_const a using 1
    field_simp
  change (∫ x in (0 : ℝ)..1, Real.cos (a * x)) = 0
  have hi := intervalIntegral.integral_deriv_eq_sub'
    (a := 0) (b := 1)
    (fun x : ℝ => Real.sin (a * x) / a)
    (funext fun x => (hd x).deriv) (fun x hx => (hd x).differentiableAt)
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
  rw [hi]
  dsimp [a]
  have hz : Real.sin ((j : ℝ) * 2 * Real.pi) = 0 := by
    convert Real.sin_nat_mul_pi (2 * j) using 1 <;> push_cast <;> ring
  simp [hz]

lemma apm_m93j05_fourier_projection_aux_sin_mean_zero
    (j : ℕ) :
    ∫ x in Set.Icc (0 : ℝ) 1, Real.sin (j * 2 * Real.pi * x) = 0 := by
  by_cases hj : j = 0
  · subst j
    simp
  rw [apm_m93j05_fourier_projection_aux_integral_Icc_eq_interval]
  let a : ℝ := j * 2 * Real.pi
  have ha : a ≠ 0 := by
    dsimp [a]
    positivity
  have hd : ∀ x : ℝ, HasDerivAt (fun y : ℝ => -Real.cos (a * y) / a)
      (Real.sin (a * x)) x := by
    intro x
    convert ((Real.hasDerivAt_cos (a * x)).comp x
      ((hasDerivAt_id x).const_mul a)).neg.div_const a using 1
    field_simp
  change (∫ x in (0 : ℝ)..1, Real.sin (a * x)) = 0
  have hi := intervalIntegral.integral_deriv_eq_sub'
    (a := 0) (b := 1)
    (fun x : ℝ => -Real.cos (a * x) / a)
    (funext fun x => (hd x).deriv) (fun x hx => (hd x).differentiableAt)
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  rw [hi]
  dsimp [a]
  have hc : Real.cos ((j : ℝ) * 2 * Real.pi) = 1 := by
    convert Real.cos_nat_mul_two_pi j using 1 <;> ring
  simp [hc]

/-! ### Split of `apm_m93j05_fourier_projection` (claude-14, 2026-10-13, after a partial
round-2 attempt that banked the three helpers above). (O) and (S) are independent; (C) takes
(O) as a hypothesis, and (K), (Sp) take (C) as a hypothesis, so all five run in parallel. -/

/-- (O) Orthogonality of the trigonometric system on `[0,1]` for frequencies `j, k ≥ 1`. -/
lemma apm_m93j05_trig_orthogonality_aux_cos_int (n : ℤ) (hn : n ≠ 0) :
    (∫ x in Set.Icc (0 : ℝ) 1, Real.cos (n * (2 * Real.pi) * x)) = 0 := by
  rw [apm_m93j05_fourier_projection_aux_integral_Icc_eq_interval]
  let a : ℝ := n * (2 * Real.pi)
  have ha : a ≠ 0 := by dsimp [a]; positivity
  have hd : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Real.sin (a * y) / a)
      (Real.cos (a * x)) x := by
    intro x
    convert ((Real.hasDerivAt_sin (a * x)).comp x
      ((hasDerivAt_id x).const_mul a)).div_const a using 1
    field_simp
  change (∫ x in (0 : ℝ)..1, Real.cos (a * x)) = 0
  rw [intervalIntegral.integral_deriv_eq_sub' (a := 0) (b := 1)
    (fun x : ℝ => Real.sin (a * x) / a) (funext fun x => (hd x).deriv)
    (fun x hx => (hd x).differentiableAt)
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn]
  dsimp [a]
  have hs : Real.sin ((n : ℝ) * (2 * Real.pi)) = 0 := by
    rw [show (n : ℝ) * (2 * Real.pi) = (2 * n : ℤ) * Real.pi by push_cast; ring]
    exact Real.sin_int_mul_pi _
  simp [hs]

lemma apm_m93j05_trig_orthogonality_aux_sin_int (n : ℤ) :
    (∫ x in Set.Icc (0 : ℝ) 1, Real.sin (n * (2 * Real.pi) * x)) = 0 := by
  by_cases hn : n = 0
  · subst n; simp
  rw [apm_m93j05_fourier_projection_aux_integral_Icc_eq_interval]
  let a : ℝ := n * (2 * Real.pi)
  have ha : a ≠ 0 := by dsimp [a]; positivity
  have hd : ∀ x : ℝ, HasDerivAt (fun y : ℝ => -Real.cos (a * y) / a)
      (Real.sin (a * x)) x := by
    intro x
    convert ((Real.hasDerivAt_cos (a * x)).comp x
      ((hasDerivAt_id x).const_mul a)).neg.div_const a using 1
    field_simp
  change (∫ x in (0 : ℝ)..1, Real.sin (a * x)) = 0
  rw [intervalIntegral.integral_deriv_eq_sub' (a := 0) (b := 1)
    (fun x : ℝ => -Real.cos (a * x) / a) (funext fun x => (hd x).deriv)
    (fun x hx => (hd x).differentiableAt)
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn]
  dsimp [a]
  simp [Real.cos_int_mul_two_pi]

theorem apm_m93j05_trig_orthogonality (j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) :
    (∫ x in Set.Icc (0 : ℝ) 1, Real.cos (j * 2 * Real.pi * x) * Real.cos (k * 2 * Real.pi * x))
        = (if j = k then 1 / 2 else 0) ∧
    (∫ x in Set.Icc (0 : ℝ) 1, Real.sin (j * 2 * Real.pi * x) * Real.sin (k * 2 * Real.pi * x))
        = (if j = k then 1 / 2 else 0) ∧
    (∫ x in Set.Icc (0 : ℝ) 1, Real.cos (j * 2 * Real.pi * x) * Real.sin (k * 2 * Real.pi * x))
        = 0 := by
  have hj0 : j ≠ 0 := Nat.ne_of_gt hj
  have hk0 : k ≠ 0 := Nat.ne_of_gt hk
  have hsum : (j : ℤ) + k ≠ 0 := by omega
  have hcc : (fun x : ℝ => Real.cos (j * 2 * Real.pi * x) *
      Real.cos (k * 2 * Real.pi * x)) = fun x =>
      (Real.cos (((j : ℝ) - k) * (2 * Real.pi) * x) +
       Real.cos (((j : ℝ) + k) * (2 * Real.pi) * x)) / 2 := by
    funext x
    rw [show ((j : ℝ) - k) * (2 * Real.pi) * x =
        (j * 2 * Real.pi * x) - (k * 2 * Real.pi * x) by ring,
      show ((j : ℝ) + k) * (2 * Real.pi) * x =
        (j * 2 * Real.pi * x) + (k * 2 * Real.pi * x) by push_cast; ring,
      Real.cos_sub, Real.cos_add]
    ring
  have hss : (fun x : ℝ => Real.sin (j * 2 * Real.pi * x) *
      Real.sin (k * 2 * Real.pi * x)) = fun x =>
      (Real.cos (((j : ℝ) - k) * (2 * Real.pi) * x) -
       Real.cos (((j : ℝ) + k) * (2 * Real.pi) * x)) / 2 := by
    funext x
    rw [show ((j : ℝ) - k) * (2 * Real.pi) * x =
        (j * 2 * Real.pi * x) - (k * 2 * Real.pi * x) by ring,
      show ((j : ℝ) + k) * (2 * Real.pi) * x =
        (j * 2 * Real.pi * x) + (k * 2 * Real.pi * x) by push_cast; ring,
      Real.cos_sub, Real.cos_add]
    ring
  have hcs : (fun x : ℝ => Real.cos (j * 2 * Real.pi * x) *
      Real.sin (k * 2 * Real.pi * x)) = fun x =>
      (Real.sin (((j : ℝ) + k) * (2 * Real.pi) * x) -
       Real.sin (((j : ℝ) - k) * (2 * Real.pi) * x)) / 2 := by
    funext x
    rw [show ((j : ℝ) - k) * (2 * Real.pi) * x =
        (j * 2 * Real.pi * x) - (k * 2 * Real.pi * x) by ring,
      show ((j : ℝ) + k) * (2 * Real.pi) * x =
        (j * 2 * Real.pi * x) + (k * 2 * Real.pi * x) by push_cast; ring,
      Real.sin_sub, Real.sin_add]
    ring
  rw [hcc, hss, hcs]
  have hcplus : (∫ x in Set.Icc (0 : ℝ) 1,
      Real.cos (((j : ℝ) + k) * (2 * Real.pi) * x)) = 0 := by
    simpa only [Int.cast_add, Int.cast_natCast] using
      apm_m93j05_trig_orthogonality_aux_cos_int ((j : ℤ) + k) hsum
  have hsplus : (∫ x in Set.Icc (0 : ℝ) 1,
      Real.sin (((j : ℝ) + k) * (2 * Real.pi) * x)) = 0 := by
    simpa only [Int.cast_add, Int.cast_natCast] using
      apm_m93j05_trig_orthogonality_aux_sin_int ((j : ℤ) + k)
  by_cases heq : j = k
  · subst k
    simp only [if_pos rfl, Int.cast_sub, Int.cast_natCast, sub_self, zero_mul,
      Real.cos_zero, one_div]
    rw [MeasureTheory.integral_div, MeasureTheory.integral_add,
      MeasureTheory.integral_div, MeasureTheory.integral_sub,
      MeasureTheory.integral_div, MeasureTheory.integral_sub]
    all_goals try exact (by fun_prop : Continuous _).integrableOn_Icc
    rw [hcplus, hsplus]
    norm_num
  · have hdiff : (j : ℤ) - k ≠ 0 := by omega
    have hcminus : (∫ x in Set.Icc (0 : ℝ) 1,
        Real.cos (((j : ℝ) - k) * (2 * Real.pi) * x)) = 0 := by
      simpa only [Int.cast_sub, Int.cast_natCast] using
        apm_m93j05_trig_orthogonality_aux_cos_int ((j : ℤ) - k) hdiff
    have hsminus : (∫ x in Set.Icc (0 : ℝ) 1,
        Real.sin (((j : ℝ) - k) * (2 * Real.pi) * x)) = 0 := by
      simpa only [Int.cast_sub, Int.cast_natCast] using
        apm_m93j05_trig_orthogonality_aux_sin_int ((j : ℤ) - k)
    simp only [if_neg heq]
    rw [MeasureTheory.integral_div, MeasureTheory.integral_add,
      MeasureTheory.integral_div, MeasureTheory.integral_sub,
      MeasureTheory.integral_div, MeasureTheory.integral_sub]
    all_goals try exact (by fun_prop : Continuous _).integrableOn_Icc
    rw [hcminus, hcplus, hsplus, hsminus]
    norm_num

/-- (C) Truncation keeps the mean and the coefficients `1 ≤ k ≤ N`, for every `f` (the truncation
is a finite trigonometric sum, so no integrability of `f` is needed). -/
theorem apm_m93j05_trunc_coeffs (N : ℕ)
    (hO : ∀ j k : ℕ, 1 ≤ j → 1 ≤ k →
      (∫ x in Set.Icc (0 : ℝ) 1, Real.cos (j * 2 * Real.pi * x) * Real.cos (k * 2 * Real.pi * x))
          = (if j = k then 1 / 2 else 0) ∧
      (∫ x in Set.Icc (0 : ℝ) 1, Real.sin (j * 2 * Real.pi * x) * Real.sin (k * 2 * Real.pi * x))
          = (if j = k then 1 / 2 else 0) ∧
      (∫ x in Set.Icc (0 : ℝ) 1, Real.cos (j * 2 * Real.pi * x) * Real.sin (k * 2 * Real.pi * x))
          = 0)
    (f : ℝ → ℝ) :
    (∫ x in Set.Icc (0 : ℝ) 1, apm_m93j05_trunc N f x) = ∫ x in Set.Icc (0 : ℝ) 1, f x ∧
    ∀ k ∈ Finset.Icc 1 N, apm_m93j05_cosCoeff (apm_m93j05_trunc N f) k = apm_m93j05_cosCoeff f k ∧ apm_m93j05_sinCoeff (apm_m93j05_trunc N f) k = apm_m93j05_sinCoeff f k := by
  let S := Finset.Icc 1 N
  let m := ∫ x in Set.Icc (0 : ℝ) 1, f x
  have htrig_int : ∀ j ∈ S, IntegrableOn (fun x : ℝ ↦
      apm_m93j05_cosCoeff f j * Real.cos (j * 2 * Real.pi * x) +
      apm_m93j05_sinCoeff f j * Real.sin (j * 2 * Real.pi * x)) (Set.Icc 0 1) := by
    intro j hj
    exact ((continuous_const.mul (Real.continuous_cos.comp
      (continuous_const.mul continuous_id))).add
      (continuous_const.mul (Real.continuous_sin.comp
        (continuous_const.mul continuous_id)))).integrableOn_Icc
  have hmean : (∫ x in Set.Icc (0 : ℝ) 1, apm_m93j05_trunc N f x) = m := by
    unfold apm_m93j05_trunc
    change (∫ x in Set.Icc (0 : ℝ) 1, m + ∑ j ∈ S,
      (apm_m93j05_cosCoeff f j * Real.cos (j * 2 * Real.pi * x) +
       apm_m93j05_sinCoeff f j * Real.sin (j * 2 * Real.pi * x))) = m
    rw [MeasureTheory.integral_add]
    · rw [MeasureTheory.integral_const, MeasureTheory.integral_finset_sum S]
      · have hz : ∑ j ∈ S, (∫ x in Set.Icc (0 : ℝ) 1,
            (apm_m93j05_cosCoeff f j * Real.cos (j * 2 * Real.pi * x) +
             apm_m93j05_sinCoeff f j * Real.sin (j * 2 * Real.pi * x))) = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
          rw [MeasureTheory.integral_add]
          · rw [MeasureTheory.integral_const_mul,
              MeasureTheory.integral_const_mul,
              apm_m93j05_fourier_projection_aux_cos_mean_zero j (by omega),
              apm_m93j05_fourier_projection_aux_sin_mean_zero j]
            ring
          · exact (continuous_const.mul (Real.continuous_cos.comp
              (continuous_const.mul continuous_id))).integrableOn_Icc
          · exact (continuous_const.mul (Real.continuous_sin.comp
              (continuous_const.mul continuous_id))).integrableOn_Icc
        rw [hz, add_zero]
        norm_num [Measure.real, Measure.restrict_apply_univ, Real.volume_Icc]
      · intro j hj
        exact htrig_int j hj
    · exact integrableOn_const (hs := measure_Icc_lt_top.ne)
    · exact MeasureTheory.integrable_finset_sum S htrig_int
  refine ⟨by simpa [m] using hmean, ?_⟩
  intro k hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hcos_int : IntegrableOn (fun x : ℝ ↦ Real.cos (k * 2 * Real.pi * x))
      (Set.Icc 0 1) := by
    exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).integrableOn_Icc
  have hsin_int : IntegrableOn (fun x : ℝ ↦ Real.sin (k * 2 * Real.pi * x))
      (Set.Icc 0 1) := by
    exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).integrableOn_Icc
  have hcos : apm_m93j05_cosCoeff (apm_m93j05_trunc N f) k =
      apm_m93j05_cosCoeff f k := by
    unfold apm_m93j05_cosCoeff apm_m93j05_trunc
    change 2 * (∫ x in Set.Icc (0 : ℝ) 1,
      (m + ∑ j ∈ S, (apm_m93j05_cosCoeff f j * Real.cos (j * 2 * Real.pi * x) +
        apm_m93j05_sinCoeff f j * Real.sin (j * 2 * Real.pi * x))) *
        Real.cos (k * 2 * Real.pi * x)) = apm_m93j05_cosCoeff f k
    have hp : (fun x : ℝ ↦
        (m + ∑ j ∈ S, (apm_m93j05_cosCoeff f j * Real.cos (j * 2 * Real.pi * x) +
          apm_m93j05_sinCoeff f j * Real.sin (j * 2 * Real.pi * x))) *
          Real.cos (k * 2 * Real.pi * x)) =
        fun x ↦ m * Real.cos (k * 2 * Real.pi * x) + ∑ j ∈ S,
          (apm_m93j05_cosCoeff f j *
              (Real.cos (j * 2 * Real.pi * x) * Real.cos (k * 2 * Real.pi * x)) +
           apm_m93j05_sinCoeff f j *
              (Real.sin (j * 2 * Real.pi * x) * Real.cos (k * 2 * Real.pi * x))) := by
      funext x
      rw [add_mul, Finset.sum_mul]
      apply congrArg (fun z : ℝ ↦ m * Real.cos (k * 2 * Real.pi * x) + z)
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hp, MeasureTheory.integral_add]
    · rw [MeasureTheory.integral_const_mul,
        apm_m93j05_fourier_projection_aux_cos_mean_zero k (by omega),
        MeasureTheory.integral_finset_sum S]
      · rw [Finset.sum_eq_single k]
        · rw [MeasureTheory.integral_add]
          · rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
              (hO k k hk1 hk1).1, if_pos rfl]
            have hcross := (hO k k hk1 hk1).2.2
            have hcross' : (∫ a in Set.Icc (0 : ℝ) 1,
                Real.sin (k * 2 * Real.pi * a) * Real.cos (k * 2 * Real.pi * a)) = 0 := by
              calc
                _ = ∫ a in Set.Icc (0 : ℝ) 1,
                    Real.cos (k * 2 * Real.pi * a) * Real.sin (k * 2 * Real.pi * a) := by
                      apply MeasureTheory.integral_congr_ae
                      filter_upwards with a
                      ring
                _ = 0 := hcross
            rw [hcross']
            ring
          · exact (continuous_const.mul ((Real.continuous_cos.comp
              (continuous_const.mul continuous_id)).mul (Real.continuous_cos.comp
                (continuous_const.mul continuous_id)))).integrableOn_Icc
          · exact (continuous_const.mul ((Real.continuous_sin.comp
              (continuous_const.mul continuous_id)).mul (Real.continuous_cos.comp
                (continuous_const.mul continuous_id)))).integrableOn_Icc
        · intro j hj hjne
          rw [MeasureTheory.integral_add]
          · rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
              (hO j k (Finset.mem_Icc.mp hj).1 hk1).1, if_neg hjne]
            have hc := (hO k j hk1 (Finset.mem_Icc.mp hj).1).2.2
            have hc' : (∫ a in Set.Icc (0 : ℝ) 1,
                Real.sin (j * 2 * Real.pi * a) * Real.cos (k * 2 * Real.pi * a)) = 0 := by
              calc
                _ = ∫ a in Set.Icc (0 : ℝ) 1,
                    Real.cos (k * 2 * Real.pi * a) * Real.sin (j * 2 * Real.pi * a) := by
                      apply MeasureTheory.integral_congr_ae
                      filter_upwards with a
                      ring
                _ = 0 := hc
            rw [hc']
            ring
          · exact (continuous_const.mul ((Real.continuous_cos.comp
              (continuous_const.mul continuous_id)).mul (Real.continuous_cos.comp
                (continuous_const.mul continuous_id)))).integrableOn_Icc
          · exact (continuous_const.mul ((Real.continuous_sin.comp
              (continuous_const.mul continuous_id)).mul (Real.continuous_cos.comp
                (continuous_const.mul continuous_id)))).integrableOn_Icc
        · intro hkn
          exact (hkn hk).elim
      · intro j hj
        exact ((continuous_const.mul ((Real.continuous_cos.comp
          (continuous_const.mul continuous_id)).mul (Real.continuous_cos.comp
            (continuous_const.mul continuous_id)))).add
          (continuous_const.mul ((Real.continuous_sin.comp
            (continuous_const.mul continuous_id)).mul (Real.continuous_cos.comp
              (continuous_const.mul continuous_id))))).integrableOn_Icc
    · exact (continuous_const.mul (Real.continuous_cos.comp
        (continuous_const.mul continuous_id))).integrableOn_Icc
    · apply MeasureTheory.integrable_finset_sum S
      intro j hj
      exact ((continuous_const.mul ((Real.continuous_cos.comp
        (continuous_const.mul continuous_id)).mul (Real.continuous_cos.comp
          (continuous_const.mul continuous_id)))).add
        (continuous_const.mul ((Real.continuous_sin.comp
          (continuous_const.mul continuous_id)).mul (Real.continuous_cos.comp
            (continuous_const.mul continuous_id))))).integrableOn_Icc
  have hsin : apm_m93j05_sinCoeff (apm_m93j05_trunc N f) k =
      apm_m93j05_sinCoeff f k := by
    unfold apm_m93j05_sinCoeff apm_m93j05_trunc
    change 2 * (∫ x in Set.Icc (0 : ℝ) 1,
      (m + ∑ j ∈ S, (apm_m93j05_cosCoeff f j * Real.cos (j * 2 * Real.pi * x) +
        apm_m93j05_sinCoeff f j * Real.sin (j * 2 * Real.pi * x))) *
        Real.sin (k * 2 * Real.pi * x)) = apm_m93j05_sinCoeff f k
    have hp : (fun x : ℝ ↦
        (m + ∑ j ∈ S, (apm_m93j05_cosCoeff f j * Real.cos (j * 2 * Real.pi * x) +
          apm_m93j05_sinCoeff f j * Real.sin (j * 2 * Real.pi * x))) *
          Real.sin (k * 2 * Real.pi * x)) =
        fun x ↦ m * Real.sin (k * 2 * Real.pi * x) + ∑ j ∈ S,
          (apm_m93j05_cosCoeff f j *
              (Real.cos (j * 2 * Real.pi * x) * Real.sin (k * 2 * Real.pi * x)) +
           apm_m93j05_sinCoeff f j *
              (Real.sin (j * 2 * Real.pi * x) * Real.sin (k * 2 * Real.pi * x))) := by
      funext x
      rw [add_mul, Finset.sum_mul]
      apply congrArg (fun z : ℝ ↦ m * Real.sin (k * 2 * Real.pi * x) + z)
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hp, MeasureTheory.integral_add]
    · rw [MeasureTheory.integral_const_mul,
        apm_m93j05_fourier_projection_aux_sin_mean_zero k,
        MeasureTheory.integral_finset_sum S]
      · rw [Finset.sum_eq_single k]
        · rw [MeasureTheory.integral_add]
          · rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
              (hO k k hk1 hk1).2.2, (hO k k hk1 hk1).2.1, if_pos rfl]
            ring
          · exact (continuous_const.mul ((Real.continuous_cos.comp
              (continuous_const.mul continuous_id)).mul (Real.continuous_sin.comp
                (continuous_const.mul continuous_id)))).integrableOn_Icc
          · exact (continuous_const.mul ((Real.continuous_sin.comp
              (continuous_const.mul continuous_id)).mul (Real.continuous_sin.comp
                (continuous_const.mul continuous_id)))).integrableOn_Icc
        · intro j hj hjne
          rw [MeasureTheory.integral_add]
          · rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
              (hO j k (Finset.mem_Icc.mp hj).1 hk1).2.2,
              (hO j k (Finset.mem_Icc.mp hj).1 hk1).2.1, if_neg hjne]
            ring
          · exact (continuous_const.mul ((Real.continuous_cos.comp
              (continuous_const.mul continuous_id)).mul (Real.continuous_sin.comp
                (continuous_const.mul continuous_id)))).integrableOn_Icc
          · exact (continuous_const.mul ((Real.continuous_sin.comp
              (continuous_const.mul continuous_id)).mul (Real.continuous_sin.comp
                (continuous_const.mul continuous_id)))).integrableOn_Icc
        · intro hkn
          exact (hkn hk).elim
      · intro j hj
        exact ((continuous_const.mul ((Real.continuous_cos.comp
          (continuous_const.mul continuous_id)).mul (Real.continuous_sin.comp
            (continuous_const.mul continuous_id)))).add
          (continuous_const.mul ((Real.continuous_sin.comp
            (continuous_const.mul continuous_id)).mul (Real.continuous_sin.comp
              (continuous_const.mul continuous_id))))).integrableOn_Icc
    · exact (continuous_const.mul (Real.continuous_sin.comp
        (continuous_const.mul continuous_id))).integrableOn_Icc
    · apply MeasureTheory.integrable_finset_sum S
      intro j hj
      exact ((continuous_const.mul ((Real.continuous_cos.comp
        (continuous_const.mul continuous_id)).mul (Real.continuous_sin.comp
          (continuous_const.mul continuous_id)))).add
        (continuous_const.mul ((Real.continuous_sin.comp
          (continuous_const.mul continuous_id)).mul (Real.continuous_sin.comp
            (continuous_const.mul continuous_id))))).integrableOn_Icc
  exact ⟨hcos, hsin⟩

/-- (S) Self-adjointness: both sides equal `m_f m_g + Σ (a_j(f) a_j(g) + b_j(f) b_j(g)) / 2`. -/
theorem apm_m93j05_trunc_selfAdjoint (N : ℕ) (p q : ℝ) (hp : 1 < p) (hq : 1 < q)
    (f g : ℝ → ℝ) (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hg : MemLp g (ENNReal.ofReal q) (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    ∫ x, apm_m93j05_trunc N f x * g x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) =
      ∫ x, f x * apm_m93j05_trunc N g x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  let μ := volume.restrict (Set.Icc (0 : ℝ) 1)
  have hfi : Integrable f μ := hf.integrable (by
    rw [ENNReal.one_le_ofReal]
    linarith)
  have hgi : Integrable g μ := hg.integrable (by
    rw [ENNReal.one_le_ofReal]
    linarith)
  have hcos (h : ℝ → ℝ) (hh : Integrable h μ) (j : ℕ) :
      Integrable (fun x ↦ Real.cos (j * 2 * Real.pi * x) * h x) μ := by
    exact hh.bdd_mul
      ((Real.continuous_cos.comp
        (continuous_const.mul continuous_const |>.mul continuous_const |>.mul
          continuous_id)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (j * 2 * Real.pi * x))
  have hsin (h : ℝ → ℝ) (hh : Integrable h μ) (j : ℕ) :
      Integrable (fun x ↦ Real.sin (j * 2 * Real.pi * x) * h x) μ := by
    exact hh.bdd_mul
      ((Real.continuous_sin.comp
        (continuous_const.mul continuous_const |>.mul continuous_const |>.mul
          continuous_id)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (j * 2 * Real.pi * x))
  have hexpand (a b : ℝ → ℝ) (hb : Integrable b μ) :
      (∫ x, apm_m93j05_trunc N a x * b x ∂μ) =
        (∫ x, a x ∂μ) * (∫ x, b x ∂μ) +
          ∑ j ∈ Finset.Icc 1 N,
            (apm_m93j05_cosCoeff a j *
                ∫ x, Real.cos (j * 2 * Real.pi * x) * b x ∂μ +
              apm_m93j05_sinCoeff a j *
                ∫ x, Real.sin (j * 2 * Real.pi * x) * b x ∂μ) := by
    unfold apm_m93j05_trunc
    simp_rw [add_mul, Finset.sum_mul]
    rw [MeasureTheory.integral_add]
    · rw [MeasureTheory.integral_const_mul]
      rw [MeasureTheory.integral_finset_sum]
      · apply congrArg
          (fun z => (∫ x, a x ∂μ) * ∫ x, b x ∂μ + z)
        apply Finset.sum_congr rfl
        intro j hj
        rw [show (fun x =>
            (apm_m93j05_cosCoeff a j * Real.cos (j * 2 * Real.pi * x) +
              apm_m93j05_sinCoeff a j * Real.sin (j * 2 * Real.pi * x)) * b x) =
            (fun x => apm_m93j05_cosCoeff a j *
                (Real.cos (j * 2 * Real.pi * x) * b x) +
              apm_m93j05_sinCoeff a j *
                (Real.sin (j * 2 * Real.pi * x) * b x)) by
          funext x; ring]
        rw [MeasureTheory.integral_add]
        · simp_rw [mul_assoc]
          rw [MeasureTheory.integral_const_mul,
            MeasureTheory.integral_const_mul]
        · exact (hcos b hb j).const_mul _
        · exact (hsin b hb j).const_mul _
      · intro j hj
        rw [show (fun x =>
            (apm_m93j05_cosCoeff a j * Real.cos (j * 2 * Real.pi * x) +
              apm_m93j05_sinCoeff a j * Real.sin (j * 2 * Real.pi * x)) * b x) =
            (fun x => apm_m93j05_cosCoeff a j *
                (Real.cos (j * 2 * Real.pi * x) * b x) +
              apm_m93j05_sinCoeff a j *
                (Real.sin (j * 2 * Real.pi * x) * b x)) by
          funext x; ring]
        exact ((hcos b hb j).const_mul _).add ((hsin b hb j).const_mul _)
    · exact hb.const_mul _
    · apply integrable_finset_sum
      intro j hj
      rw [show (fun x =>
          (apm_m93j05_cosCoeff a j * Real.cos (j * 2 * Real.pi * x) +
            apm_m93j05_sinCoeff a j * Real.sin (j * 2 * Real.pi * x)) * b x) =
          (fun x => apm_m93j05_cosCoeff a j *
              (Real.cos (j * 2 * Real.pi * x) * b x) +
            apm_m93j05_sinCoeff a j *
              (Real.sin (j * 2 * Real.pi * x) * b x)) by
        funext x; ring]
      exact ((hcos b hb j).const_mul _).add ((hsin b hb j).const_mul _)
  rw [hexpand f g hgi]
  have hright : (∫ x, f x * apm_m93j05_trunc N g x ∂μ) =
      (∫ x, apm_m93j05_trunc N g x * f x ∂μ) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    ring
  rw [hright, hexpand g f hfi]
  have hcos_sym (a : ℝ → ℝ) (j : ℕ) :
      (∫ x, Real.cos (j * 2 * Real.pi * x) * a x ∂μ) =
        ∫ x, a x * Real.cos (j * 2 * Real.pi * x) ∂μ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    ring
  have hsin_sym (a : ℝ → ℝ) (j : ℕ) :
      (∫ x, Real.sin (j * 2 * Real.pi * x) * a x ∂μ) =
        ∫ x, a x * Real.sin (j * 2 * Real.pi * x) ∂μ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    ring
  simp_rw [hcos_sym, hsin_sym]
  unfold apm_m93j05_cosCoeff apm_m93j05_sinCoeff
  dsimp [μ]
  rw [mul_comm (∫ x in Set.Icc (0 : ℝ) 1, f x)
    (∫ x in Set.Icc (0 : ℝ) 1, g x)]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hc (a : ℝ → ℝ) :
      (∫ x in Set.Icc (0 : ℝ) 1,
        a x * Real.cos (j * 2 * Real.pi * x)) =
      ∫ x in Set.Icc (0 : ℝ) 1,
        a x * Real.cos (Real.pi * j * x * 2) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    congr 2
    push_cast
    ring
  have hs (a : ℝ → ℝ) :
      (∫ x in Set.Icc (0 : ℝ) 1,
        a x * Real.sin (j * 2 * Real.pi * x)) =
      ∫ x in Set.Icc (0 : ℝ) 1,
        a x * Real.sin (Real.pi * j * x * 2) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    congr 2
    push_cast
    ring
  rw [hc f, hc g, hs f, hs g]
  ring

/-- (K) Kernel: `Φ f = 0` iff the mean and the coefficients up to `N` vanish. -/
theorem apm_m93j05_trunc_kernel (N : ℕ)
    (hC : ∀ f : ℝ → ℝ,
      (∫ x in Set.Icc (0 : ℝ) 1, apm_m93j05_trunc N f x) = ∫ x in Set.Icc (0 : ℝ) 1, f x ∧
      ∀ k ∈ Finset.Icc 1 N, apm_m93j05_cosCoeff (apm_m93j05_trunc N f) k = apm_m93j05_cosCoeff f k ∧ apm_m93j05_sinCoeff (apm_m93j05_trunc N f) k = apm_m93j05_sinCoeff f k)
    (f : ℝ → ℝ) :
    apm_m93j05_trunc N f = 0 ↔
      (∫ x in Set.Icc (0 : ℝ) 1, f x = 0 ∧
       ∀ j ∈ Finset.Icc 1 N, apm_m93j05_cosCoeff f j = 0 ∧ apm_m93j05_sinCoeff f j = 0) := by
  constructor
  · intro hzero
    have hdata := hC f
    constructor
    · rw [← hdata.1, hzero]
      simp
    · intro j hj
      have hjdata := hdata.2 j hj
      constructor
      · rw [← hjdata.1, hzero]
        simp [apm_m93j05_cosCoeff]
      · rw [← hjdata.2, hzero]
        simp [apm_m93j05_sinCoeff]
  · rintro ⟨hmean, hcoeff⟩
    funext x
    simp only [apm_m93j05_trunc, Pi.zero_apply]
    rw [hmean]
    simp only [zero_add]
    apply Finset.sum_eq_zero
    intro j hj
    rw [(hcoeff j hj).1, (hcoeff j hj).2]
    ring

/-- (Sp) Splitting `f = Φ f + (f − Φ f)`. For `Φ (f − Φ f) = 0`: if `f · cos_k` is integrable the
coefficients subtract; if not, neither is `(f − Φ f) · cos_k`, and both coefficients are `0`. -/
lemma apm_m93j05_trunc_split_aux_continuous (N : ℕ) (f : ℝ → ℝ) :
    Continuous (apm_m93j05_trunc N f) := by
  apply Continuous.add continuous_const
  apply continuous_finset_sum
  intro j hj
  apply Continuous.add
  · exact continuous_const.mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  · exact continuous_const.mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))

lemma apm_m93j05_trunc_split_aux_integral_sub (f g : ℝ → ℝ)
    (hg : IntegrableOn g (Set.Icc (0 : ℝ) 1))
    (heq : (∫ x in Set.Icc (0 : ℝ) 1, f x) =
      ∫ x in Set.Icc (0 : ℝ) 1, g x) :
    (∫ x in Set.Icc (0 : ℝ) 1, (f x - g x)) = 0 := by
  let μ := volume.restrict (Set.Icc (0 : ℝ) 1)
  change (∫ x, f x - g x ∂μ) = 0
  by_cases hf : Integrable f μ
  · rw [integral_sub hf hg, heq, sub_self]
  · have hfg : ¬ Integrable (fun x => f x - g x) μ := by
      intro h
      apply hf
      have := h.add hg
      exact this.congr (ae_of_all _ fun x => by simp)
    exact integral_undef hfg

theorem apm_m93j05_trunc_split (N : ℕ)
    (hC : ∀ f : ℝ → ℝ,
      (∫ x in Set.Icc (0 : ℝ) 1, apm_m93j05_trunc N f x) = ∫ x in Set.Icc (0 : ℝ) 1, f x ∧
      ∀ k ∈ Finset.Icc 1 N, apm_m93j05_cosCoeff (apm_m93j05_trunc N f) k = apm_m93j05_cosCoeff f k ∧ apm_m93j05_sinCoeff (apm_m93j05_trunc N f) k = apm_m93j05_sinCoeff f k)
    (f : ℝ → ℝ) :
    ∃ u v, f = u + v ∧ apm_m93j05_trunc N u = u ∧ apm_m93j05_trunc N v = 0 := by
  let u := apm_m93j05_trunc N f
  let v := f - u
  refine ⟨u, v, ?_, ?_, ?_⟩
  · funext x
    simp [v]
  · funext x
    simp only [apm_m93j05_trunc]
    rw [(hC f).1]
    apply congrArg₂ (· + ·) rfl
    apply Finset.sum_congr rfl
    intro j hj
    rw [(hC f).2 j hj |>.1, (hC f).2 j hj |>.2]
  · funext x
    simp only [apm_m93j05_trunc, Pi.zero_apply]
    have hu : Continuous u := apm_m93j05_trunc_split_aux_continuous N f
    have huI : IntegrableOn u (Set.Icc (0 : ℝ) 1) := hu.continuousOn.integrableOn_Icc
    have hmean : (∫ y in Set.Icc (0 : ℝ) 1, v y) = 0 := by
      rw [show (fun y => v y) = fun y => f y - u y by rfl,
        apm_m93j05_trunc_split_aux_integral_sub f u huI (hC f).1.symm]
    rw [hmean, zero_add]
    apply Finset.sum_eq_zero
    intro j hj
    have hcosI : IntegrableOn (fun y => u y * Real.cos (j * 2 * Real.pi * y))
        (Set.Icc (0 : ℝ) 1) :=
      (hu.mul (Real.continuous_cos.comp
        (continuous_const.mul continuous_id))).continuousOn.integrableOn_Icc
    have hsinI : IntegrableOn (fun y => u y * Real.sin (j * 2 * Real.pi * y))
        (Set.Icc (0 : ℝ) 1) :=
      (hu.mul (Real.continuous_sin.comp
        (continuous_const.mul continuous_id))).continuousOn.integrableOn_Icc
    have hc : apm_m93j05_cosCoeff v j = 0 := by
      have hh : apm_m93j05_cosCoeff u j = apm_m93j05_cosCoeff f j := by
        simpa [u] using ((hC f).2 j hj).1
      unfold apm_m93j05_cosCoeff at hh
      unfold apm_m93j05_cosCoeff
      rw [show (fun y => v y * Real.cos (j * 2 * Real.pi * y)) =
          fun y => f y * Real.cos (j * 2 * Real.pi * y) -
            u y * Real.cos (j * 2 * Real.pi * y) by funext y; simp [v]; ring,
        apm_m93j05_trunc_split_aux_integral_sub _ _ hcosI (by nlinarith [hh])]
      norm_num
    have hs : apm_m93j05_sinCoeff v j = 0 := by
      have hh : apm_m93j05_sinCoeff u j = apm_m93j05_sinCoeff f j := by
        simpa [u] using ((hC f).2 j hj).2
      unfold apm_m93j05_sinCoeff at hh
      unfold apm_m93j05_sinCoeff
      rw [show (fun y => v y * Real.sin (j * 2 * Real.pi * y)) =
          fun y => f y * Real.sin (j * 2 * Real.pi * y) -
            u y * Real.sin (j * 2 * Real.pi * y) by funext y; simp [v]; ring,
        apm_m93j05_trunc_split_aux_integral_sub _ _ hsinI (by nlinarith [hh])]
      norm_num
    simp [hc, hs]

theorem apm_m93j05_fourier_projection
    (N : ℕ) (p q : ℝ) (hp : 1 < p) (hq : 1 < q)
    (hpq : 1 / p + 1 / q = 1) :
    let μ := volume.restrict (Set.Icc (0 : ℝ) 1)
    let Φ := apm_m93j05_trunc N
    (∀ f g, MemLp f (ENNReal.ofReal p) μ → MemLp g (ENNReal.ofReal q) μ →
      ∫ x, Φ f x * g x ∂μ = ∫ x, f x * Φ g x ∂μ) ∧
    (∀ f, Φ f = 0 ↔
      (∫ x in Set.Icc (0 : ℝ) 1, f x = 0 ∧
       ∀ j ∈ Finset.Icc 1 N,
         apm_m93j05_cosCoeff f j = 0 ∧ apm_m93j05_sinCoeff f j = 0)) ∧
    (∀ f, ∃ u v, f = u + v ∧ Φ u = u ∧ Φ v = 0) := by
  intro μ Φ
  have hC := apm_m93j05_trunc_coeffs N
    (fun j k hj hk ↦ apm_m93j05_trig_orthogonality j k hj hk)
  exact ⟨fun f g hf hg ↦ apm_m93j05_trunc_selfAdjoint N p q hp hq f g hf hg,
    fun f ↦ apm_m93j05_trunc_kernel N hC f,
    fun f ↦ apm_m93j05_trunc_split N hC f⟩

lemma apm_m93j05_weak_lowerSemicontinuous_aux_pairing
    {q : ℝ} {μ : Measure ℝ} (g f : ℝ → ℝ) (s : ℕ → ℝ → ℝ)
    (hg : MemLp g (ENNReal.ofReal q) μ)
    (hweak : ∀ h, MemLp h (ENNReal.ofReal q) μ →
      Tendsto (fun n => ∫ x, s n x * h x ∂μ) atTop
        (nhds (∫ x, f x * h x ∂μ))) :
    Tendsto (fun n => ∫ x, s n x * g x ∂μ) atTop
      (nhds (∫ x, f x * g x ∂μ)) :=
  hweak g hg

lemma apm_m93j05_weak_lowerSemicontinuous_aux_cos_memLp
    (q : ℝ) (j : ℕ) :
    MemLp (fun x : ℝ => Real.cos (j * 2 * Real.pi * x)) (ENNReal.ofReal q)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  apply MemLp.of_bound
  · exact (Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).aestronglyMeasurable
  · filter_upwards [] with x
    simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (j * 2 * Real.pi * x)

lemma apm_m93j05_weak_lowerSemicontinuous_aux_sin_memLp
    (q : ℝ) (j : ℕ) :
    MemLp (fun x : ℝ => Real.sin (j * 2 * Real.pi * x)) (ENNReal.ofReal q)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  apply MemLp.of_bound
  · exact (Real.continuous_sin.comp
      (continuous_const.mul continuous_id)).aestronglyMeasurable
  · filter_upwards [] with x
    simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (j * 2 * Real.pi * x)

/-! Split of `apm_m93j05_weak_lowerSemicontinuous` (claude-14, after a second partial that banked the cos/sin `Lq` helpers):
(L1) truncation energies converge, (L2) weak lower semicontinuity of `‖·‖ₚᵖ` (generic, via the
norming dual function), (L3) the high-mode parts converge weakly, (L4) combine. Parallel. -/

lemma apm_m93j05_trunc_energy_tendsto_aux_coeffs
    (N q : ℝ) (f : ℝ → ℝ) (s : ℕ → ℝ → ℝ)
    (hweak : ∀ h, MemLp h (ENNReal.ofReal q)
        (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      Tendsto (fun n ↦ ∫ x, s n x * h x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
        atTop (nhds (∫ x, f x * h x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))))) :
    Tendsto (fun n ↦ ∫ x in Set.Icc (0 : ℝ) 1, s n x) atTop
        (nhds (∫ x in Set.Icc (0 : ℝ) 1, f x)) ∧
      (∀ j : ℕ, Tendsto (fun n ↦ apm_m93j05_cosCoeff (s n) j) atTop
        (nhds (apm_m93j05_cosCoeff f j))) ∧
      ∀ j : ℕ, Tendsto (fun n ↦ apm_m93j05_sinCoeff (s n) j) atTop
        (nhds (apm_m93j05_sinCoeff f j)) := by
  have hone : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal q)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    apply MemLp.of_bound (C := (1 : ℝ))
    · exact aestronglyMeasurable_const
    · filter_upwards [] with x
      norm_num
  refine ⟨?_, ?_, ?_⟩
  · simpa using hweak (fun _ : ℝ => (1 : ℝ)) hone
  · intro j
    simpa [apm_m93j05_cosCoeff] using
      (hweak (fun x : ℝ => Real.cos (j * 2 * Real.pi * x))
        (apm_m93j05_weak_lowerSemicontinuous_aux_cos_memLp q j)).const_mul 2
  · intro j
    simpa [apm_m93j05_sinCoeff] using
      (hweak (fun x : ℝ => Real.sin (j * 2 * Real.pi * x))
        (apm_m93j05_weak_lowerSemicontinuous_aux_sin_memLp q j)).const_mul 2

lemma apm_m93j05_trunc_parseval_aux_norm_sq (N : ℕ) (f : ℝ → ℝ) :
    (eLpNorm (apm_m93j05_trunc N f) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 =
      ∫ x in Set.Icc (0 : ℝ) 1,
        apm_m93j05_trunc N f x * apm_m93j05_trunc N f x := by
  let μ := volume.restrict (Set.Icc (0 : ℝ) 1)
  let g := apm_m93j05_trunc N f
  have hgcont : Continuous g := apm_m93j05_trunc_split_aux_continuous N f
  have hg : MemLp g 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hgcont.aestronglyMeasurable]
    exact (hgcont.norm.pow 2).continuousOn.integrableOn_Icc
  let G : Lp ℝ 2 μ := hg.toLp g
  rw [← Lp.norm_toLp g hg]
  rw [← real_inner_self_eq_norm_sq G, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp, hg.coeFn_toLp] with x hx₁ hx₂
  rw [real_inner_self_eq_norm_sq]
  simp only [Real.norm_eq_abs, sq_abs]
  rw [hx₁]
  simp [g, pow_two]

lemma apm_m93j05_trunc_parseval_aux_mean (a b : ℝ) (j : ℕ) (hj : 1 ≤ j) :
    (∫ x in Set.Icc (0 : ℝ) 1,
      (a * Real.cos (j * 2 * Real.pi * x) +
       b * Real.sin (j * 2 * Real.pi * x))) = 0 := by
  rw [MeasureTheory.integral_add]
  · rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      apm_m93j05_fourier_projection_aux_cos_mean_zero j (by omega),
      apm_m93j05_fourier_projection_aux_sin_mean_zero j]
    ring
  · exact (continuous_const.mul (Real.continuous_cos.comp
      (continuous_const.mul continuous_id))).integrableOn_Icc
  · exact (continuous_const.mul (Real.continuous_sin.comp
      (continuous_const.mul continuous_id))).integrableOn_Icc

lemma apm_m93j05_trunc_parseval_aux_inner (a b c d : ℝ) (j k : ℕ)
    (hj : 1 ≤ j) (hk : 1 ≤ k) :
    (∫ x in Set.Icc (0 : ℝ) 1,
      (a * Real.cos (j * 2 * Real.pi * x) + b * Real.sin (j * 2 * Real.pi * x)) *
      (c * Real.cos (k * 2 * Real.pi * x) + d * Real.sin (k * 2 * Real.pi * x))) =
      if j = k then (a * c + b * d) / 2 else 0 := by
  have hcont : ∀ (r s : ℕ), Continuous (fun x : ℝ =>
      Real.cos (r * 2 * Real.pi * x) * Real.sin (s * 2 * Real.pi * x)) := by
    intro r s
    exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  have hcc := (apm_m93j05_trig_orthogonality j k hj hk).1
  have hss := (apm_m93j05_trig_orthogonality j k hj hk).2.1
  have hcs := (apm_m93j05_trig_orthogonality j k hj hk).2.2
  have hsc : (∫ x in Set.Icc (0 : ℝ) 1,
      Real.sin (j * 2 * Real.pi * x) * Real.cos (k * 2 * Real.pi * x)) = 0 := by
    simpa [mul_comm] using (apm_m93j05_trig_orthogonality k j hk hj).2.2
  rw [show (fun x : ℝ =>
      (a * Real.cos (j * 2 * Real.pi * x) + b * Real.sin (j * 2 * Real.pi * x)) *
      (c * Real.cos (k * 2 * Real.pi * x) + d * Real.sin (k * 2 * Real.pi * x))) =
      fun x => a*c*(Real.cos (j*2*Real.pi*x)*Real.cos (k*2*Real.pi*x)) +
        a*d*(Real.cos (j*2*Real.pi*x)*Real.sin (k*2*Real.pi*x)) +
        b*c*(Real.sin (j*2*Real.pi*x)*Real.cos (k*2*Real.pi*x)) +
        b*d*(Real.sin (j*2*Real.pi*x)*Real.sin (k*2*Real.pi*x)) by
        funext x; ring]
  rw [MeasureTheory.integral_add, MeasureTheory.integral_add,
    MeasureTheory.integral_add] <;>
    try exact (by fun_prop : Continuous _).continuousOn.integrableOn_Icc
  simp_rw [MeasureTheory.integral_const_mul]
  rw [hcc, hcs, hsc, hss]
  split_ifs with h <;> ring

lemma apm_m93j05_trunc_parseval_aux_expand (N : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    apm_m93j05_trunc N f x ^ 2 =
      (∫ y in Set.Icc (0 : ℝ) 1, f y) ^ 2 +
      2 * (∫ y in Set.Icc (0 : ℝ) 1, f y) *
        (∑ j ∈ Finset.Icc 1 N,
          (apm_m93j05_cosCoeff f j * Real.cos (j * 2 * Real.pi * x) +
           apm_m93j05_sinCoeff f j * Real.sin (j * 2 * Real.pi * x))) +
      ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        (apm_m93j05_cosCoeff f j * Real.cos (j * 2 * Real.pi * x) +
         apm_m93j05_sinCoeff f j * Real.sin (j * 2 * Real.pi * x)) *
        (apm_m93j05_cosCoeff f k * Real.cos (k * 2 * Real.pi * x) +
         apm_m93j05_sinCoeff f k * Real.sin (k * 2 * Real.pi * x)) := by
  unfold apm_m93j05_trunc
  rw [pow_two]
  have hsum := Finset.sum_mul_sum
    (s := Finset.Icc 1 N) (t := Finset.Icc 1 N)
    (f := fun j => apm_m93j05_cosCoeff f j * Real.cos (j * 2 * Real.pi * x) +
      apm_m93j05_sinCoeff f j * Real.sin (j * 2 * Real.pi * x))
    (g := fun k => apm_m93j05_cosCoeff f k * Real.cos (k * 2 * Real.pi * x) +
      apm_m93j05_sinCoeff f k * Real.sin (k * 2 * Real.pi * x))
  rw [← hsum]
  ring

/-- Parseval for the truncation: `∫₀¹ (m + Σ aⱼ cos + bⱼ sin)² = m² + Σ (aⱼ² + bⱼ²)/2`
(from `apm_m93j05_trig_orthogonality` and the mean-zero helpers). -/
lemma apm_m93j05_trunc_parseval_aux_integrated (N : ℕ) (f : ℝ → ℝ) :
    (∫ x in Set.Icc (0 : ℝ) 1, apm_m93j05_trunc N f x ^ 2) =
      (∫ x in Set.Icc (0 : ℝ) 1, f x) ^ 2 +
      ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        if j = k then
          (apm_m93j05_cosCoeff f j * apm_m93j05_cosCoeff f k +
           apm_m93j05_sinCoeff f j * apm_m93j05_sinCoeff f k) / 2
        else 0 := by
  let S := Finset.Icc 1 N
  let m := ∫ x in Set.Icc (0 : ℝ) 1, f x
  let T : ℕ → ℝ → ℝ := fun j x =>
    apm_m93j05_cosCoeff f j * Real.cos (j * 2 * Real.pi * x) +
    apm_m93j05_sinCoeff f j * Real.sin (j * 2 * Real.pi * x)
  have hT (j : ℕ) : Continuous (T j) := by
    exact (continuous_const.mul (Real.continuous_cos.comp
      (continuous_const.mul continuous_id))).add
      (continuous_const.mul (Real.continuous_sin.comp
        (continuous_const.mul continuous_id)))
  have hsum : Continuous (fun x => ∑ j ∈ S, T j x) := by
    fun_prop
  calc
    (∫ x in Set.Icc (0 : ℝ) 1, apm_m93j05_trunc N f x ^ 2) =
        ∫ x in Set.Icc (0 : ℝ) 1,
          m ^ 2 + 2 * m * (∑ j ∈ S, T j x) +
            ∑ j ∈ S, ∑ k ∈ S, T j x * T k x := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with x
      simpa [S, m, T] using apm_m93j05_trunc_parseval_aux_expand N f x
    _ = m ^ 2 +
        ∑ j ∈ S, ∑ k ∈ S,
          if j = k then
            (apm_m93j05_cosCoeff f j * apm_m93j05_cosCoeff f k +
             apm_m93j05_sinCoeff f j * apm_m93j05_sinCoeff f k) / 2
          else 0 := by
      rw [MeasureTheory.integral_add]
      · rw [MeasureTheory.integral_add]
        · rw [MeasureTheory.integral_const]
          simp only [Measure.real, Measure.restrict_apply_univ, Set.univ_inter,
            Real.volume_Icc, sub_zero, ENNReal.ofReal_one, ENNReal.toReal_one,
            one_mul]
          have hdouble : (∫ x in Set.Icc (0 : ℝ) 1,
              ∑ j ∈ S, ∑ k ∈ S, T j x * T k x) =
              ∑ j ∈ S, ∑ k ∈ S, if j = k then
                (apm_m93j05_cosCoeff f j * apm_m93j05_cosCoeff f k +
                 apm_m93j05_sinCoeff f j * apm_m93j05_sinCoeff f k) / 2 else 0 := by
            rw [MeasureTheory.integral_finset_sum S]
            · apply Finset.sum_congr rfl
              intro j hj
              rw [MeasureTheory.integral_finset_sum S]
              · apply Finset.sum_congr rfl
                intro k hk
                exact apm_m93j05_trunc_parseval_aux_inner _ _ _ _ j k
                  (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hk).1
              · intro k hk
                exact ((hT j).mul (hT k)).continuousOn.integrableOn_Icc
            · intro j hj
              exact MeasureTheory.integrable_finset_sum S fun k hk =>
                ((hT j).mul (hT k)).continuousOn.integrableOn_Icc
          have hcross : (∫ x in Set.Icc (0 : ℝ) 1,
              2 * m * (∑ j ∈ S, T j x)) = 0 := by
            rw [MeasureTheory.integral_const_mul,
              MeasureTheory.integral_finset_sum S]
            · apply mul_eq_zero_of_right
              apply Finset.sum_eq_zero
              intro j hj
              exact apm_m93j05_trunc_parseval_aux_mean _ _ j
                (Finset.mem_Icc.mp hj).1
            · intro j hj
              exact (hT j).continuousOn.integrableOn_Icc
          rw [hcross, hdouble]
          simp
        · exact integrableOn_const (hs := measure_Icc_lt_top.ne)
        · exact (continuous_const.mul hsum).continuousOn.integrableOn_Icc
      · exact (continuous_const.add (continuous_const.mul hsum)).continuousOn.integrableOn_Icc
      · exact MeasureTheory.integrable_finset_sum S fun j hj =>
          MeasureTheory.integrable_finset_sum S fun k hk =>
            ((hT j).mul (hT k)).continuousOn.integrableOn_Icc
    _ = _ := by rfl

theorem apm_m93j05_trunc_parseval (N : ℕ) (f : ℝ → ℝ) :
    (eLpNorm (apm_m93j05_trunc N f) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 =
      (∫ x in Set.Icc (0 : ℝ) 1, f x) ^ 2 +
        ∑ j ∈ Finset.Icc 1 N, (apm_m93j05_cosCoeff f j ^ 2 + apm_m93j05_sinCoeff f j ^ 2) / 2 := by
  rw [apm_m93j05_trunc_parseval_aux_norm_sq]
  rw [show (∫ x in Set.Icc (0 : ℝ) 1,
      apm_m93j05_trunc N f x * apm_m93j05_trunc N f x) =
      (∫ x in Set.Icc (0 : ℝ) 1, f x) ^ 2 +
      ∑ j ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        if j = k then
          (apm_m93j05_cosCoeff f j * apm_m93j05_cosCoeff f k +
           apm_m93j05_sinCoeff f j * apm_m93j05_sinCoeff f k) / 2
        else 0 by simpa [pow_two] using apm_m93j05_trunc_parseval_aux_integrated N f]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_ite_eq]
  simp [hj, pow_two]

theorem apm_m93j05_trunc_energy_tendsto (N : ℕ) (p q : ℝ) (hp : 1 < p) (hq : 1 < q) (hpq : 1 / p + 1 / q = 1)
    (f : ℝ → ℝ) (s : ℕ → ℝ → ℝ) (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hs : ∀ n, MemLp (s n) (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hweak : (∀ h, MemLp h (ENNReal.ofReal q) (volume.restrict (Set.Icc (0 : ℝ) 1)) → Tendsto (fun n ↦ ∫ x, s n x * h x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) atTop (nhds (∫ x, f x * h x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))))) :
    Tendsto (fun n ↦ (eLpNorm (apm_m93j05_trunc N (s n)) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2) atTop
      (nhds ((eLpNorm (apm_m93j05_trunc N f) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2)) := by
  obtain ⟨hm, hc, hs⟩ := apm_m93j05_trunc_energy_tendsto_aux_coeffs (N : ℝ) q f s hweak
  simp only [apm_m93j05_trunc_parseval]
  refine (hm.pow 2).add (tendsto_finset_sum _ fun j _ ↦ ?_)
  exact (((hc j).pow 2).add ((hs j).pow 2)).div_const 2

lemma apm_m93j05_lp_rpow_weak_lsc_aux_norming_memLp
    {p q : ℝ} (hp : 1 < p) (hpq : 1 / p + 1 / q = 1)
    {μ : Measure ℝ} {u : ℝ → ℝ} (hu : MemLp u (ENNReal.ofReal p) μ) :
    MemLp (fun x => u x * ‖u x‖ ^ (p - 2)) (ENNReal.ofReal q) μ := by
  have hp1 : 0 < p - 1 := by linarith
  have hq : q = p / (p - 1) := by
    have hp0 : p ≠ 0 := ne_of_gt (lt_trans (by norm_num) hp)
    have hq0 : q ≠ 0 := by
      intro h
      rw [h, div_zero] at hpq
      field_simp at hpq
      linarith
    field_simp [hp0, hq0] at hpq ⊢
    nlinarith
  have hpow : MemLp (fun x => ‖u x‖ ^ (p - 1)) (ENNReal.ofReal q) μ := by
    convert hu.norm_rpow_div (ENNReal.ofReal (p - 1)) using 1
    · simp [ENNReal.toReal_ofReal hp1.le]
    · rw [hq, ENNReal.ofReal_div_of_pos hp1]
  have hmeas : AEStronglyMeasurable (fun x => u x * ‖u x‖ ^ (p - 2)) μ :=
    hu.1.mul (hu.1.norm.aemeasurable.pow aemeasurable_const).aestronglyMeasurable
  apply (memLp_norm_iff hmeas).mp
  convert hpow using 1
  funext x
  by_cases hx : u x = 0
  · simp [hx, Real.zero_rpow (ne_of_gt hp1)]
  · rw [norm_mul, Real.norm_rpow_of_nonneg (norm_nonneg _)]
    simp only [norm_norm]
    calc
      ‖u x‖ * ‖u x‖ ^ (p - 2) = ‖u x‖ ^ (1 : ℝ) * ‖u x‖ ^ (p - 2) := by
        rw [Real.rpow_one]
      _ = ‖u x‖ ^ ((1 : ℝ) + (p - 2)) :=
        (Real.rpow_add (norm_pos_iff.mpr hx) _ _).symm
      _ = ‖u x‖ ^ (p - 1) := by ring_nf

lemma apm_m93j05_lp_rpow_weak_lsc_aux_norming_bounds
    {p q : ℝ} (hp : 1 < p) (hpq : 1 / p + 1 / q = 1)
    {μ : Measure ℝ} {u v : ℝ → ℝ}
    (hu : MemLp u (ENNReal.ofReal p) μ)
    (hv : MemLp v (ENNReal.ofReal p) μ) :
    let h := fun x => u x * ‖u x‖ ^ (p - 2)
    (∫ x, u x * h x ∂μ) =
        Real.rpow (eLpNorm u (ENNReal.ofReal p) μ).toReal p ∧
      (∫ x, v x * h x ∂μ) ≤
        (eLpNorm v (ENNReal.ofReal p) μ).toReal *
          Real.rpow (eLpNorm u (ENNReal.ofReal p) μ).toReal (p - 1) := by
  dsimp
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans (by norm_num) hp)
  have hp0' : (ENNReal.ofReal p) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    linarith
  have hp_top : (ENNReal.ofReal p) ≠ (⊤ : ENNReal) := ENNReal.ofReal_ne_top
  have hpq' : p.HolderConjugate q :=
    Real.holderConjugate_iff.mpr ⟨hp, by simpa [one_div] using hpq⟩
  have hpoint (x : ℝ) :
      u x * (u x * |u x| ^ (p - 2)) = |u x| ^ p := by
    by_cases hx : u x = 0
    · simp [hx, Real.zero_rpow hp0]
    · rw [← mul_assoc, ← pow_two, ← sq_abs, ← Real.rpow_two,
        ← Real.rpow_add (abs_pos.mpr hx)]
      congr 1
      ring
  have hint_nonneg : 0 ≤ ∫ x, ‖u x‖ ^ p ∂μ :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  have hnorm_u :
      (eLpNorm u (ENNReal.ofReal p) μ).toReal =
        (∫ x, ‖u x‖ ^ p ∂μ) ^ (1 / p) := by
    rw [toReal_eLpNorm hu.1]
    simpa [ENNReal.toReal_ofReal (le_trans (by norm_num) hp.le)] using
      lpNorm_eq_integral_norm_rpow_toReal hp0' hp_top hu.1
  constructor
  · rw [integral_congr_ae (Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using hpoint x), hnorm_u]
    simpa [one_div] using (Real.rpow_inv_rpow hint_nonneg hp0).symm
  · have hh := apm_m93j05_lp_rpow_weak_lsc_aux_norming_memLp hp hpq hu
    have hle_norm :
        (∫ x, v x * (u x * ‖u x‖ ^ (p - 2)) ∂μ) ≤
          ∫ x, ‖v x‖ * ‖u x * ‖u x‖ ^ (p - 2)‖ ∂μ := by
      refine le_trans (le_abs_self _) ?_
      simpa [norm_mul] using
        (norm_integral_le_integral_norm
          (fun x => v x * (u x * ‖u x‖ ^ (p - 2))) :
          ‖∫ x, v x * (u x * ‖u x‖ ^ (p - 2)) ∂μ‖ ≤
            ∫ x, ‖v x * (u x * ‖u x‖ ^ (p - 2))‖ ∂μ)
    refine hle_norm.trans ?_
    have hholder := integral_mul_norm_le_Lp_mul_Lq hpq' hv hh
    refine hholder.trans_eq ?_
    have hnorm_v :
        (∫ x, ‖v x‖ ^ p ∂μ) ^ (1 / p) =
          (eLpNorm v (ENNReal.ofReal p) μ).toReal := by
      rw [toReal_eLpNorm hv.1]
      simpa [ENNReal.toReal_ofReal (le_trans (by norm_num) hp.le)] using
        (lpNorm_eq_integral_norm_rpow_toReal hp0' hp_top hv.1).symm
    have hq0 : q ≠ 0 := hpq'.symm.ne_zero
    have hqp : q * (p - 1) = p := by
      have := hpq'.conjugate_eq
      field_simp [hp0, hq0] at hpq ⊢
      nlinarith
    have hhpow :
        (∫ x, ‖u x * ‖u x‖ ^ (p - 2)‖ ^ q ∂μ) =
          ∫ x, ‖u x‖ ^ p ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : u x = 0
      · simp [hx, Real.zero_rpow hp0, Real.zero_rpow hq0]
      · rw [show ‖u x * ‖u x‖ ^ (p - 2)‖ = ‖u x‖ ^ (p - 1) by
          rw [norm_mul, Real.norm_rpow_of_nonneg (norm_nonneg _), norm_norm]
          calc
            ‖u x‖ * ‖u x‖ ^ (p - 2) = ‖u x‖ ^ (1 : ℝ) * ‖u x‖ ^ (p - 2) := by rw [Real.rpow_one]
            _ = ‖u x‖ ^ ((1 : ℝ) + (p - 2)) := (Real.rpow_add (norm_pos_iff.mpr hx) _ _).symm
            _ = ‖u x‖ ^ (p - 1) := by ring_nf,
          ← Real.rpow_mul (norm_nonneg _), mul_comm (p - 1) q, hqp]
    rw [hnorm_v, hhpow, hnorm_u]
    rw [← Real.rpow_mul hint_nonneg]
    congr 2
    field_simp [hp0, hq0] at hpq ⊢
    nlinarith

lemma apm_m93j05_lp_rpow_weak_lsc_aux_limit
    {p r A : ℝ} (hp : 1 < p) (hA : 0 ≤ A)
    {B z : ℕ → ℝ} (hB : ∀ n, 0 ≤ B n)
    (hz : Tendsto z atTop (nhds (Real.rpow A p)))
    (hzB : ∀ n, z n ≤ B n * Real.rpow A (p - 1))
    (hfreq : ∃ᶠ n in atTop, Real.rpow (B n) p ≤ r) :
    Real.rpow A p ≤ r := by
  have hp0 : 0 < p := by linarith
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hr : 0 ≤ r := by
    obtain ⟨n, hn⟩ := hfreq.exists
    exact le_trans (Real.rpow_nonneg (hB n) p) hn
  let R : ℝ := Real.rpow r p⁻¹
  have hR : 0 ≤ R := Real.rpow_nonneg hr _
  have hRp : Real.rpow R p = r := by
    dsimp [R]
    exact Real.rpow_inv_rpow hr hpne
  let l : Filter ℕ := atTop ⊓ Filter.principal
    {n | Real.rpow (B n) p ≤ r}
  letI : l.NeBot := (Filter.frequently_iff_neBot.mp hfreq)
  have hl_atTop : l ≤ atTop := inf_le_left
  have hl_bound : ∀ᶠ n in l, Real.rpow (B n) p ≤ r := by
    apply Filter.Eventually.filter_mono inf_le_right
    simp
  have hBR : ∀ᶠ n in l, B n ≤ R := by
    filter_upwards [hl_bound] with n hn
    apply (Real.rpow_le_rpow_iff (hB n) hR hp0).mp
    calc
      Real.rpow (B n) p ≤ r := hn
      _ = Real.rpow R p := hRp.symm
  have hfactor : 0 ≤ Real.rpow A (p - 1) := Real.rpow_nonneg hA _
  have hzle : ∀ᶠ n in l, z n ≤ R * Real.rpow A (p - 1) := by
    filter_upwards [hBR] with n hn
    exact (hzB n).trans (mul_le_mul_of_nonneg_right hn hfactor)
  have hlim : Real.rpow A p ≤ R * Real.rpow A (p - 1) :=
    le_of_tendsto (hz.mono_left hl_atTop) hzle
  by_cases hAz : A = 0
  · subst A
    simpa [Real.zero_rpow hp0.ne'] using hr
  have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
  have hsplit : Real.rpow A p = A * Real.rpow A (p - 1) := by
    calc
      Real.rpow A p = Real.rpow A (1 + (p - 1)) := by ring_nf
      _ = Real.rpow A 1 * Real.rpow A (p - 1) := Real.rpow_add hApos 1 (p - 1)
      _ = A * Real.rpow A (p - 1) := by simp
  rw [hsplit] at hlim
  have hAR : A ≤ R := by
    apply le_of_not_gt
    intro hRA
    have hstrict := mul_lt_mul_of_pos_right hRA
      (Real.rpow_pos_of_pos hApos (p - 1))
    exact (not_lt_of_ge hlim) hstrict
  rw [← hRp]
  exact Real.rpow_le_rpow hA hAR hp0.le

theorem apm_m93j05_lp_rpow_weak_lsc (p q : ℝ) (hp : 1 < p) (hq : 1 < q) (hpq : 1 / p + 1 / q = 1) :
    ∀ (u : ℝ → ℝ) (w : ℕ → ℝ → ℝ), MemLp u (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      (∀ n, MemLp (w n) (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1))) →
      (∀ h, MemLp h (ENNReal.ofReal q) (volume.restrict (Set.Icc (0 : ℝ) 1)) → Tendsto (fun n ↦ ∫ x, w n x * h x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) atTop (nhds (∫ x, u x * h x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))))) →
      ∀ r, (∃ᶠ n in atTop, Real.rpow (eLpNorm (w n) (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal p ≤ r) →
        Real.rpow (eLpNorm u (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal p ≤ r := by
  intro u w hu hw hweak r hfreq
  let μ := volume.restrict (Set.Icc (0 : ℝ) 1)
  let h := fun x => u x * ‖u x‖ ^ (p - 2)
  let A := (eLpNorm u (ENNReal.ofReal p) μ).toReal
  let B := fun n => (eLpNorm (w n) (ENNReal.ofReal p) μ).toReal
  let z := fun n => ∫ x, w n x * h x ∂μ
  have hh : MemLp h (ENNReal.ofReal q) μ :=
    apm_m93j05_lp_rpow_weak_lsc_aux_norming_memLp hp hpq hu
  have hpair := apm_m93j05_lp_rpow_weak_lsc_aux_norming_bounds hp hpq hu hu
  have hz : Tendsto z atTop (nhds (Real.rpow A p)) := by
    have ht := hweak h hh
    rw [hpair.1] at ht
    simpa [z, A, h, μ] using ht
  apply apm_m93j05_lp_rpow_weak_lsc_aux_limit hp ENNReal.toReal_nonneg
    (fun n => ENNReal.toReal_nonneg) hz
  · intro n
    exact (apm_m93j05_lp_rpow_weak_lsc_aux_norming_bounds hp hpq hu (hw n)).2
  · exact hfreq

lemma apm_m93j05_high_modes_weak_tendsto_aux_trunc_continuous
    (N : ℕ) (h : ℝ → ℝ) : Continuous (apm_m93j05_trunc N h) := by
  unfold apm_m93j05_trunc
  fun_prop

theorem apm_m93j05_high_modes_weak_tendsto (N : ℕ) (p q : ℝ) (hp : 1 < p) (hq : 1 < q) (hpq : 1 / p + 1 / q = 1)
    (f : ℝ → ℝ) (s : ℕ → ℝ → ℝ) (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hs : ∀ n, MemLp (s n) (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hweak : (∀ h, MemLp h (ENNReal.ofReal q) (volume.restrict (Set.Icc (0 : ℝ) 1)) → Tendsto (fun n ↦ ∫ x, s n x * h x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) atTop (nhds (∫ x, f x * h x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))))) :
    (∀ h, MemLp h (ENNReal.ofReal q) (volume.restrict (Set.Icc (0 : ℝ) 1)) → Tendsto (fun n ↦ ∫ x, (s n x - apm_m93j05_trunc N (s n) x) * h x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) atTop (nhds (∫ x, (f x - apm_m93j05_trunc N f x) * h x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))))) := by
  intro h hh
  let μ := volume.restrict (Set.Icc (0 : ℝ) 1)
  have htrunc (r : ℝ) (v : ℝ → ℝ) :
      MemLp (apm_m93j05_trunc N v) (ENNReal.ofReal r) μ := by
    have hcont := apm_m93j05_high_modes_weak_tendsto_aux_trunc_continuous N v
    have hbdd : BddAbove ((fun x ↦ |apm_m93j05_trunc N v x|) '' Set.Icc (0 : ℝ) 1) :=
      isCompact_Icc.bddAbove_image hcont.abs.continuousOn
    obtain ⟨C, hC⟩ := hbdd
    apply MemLp.of_bound hcont.aestronglyMeasurable C
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    simpa [Real.norm_eq_abs] using hC (Set.mem_image_of_mem _ hx)
  have hth := htrunc q h
  have hc : p.HolderConjugate q := Real.holderConjugate_iff.mpr ⟨hp, by
    simpa [div_eq_mul_inv, add_comm] using hpq⟩
  letI : ENNReal.HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal q) 1 := hc.ennrealOfReal
  have A := hweak h hh
  have B := hweak (apm_m93j05_trunc N h) hth
  have B' : Tendsto
      (fun n ↦ ∫ x, apm_m93j05_trunc N (s n) x * h x ∂μ) atTop
      (nhds (∫ x, apm_m93j05_trunc N f x * h x ∂μ)) := by
    rw [apm_m93j05_trunc_selfAdjoint N p q hp hq f h hf hh]
    apply B.congr'
    filter_upwards with n
    exact (apm_m93j05_trunc_selfAdjoint N p q hp hq (s n) h (hs n) hh).symm
  have H := A.sub B'
  rw [show (∫ x, (f x - apm_m93j05_trunc N f x) * h x ∂μ) =
      (∫ x, f x * h x ∂μ) - (∫ x, apm_m93j05_trunc N f x * h x ∂μ) by
    calc
      _ = ∫ x, f x * h x - apm_m93j05_trunc N f x * h x ∂μ := by
        congr 1; funext x; ring
      _ = _ := MeasureTheory.integral_sub (hf.integrable_mul hh)
        ((htrunc p f).integrable_mul hh)]
  apply H.congr'
  filter_upwards with n
  symm
  calc
    _ = ∫ x, s n x * h x - apm_m93j05_trunc N (s n) x * h x ∂μ := by
      congr 1; funext x; ring
    _ = _ := MeasureTheory.integral_sub ((hs n).integrable_mul hh)
      ((htrunc p (s n)).integrable_mul hh)

theorem apm_m93j05_weak_lsc_of_parts (N : ℕ) (p q : ℝ) (hp : 1 < p) (hq : 1 < q) (hpq : 1 / p + 1 / q = 1)
    (f : ℝ → ℝ) (s : ℕ → ℝ → ℝ) (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hs : ∀ n, MemLp (s n) (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hweak : (∀ h, MemLp h (ENNReal.ofReal q) (volume.restrict (Set.Icc (0 : ℝ) 1)) → Tendsto (fun n ↦ ∫ x, s n x * h x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) atTop (nhds (∫ x, f x * h x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))))))
    (g : ℝ → ℝ) (hg : MemLp g (ENNReal.ofReal q) (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hL1 : Tendsto (fun n ↦ (eLpNorm (apm_m93j05_trunc N (s n)) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2) atTop
      (nhds ((eLpNorm (apm_m93j05_trunc N f) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2))) (hL2 : ∀ (u : ℝ → ℝ) (w : ℕ → ℝ → ℝ), MemLp u (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      (∀ n, MemLp (w n) (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1))) →
      (∀ h, MemLp h (ENNReal.ofReal q) (volume.restrict (Set.Icc (0 : ℝ) 1)) → Tendsto (fun n ↦ ∫ x, w n x * h x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) atTop (nhds (∫ x, u x * h x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))))) →
      ∀ r, (∃ᶠ n in atTop, Real.rpow (eLpNorm (w n) (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal p ≤ r) →
        Real.rpow (eLpNorm u (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal p ≤ r) (hL3 : (∀ h, MemLp h (ENNReal.ofReal q) (volume.restrict (Set.Icc (0 : ℝ) 1)) → Tendsto (fun n ↦ ∫ x, (s n x - apm_m93j05_trunc N (s n) x) * h x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) atTop (nhds (∫ x, (f x - apm_m93j05_trunc N f x) * h x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))))) :
    ∀ r, (∃ᶠ n in atTop, apm_m93j05_J N p g (s n) ≤ r) → apm_m93j05_J N p g f ≤ r := by
  let μ := volume.restrict (Set.Icc (0 : ℝ) 1)
  have htrunc : ∀ v : ℝ → ℝ,
      MemLp (apm_m93j05_trunc N v) (ENNReal.ofReal p) μ := by
    intro v
    let C : ℝ := |∫ x in Set.Icc (0 : ℝ) 1, v x| +
      ∑ j ∈ Finset.Icc 1 N,
        (|apm_m93j05_cosCoeff v j| + |apm_m93j05_sinCoeff v j|)
    apply MemLp.of_bound (C := C)
    · exact (apm_m93j05_trunc_split_aux_continuous N v).aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs]
      unfold apm_m93j05_trunc
      calc
        |_ + _| ≤ |∫ z in Set.Icc (0 : ℝ) 1, v z| +
              |∑ j ∈ Finset.Icc 1 N,
                (apm_m93j05_cosCoeff v j * Real.cos (j * 2 * Real.pi * x) +
                 apm_m93j05_sinCoeff v j * Real.sin (j * 2 * Real.pi * x))| := abs_add_le _ _
        _ ≤ C := by
          dsimp [C]
          apply add_le_add le_rfl
          calc
            |∑ j ∈ Finset.Icc 1 N, _| ≤
                ∑ j ∈ Finset.Icc 1 N,
                  |apm_m93j05_cosCoeff v j * Real.cos (j * 2 * Real.pi * x) +
                   apm_m93j05_sinCoeff v j * Real.sin (j * 2 * Real.pi * x)| :=
              Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ j ∈ Finset.Icc 1 N,
                (|apm_m93j05_cosCoeff v j| + |apm_m93j05_sinCoeff v j|) := by
              apply Finset.sum_le_sum
              intro j hj
              calc
                |_ + _| ≤ |_| + |_| := abs_add_le _ _
                _ ≤ |apm_m93j05_cosCoeff v j| + |apm_m93j05_sinCoeff v j| := by
                  simp only [abs_mul]
                  exact add_le_add
                    (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
                    (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _))
  have huf : MemLp (fun x ↦ f x - apm_m93j05_trunc N f x)
      (ENNReal.ofReal p) μ := hf.sub (htrunc f)
  have huw : ∀ n, MemLp (fun x ↦ s n x - apm_m93j05_trunc N (s n) x)
      (ENNReal.ofReal p) μ := fun n ↦ (hs n).sub (htrunc (s n))
  have hpair := apm_m93j05_weak_lowerSemicontinuous_aux_pairing g f s hg hweak
  let A : (ℝ → ℝ) → ℝ := fun v ↦ Real.rpow
    (eLpNorm (fun x ↦ v x - apm_m93j05_trunc N v x) (ENNReal.ofReal p) μ).toReal p
  let B : (ℝ → ℝ) → ℝ := fun v ↦
    (eLpNorm (apm_m93j05_trunc N v) 2 μ).toReal ^ 2
  let C : (ℝ → ℝ) → ℝ := fun v ↦ ∫ x, v x * g x ∂μ
  have hBC : Tendsto (fun n ↦ B (s n) + C (s n)) atTop
      (nhds (B f + C f)) := hL1.add hpair
  intro r hr
  apply le_of_forall_pos_le_add
  intro ε hε
  have hev : ∀ᶠ n in atTop, B f + C f - ε < B (s n) + C (s n) :=
    (tendsto_order.1 hBC).1 _ (by linarith)
  have hfreq := hr.and_eventually hev
  have hAfreq : ∃ᶠ n in atTop, A (s n) ≤ r - (B f + C f) + ε := by
    apply hfreq.mono
    intro n hn
    dsimp [apm_m93j05_J, A, B, C, μ] at hn ⊢
    linarith
  have hAle : A f ≤ r - (B f + C f) + ε :=
    hL2 (fun x ↦ f x - apm_m93j05_trunc N f x)
      (fun n x ↦ s n x - apm_m93j05_trunc N (s n) x)
      huf huw hL3 _ (by simpa [A, μ] using hAfreq)
  dsimp [apm_m93j05_J, A, B, C, μ] at hAle ⊢
  linarith

theorem apm_m93j05_weak_lowerSemicontinuous
    (N : ℕ) (p q : ℝ) (hp : 1 < p) (hq : 1 < q)
    (hpq : 1 / p + 1 / q = 1) :
    let μ := volume.restrict (Set.Icc (0 : ℝ) 1)
    ∀ g, MemLp g (ENNReal.ofReal q) μ →
      ∀ (f : ℝ → ℝ) (s : ℕ → ℝ → ℝ),
        MemLp f (ENNReal.ofReal p) μ →
        (∀ n, MemLp (s n) (ENNReal.ofReal p) μ) →
        (∀ h, MemLp h (ENNReal.ofReal q) μ →
          Tendsto (fun n => ∫ x, s n x * h x ∂μ) atTop
            (nhds (∫ x, f x * h x ∂μ))) →
        ∀ r, (∃ᶠ n in atTop, apm_m93j05_J N p g (s n) ≤ r) →
          apm_m93j05_J N p g f ≤ r := by
  intro μ g hg f s hf hs hweak
  exact apm_m93j05_weak_lsc_of_parts N p q hp hq hpq f s hf hs hweak g hg
    (apm_m93j05_trunc_energy_tendsto N p q hp hq hpq f s hf hs hweak)
    (apm_m93j05_lp_rpow_weak_lsc p q hp hq hpq)
    (apm_m93j05_high_modes_weak_tendsto N p q hp hq hpq f s hf hs hweak)

lemma apm_m93j05_exists_minimizer_aux_zero_memLp (p : ℝ) :
    MemLp (0 : ℝ → ℝ) (ENNReal.ofReal p)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  exact MemLp.zero

lemma apm_m93j05_exists_minimizer_aux_trunc_zero (N : ℕ) :
    apm_m93j05_trunc N (0 : ℝ → ℝ) = 0 := by
  funext x
  simp [apm_m93j05_trunc, apm_m93j05_cosCoeff, apm_m93j05_sinCoeff]

lemma apm_m93j05_exists_minimizer_aux_J_zero (N : ℕ) (p : ℝ) (g : ℝ → ℝ)
    (hp : 0 < p) :
    apm_m93j05_J N p g (0 : ℝ → ℝ) = 0 := by
  simp [apm_m93j05_J, apm_m93j05_exists_minimizer_aux_trunc_zero,
    Real.zero_rpow hp.ne']

/-! ### Split of `apm_m93j05_exists_minimizer`

The first two leaves are direct-method preliminaries.  The third is the one missing functional-
analytic foundation in Mathlib: weak sequential compactness of bounded sets in `Lᵖ`, transported
from quotient `Lp` back to representatives.  The fourth is the order-theoretic/lower-semicontinuity
closure.  Every dependency is an explicit hypothesis, so the four seats are independent. -/

/-- Coercivity of `J`: every finite sublevel is bounded in `Lᵖ`, uniformly in its elements. -/
lemma apm_m93j05_exists_minimizer_coercive_aux_trunc_pointwise
    (N : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    |apm_m93j05_trunc N f x| ≤
      (1 + 4 * N) *
        (eLpNorm (apm_m93j05_trunc N f) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := by
  let y := (eLpNorm (apm_m93j05_trunc N f) 2
    (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
  have hy : 0 ≤ y := ENNReal.toReal_nonneg
  have hparse := apm_m93j05_trunc_parseval N f
  have hm : |∫ z in Set.Icc (0 : ℝ) 1, f z| ≤ y := by
    have hs : 0 ≤ ∑ j ∈ Finset.Icc 1 N,
        (apm_m93j05_cosCoeff f j ^ 2 + apm_m93j05_sinCoeff f j ^ 2) / 2 := by
      positivity
    rw [show (eLpNorm (apm_m93j05_trunc N f) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal = y by rfl] at hparse
    nlinarith [sq_abs (∫ z in Set.Icc (0 : ℝ) 1, f z)]
  have hc (j : ℕ) (hj : j ∈ Finset.Icc 1 N) :
      |apm_m93j05_cosCoeff f j| ≤ 2 * y := by
    have hterm : (apm_m93j05_cosCoeff f j ^ 2 +
        apm_m93j05_sinCoeff f j ^ 2) / 2 ≤ y ^ 2 := by
      rw [show y ^ 2 = (∫ z in Set.Icc (0 : ℝ) 1, f z) ^ 2 +
          ∑ k ∈ Finset.Icc 1 N,
            (apm_m93j05_cosCoeff f k ^ 2 + apm_m93j05_sinCoeff f k ^ 2) / 2 by
        simpa [y] using hparse]
      have hsingle : (apm_m93j05_cosCoeff f j ^ 2 +
          apm_m93j05_sinCoeff f j ^ 2) / 2 ≤
          ∑ k ∈ Finset.Icc 1 N,
            (apm_m93j05_cosCoeff f k ^ 2 + apm_m93j05_sinCoeff f k ^ 2) / 2 :=
        Finset.single_le_sum (s := Finset.Icc 1 N)
          (f := fun k => (apm_m93j05_cosCoeff f k ^ 2 +
            apm_m93j05_sinCoeff f k ^ 2) / 2)
          (fun k (_ : k ∈ Finset.Icc 1 N) => by positivity) hj
      nlinarith
    nlinarith [sq_abs (apm_m93j05_cosCoeff f j),
      sq_nonneg (apm_m93j05_sinCoeff f j)]
  have hs (j : ℕ) (hj : j ∈ Finset.Icc 1 N) :
      |apm_m93j05_sinCoeff f j| ≤ 2 * y := by
    have hterm : (apm_m93j05_cosCoeff f j ^ 2 +
        apm_m93j05_sinCoeff f j ^ 2) / 2 ≤ y ^ 2 := by
      rw [show y ^ 2 = (∫ z in Set.Icc (0 : ℝ) 1, f z) ^ 2 +
          ∑ k ∈ Finset.Icc 1 N,
            (apm_m93j05_cosCoeff f k ^ 2 + apm_m93j05_sinCoeff f k ^ 2) / 2 by
        simpa [y] using hparse]
      have hsingle : (apm_m93j05_cosCoeff f j ^ 2 +
          apm_m93j05_sinCoeff f j ^ 2) / 2 ≤
          ∑ k ∈ Finset.Icc 1 N,
            (apm_m93j05_cosCoeff f k ^ 2 + apm_m93j05_sinCoeff f k ^ 2) / 2 :=
        Finset.single_le_sum (s := Finset.Icc 1 N)
          (f := fun k => (apm_m93j05_cosCoeff f k ^ 2 +
            apm_m93j05_sinCoeff f k ^ 2) / 2)
          (fun k (_ : k ∈ Finset.Icc 1 N) => by positivity) hj
      nlinarith
    nlinarith [sq_abs (apm_m93j05_sinCoeff f j),
      sq_nonneg (apm_m93j05_cosCoeff f j)]
  rw [apm_m93j05_trunc]
  calc
    |(∫ z in Set.Icc (0 : ℝ) 1, f z) + ∑ j ∈ Finset.Icc 1 N,
        (apm_m93j05_cosCoeff f j * Real.cos (j * 2 * Real.pi * x) +
         apm_m93j05_sinCoeff f j * Real.sin (j * 2 * Real.pi * x))| ≤
        |∫ z in Set.Icc (0 : ℝ) 1, f z| + ∑ j ∈ Finset.Icc 1 N,
          (|apm_m93j05_cosCoeff f j| + |apm_m93j05_sinCoeff f j|) := by
      refine (abs_add_le _ _).trans (add_le_add_right (Finset.abs_sum_le_sum_abs _ _) _ |>.trans ?_)
      gcongr with j hj
      exact (abs_add_le _ _).trans (add_le_add
        (by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
        (by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)))
    _ ≤ y + ∑ j ∈ Finset.Icc 1 N, (2 * y + 2 * y) := by
      exact add_le_add hm (Finset.sum_le_sum fun j hj =>
        add_le_add (hc j hj) (hs j hj))
    _ = (1 + 4 * N) * y := by
      simp [Finset.sum_const, Nat.card_Icc]
      ring

lemma apm_m93j05_exists_minimizer_coercive_aux_trunc_Lp
    (N : ℕ) (p : ℝ) (hp : 1 < p) (f : ℝ → ℝ) :
    (eLpNorm (apm_m93j05_trunc N f) (ENNReal.ofReal p)
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ≤
      (1 + 4 * N) *
        (eLpNorm (apm_m93j05_trunc N f) 2
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := by
  let C : ℝ := (1 + 4 * N) *
    (eLpNorm (apm_m93j05_trunc N f) 2
      (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hae : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      ‖apm_m93j05_trunc N f x‖ ≤ C := by
    filter_upwards [] with x
    simpa [Real.norm_eq_abs, C] using
      apm_m93j05_exists_minimizer_coercive_aux_trunc_pointwise N f x
  have h := eLpNorm_le_of_ae_bound
    (p := ENNReal.ofReal p) hae
  have hmass : (volume.restrict (Set.Icc (0 : ℝ) 1)) Set.univ = 1 := by
    simp [Measure.restrict_apply_univ, Real.volume_Icc]
  rw [hmass] at h
  have hsimpl :
      eLpNorm (apm_m93j05_trunc N f) (ENNReal.ofReal p)
        (volume.restrict (Set.Icc (0 : ℝ) 1)) ≤ ENNReal.ofReal C := by
    simpa using h
  have hfinite : ENNReal.ofReal C ≠ ⊤ := ENNReal.ofReal_ne_top
  have hnormfinite :
      eLpNorm (apm_m93j05_trunc N f) (ENNReal.ofReal p)
        (volume.restrict (Set.Icc (0 : ℝ) 1)) ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite hsimpl
  have hreal := (ENNReal.toReal_le_toReal hnormfinite hfinite).2 hsimpl
  simpa [C, ENNReal.toReal_ofReal hC] using hreal

lemma apm_m93j05_exists_minimizer_coercive_aux_triangle
    (N : ℕ) (p : ℝ) (hp : 1 < p) (f : ℝ → ℝ)
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    (eLpNorm f (ENNReal.ofReal p)
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ≤
      (eLpNorm (fun x => f x - apm_m93j05_trunc N f x) (ENNReal.ofReal p)
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal +
        (eLpNorm (apm_m93j05_trunc N f) (ENNReal.ofReal p)
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := by
  sorry

lemma apm_m93j05_exists_minimizer_coercive_aux_holder
    (p q : ℝ) (hp : 1 < p) (hq : 1 < q)
    (hpq : 1 / p + 1 / q = 1) (f g : ℝ → ℝ)
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hg : MemLp g (ENNReal.ofReal q) (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    |∫ x in Set.Icc (0 : ℝ) 1, f x * g x| ≤
      (eLpNorm f (ENNReal.ofReal p)
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal *
        (eLpNorm g (ENNReal.ofReal q)
          (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := by
  sorry

lemma apm_m93j05_exists_minimizer_coercive_aux_scalar
    (p : ℝ) (hp : 1 < p) (G C A : ℝ) (hG : 0 ≤ G) (hC : 0 ≤ C) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ a y : ℝ, 0 ≤ a → 0 ≤ y →
      a ^ p + y ^ 2 - G * (a + C * y) ≤ A → a + C * y ≤ R := by
  sorry

lemma apm_m93j05_exists_minimizer_coercive
    (N : ℕ) (p q : ℝ) (hp : 1 < p) (hq : 1 < q)
    (hpq : 1 / p + 1 / q = 1) (g : ℝ → ℝ)
    (hg : MemLp g (ENNReal.ofReal q) (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    ∀ A : ℝ, ∃ R : ℝ, 0 ≤ R ∧ ∀ f,
      MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      apm_m93j05_J N p g f ≤ A →
      (eLpNorm f (ENNReal.ofReal p)
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ≤ R := by
  intro A
  set G := (eLpNorm g (ENNReal.ofReal q)
    (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal with hGdef
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hC : (0 : ℝ) ≤ 1 + 4 * N := by positivity
  obtain ⟨R, hR0, hR⟩ :=
    apm_m93j05_exists_minimizer_coercive_aux_scalar p hp G (1 + 4 * N) A hG hC
  refine ⟨R, hR0, fun f hf hJ => ?_⟩
  set a := (eLpNorm (fun x => f x - apm_m93j05_trunc N f x) (ENNReal.ofReal p)
    (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal with hadef
  set y := (eLpNorm (apm_m93j05_trunc N f) 2
    (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal with hydef
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hy : 0 ≤ y := ENNReal.toReal_nonneg
  have hh := apm_m93j05_exists_minimizer_coercive_aux_holder p q hp hq hpq f g hf hg
  have ht := apm_m93j05_exists_minimizer_coercive_aux_triangle N p hp f hf
  have hu := apm_m93j05_exists_minimizer_coercive_aux_trunc_Lp N p hp f
  have hfle : (eLpNorm f (ENNReal.ofReal p)
      (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ≤ a + (1 + 4 * N) * y := by
    linarith
  have hfg : -(G * (a + (1 + 4 * N) * y)) ≤ ∫ x in Set.Icc (0 : ℝ) 1, f x * g x := by
    have h1 := neg_abs_le (∫ x in Set.Icc (0 : ℝ) 1, f x * g x)
    have h2 := mul_le_mul_of_nonneg_left hfle hG
    nlinarith
  have hJ' : a ^ p + y ^ 2 + ∫ x in Set.Icc (0 : ℝ) 1, f x * g x ≤ A := by
    simpa [apm_m93j05_J, Real.rpow_eq_pow] using hJ
  exact hfle.trans (hR a y ha hy (by linarith))

/-- An `Lᵖ` minimizing sequence, expressed without an infimum: at precision `1/(k+1)`, its tail
beats every admissible competitor up to that error. -/
lemma apm_m93j05_exists_minimizer_minimizing_sequence
    (N : ℕ) (p q : ℝ) (hp : 1 < p) (hq : 1 < q)
    (hpq : 1 / p + 1 / q = 1) (g : ℝ → ℝ)
    (hg : MemLp g (ENNReal.ofReal q) (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    ∃ s : ℕ → ℝ → ℝ,
      (∀ n, MemLp (s n) (ENNReal.ofReal p)
        (volume.restrict (Set.Icc (0 : ℝ) 1))) ∧
      ∀ f, MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)) →
        ∀ k : ℕ, ∀ᶠ n in atTop,
          apm_m93j05_J N p g (s n) ≤ apm_m93j05_J N p g f + 1 / (k + 1 : ℝ) := by
  classical
  let A : Set ℝ := {a | ∃ f : ℝ → ℝ,
    MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)) ∧
      apm_m93j05_J N p g f = a}
  have hA : A.Nonempty := by
    refine ⟨apm_m93j05_J N p g 0, 0, ?_, rfl⟩
    exact apm_m93j05_exists_minimizer_aux_zero_memLp p
  by_cases hb : BddBelow A
  · have hchoice : ∀ n : ℕ, ∃ f : ℝ → ℝ,
        MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)) ∧
          apm_m93j05_J N p g f < sInf A + 1 / (n + 1 : ℝ) := by
      intro n
      have heps : 0 < 1 / (n + 1 : ℝ) := by positivity
      obtain ⟨a, haA, ha⟩ := exists_lt_of_csInf_lt hA (lt_add_of_pos_right _ heps)
      obtain ⟨f, hf, rfl⟩ := haA
      exact ⟨f, hf, ha⟩
    choose s hs hJ using hchoice
    refine ⟨s, hs, ?_⟩
    intro f hf k
    filter_upwards [eventually_ge_atTop k] with n hn
    have hin : apm_m93j05_J N p g f ∈ A := ⟨f, hf, rfl⟩
    have hinf : sInf A ≤ apm_m93j05_J N p g f := csInf_le hb hin
    have hden : (k + 1 : ℝ) ≤ n + 1 := by exact_mod_cast Nat.add_le_add_right hn 1
    have hfrac : 1 / (n + 1 : ℝ) ≤ 1 / (k + 1 : ℝ) := by
      exact one_div_le_one_div_of_le (by positivity) hden
    exact (hJ n).le.trans (add_le_add hinf hfrac)
  · have hchoice : ∀ n : ℕ, ∃ f : ℝ → ℝ,
        MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)) ∧
          apm_m93j05_J N p g f < -(n : ℝ) := by
      intro n
      have hnlow : -(n : ℝ) ∉ lowerBounds A := by
        intro hnlow
        exact hb ⟨-(n : ℝ), hnlow⟩
      change ¬ (∀ a ∈ A, -(n : ℝ) ≤ a) at hnlow
      push_neg at hnlow
      obtain ⟨a, haA, ha⟩ := hnlow
      obtain ⟨f, hf, rfl⟩ := haA
      exact ⟨f, hf, ha⟩
    choose s hs hJ using hchoice
    refine ⟨s, hs, ?_⟩
    intro f hf k
    obtain ⟨m, hm⟩ := exists_nat_gt (-(apm_m93j05_J N p g f + 1 / (k + 1 : ℝ)))
    filter_upwards [eventually_ge_atTop m] with n hn
    have hmn : (m : ℝ) ≤ n := by exact_mod_cast hn
    have hbound : -(n : ℝ) ≤ apm_m93j05_J N p g f + 1 / (k + 1 : ℝ) := by
      linarith
    exact (hJ n).le.trans hbound

lemma apm_m93j05_exists_minimizer_weak_subsequence_aux_eventually_bounded
    (N : ℕ) (p q : ℝ) (hp : 1 < p) (g : ℝ → ℝ)
    (hcoercive : ∀ A : ℝ, ∃ R : ℝ, 0 ≤ R ∧ ∀ f,
      MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      apm_m93j05_J N p g f ≤ A →
      (eLpNorm f (ENNReal.ofReal p)
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ≤ R)
    (s : ℕ → ℝ → ℝ)
    (hs : ∀ n, MemLp (s n) (ENNReal.ofReal p)
      (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hmin : ∀ f, MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ k : ℕ, ∀ᶠ n in atTop,
        apm_m93j05_J N p g (s n) ≤ apm_m93j05_J N p g f + 1 / (k + 1 : ℝ)) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ n in atTop,
      (eLpNorm (s n) (ENNReal.ofReal p)
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ≤ R := by
  obtain ⟨R, hR, hbound⟩ := hcoercive 1
  refine ⟨R, hR, ?_⟩
  filter_upwards [hmin (0 : ℝ → ℝ) MemLp.zero 0] with n hn
  apply hbound (s n) (hs n)
  rw [apm_m93j05_exists_minimizer_aux_J_zero N p g (by linarith)] at hn
  norm_num at hn ⊢
  exact hn

/-- Weak sequential compactness of a bounded sequence in real `Lp([0,1])`, `1 < p < ∞`, without
the identification `(Lᵠ)* = Lᵖ`: shift to a uniformly bounded tail, diagonalise over rational
interval pairings, represent the limit, extend by density (split 2026-10-19 after lemma-3's
partial). -/
lemma apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_exponents
    (p q : ℝ) (hp : 1 < p) (hq : 1 < q) (hpq : 1 / p + 1 / q = 1) :
    0 < p ∧ 0 < q ∧ p ≠ 0 ∧ q ≠ 0 ∧
      q * (p - 1) = p ∧ p * (q - 1) = q := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hqne : q ≠ 0 := ne_of_gt hq0
  refine ⟨hp0, hq0, hpne, hqne, ?_, ?_⟩
  · field_simp [hpne, hqne] at hpq
    nlinarith
  · field_simp [hpne, hqne] at hpq
    nlinarith

lemma apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_tail
    (p : ℝ) (s : ℕ → ℝ → ℝ)
    (hbounded : ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ n in atTop,
      (eLpNorm (s n) (ENNReal.ofReal p)
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ≤ R) :
    ∃ R : ℝ, 0 ≤ R ∧ ∃ k : ℕ, ∀ n : ℕ,
      (eLpNorm (s (k + n)) (ENNReal.ofReal p)
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ≤ R := by
  obtain ⟨R, hR, h⟩ := hbounded
  rw [eventually_atTop] at h
  obtain ⟨k, hk⟩ := h
  refine ⟨R, hR, k, fun n ↦ hk (k + n) ?_⟩
  omega

/-- Leaf (diagonal argument). Countably many bounded real sequences have a common convergent
subsequence. Route: the coordinatewise bounds put `u n` in a product of closed intervals, which
is compact and metrizable for countable `ι`; use `IsCompact.tendsto_subseq`. -/
lemma apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_diagonal
    {ι : Type*} [Countable ι] (u : ℕ → ι → ℝ) (hb : ∀ i, ∃ C : ℝ, ∀ n, |u n i| ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ L : ι → ℝ,
      ∀ i, Tendsto (fun n ↦ u (φ n) i) atTop (nhds (L i)) := by
  sorry

/-- Leaf (Hölder). Pairing an `Lᵖ([0,1])` function against the indicator of an interval is
bounded by its `Lᵖ` norm, since that indicator has `Lᵠ([0,1])` norm at most `1`. -/
lemma apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_indicator_bound
    (p q : ℝ) (hp : 1 < p) (hq : 1 < q) (hpq : 1 / p + 1 / q = 1)
    (f : ℝ → ℝ) (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (a b : ℝ) :
    |∫ x in Set.Icc (0 : ℝ) 1, f x * (Set.Ioc a b).indicator (fun _ ↦ (1 : ℝ)) x| ≤
      (eLpNorm f (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := by
  sorry

lemma apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_limit_rep_aux_tendsto_abs_le
    {u : ℕ → ℝ} {x C : ℝ} (hu : Tendsto u atTop (nhds x))
    (hC : ∀ n, |u n| ≤ C) : |x| ≤ C := by
  have habs : Tendsto (fun n ↦ |u n|) atTop (nhds |x|) :=
    (continuous_abs.tendsto x).comp hu
  exact le_of_tendsto habs (Eventually.of_forall hC)

lemma apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_limit_rep_aux_add
    (p q : ℝ) (hp : 1 < p) (hpq : 1 / p + 1 / q = 1)
    (s : ℕ → ℝ → ℝ)
    (hs : ∀ n, MemLp (s n) (ENNReal.ofReal p)
      (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (L : ℚ × ℚ → ℝ)
    (hL : ∀ i : ℚ × ℚ, Tendsto (fun n ↦ ∫ x in Set.Icc (0 : ℝ) 1,
      s n x * (Set.Ioc (i.1 : ℝ) i.2).indicator (fun _ ↦ (1 : ℝ)) x) atTop (nhds (L i)))
    (a b c : ℚ) (hab : a ≤ b) (hbc : b ≤ c) :
    L (a, c) = L (a, b) + L (b, c) := by
  have hpqR : p.HolderConjugate q := Real.holderConjugate_iff.mpr ⟨hp, by simpa [div_eq_mul_inv] using hpq⟩
  have hpqE : (ENNReal.ofReal p).HolderConjugate (ENNReal.ofReal q) := by
    apply ENNReal.HolderConjugate.of_toReal
    simpa [ENNReal.toReal_ofReal hpqR.nonneg, ENNReal.toReal_ofReal hpqR.symm.nonneg]
      using hpqR
  let μ := volume.restrict (Set.Icc (0 : ℝ) 1)
  have hind (u v : ℚ) : MemLp
      ((Set.Ioc (u : ℝ) v).indicator (fun _ ↦ (1 : ℝ))) (ENNReal.ofReal q) μ := by
    apply memLp_indicator_const
    · exact measurableSet_Ioc
    · right
      simp only [μ, Measure.restrict_apply measurableSet_Ioc]
      exact ((measure_mono Set.inter_subset_right).trans_lt
        (by simp : volume (Set.Icc (0 : ℝ) 1) < ⊤)).ne
  have hint (n : ℕ) (u v : ℚ) : Integrable
      (fun x ↦ s n x * (Set.Ioc (u : ℝ) v).indicator (fun _ ↦ (1 : ℝ)) x) μ := by
    letI : (ENNReal.ofReal p).HolderTriple (ENNReal.ofReal q) 1 := hpqE
    exact (hs n).integrable_mul (hind u v)
  have heq (n : ℕ) : (∫ x in Set.Icc (0 : ℝ) 1,
      s n x * (Set.Ioc (a : ℝ) c).indicator (fun _ ↦ (1 : ℝ)) x) =
      (∫ x in Set.Icc (0 : ℝ) 1,
        s n x * (Set.Ioc (a : ℝ) b).indicator (fun _ ↦ (1 : ℝ)) x) +
      ∫ x in Set.Icc (0 : ℝ) 1,
        s n x * (Set.Ioc (b : ℝ) c).indicator (fun _ ↦ (1 : ℝ)) x := by
    rw [← integral_add (hint n a b) (hint n b c)]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
    have hbcR : (b : ℝ) ≤ c := by exact_mod_cast hbc
    show s n x * _ = s n x * _ + s n x * _
    rw [← mul_add, ← Set.Ioc_union_Ioc_eq_Ioc habR hbcR,
      Set.indicator_union_of_disjoint (Set.Ioc_disjoint_Ioc_of_le le_rfl)]
  apply tendsto_nhds_unique (hL (a, c))
  convert (hL (a, b)).add (hL (b, c)) using 1
  exact funext heq

/-- Leaf (step functional). The limits `L` extend linearly to rational step functions, with
the bound `|Λ g| ≤ R ‖g‖_q`. Route: `∑ c_i ∫ s_n 1_i = ∫ s_n g` (linearity; each product is
integrable by Hölder), so the left side is the limit of `∫ s_n g`; Hölder bounds each term
by `R ‖g‖_q`; pass to the limit with `..._aux_limit_rep_aux_tendsto_abs_le`. -/
lemma apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_limit_rep_aux_step_bound
    (p q : ℝ) (hp : 1 < p) (hq : 1 < q) (hpq : 1 / p + 1 / q = 1)
    (s : ℕ → ℝ → ℝ)
    (hs : ∀ n, MemLp (s n) (ENNReal.ofReal p)
      (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ n : ℕ,
      (eLpNorm (s n) (ENNReal.ofReal p)
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ≤ R)
    (L : ℚ × ℚ → ℝ)
    (hL : ∀ i : ℚ × ℚ, Tendsto (fun n ↦ ∫ x in Set.Icc (0 : ℝ) 1,
      s n x * (Set.Ioc (i.1 : ℝ) i.2).indicator (fun _ ↦ (1 : ℝ)) x) atTop (nhds (L i))) :
    ∀ (F : Finset (ℚ × ℚ)) (c : ℚ × ℚ → ℝ),
      |∑ i ∈ F, c i * L i| ≤ R * (eLpNorm (fun x ↦ ∑ i ∈ F, c i *
          (Set.Ioc (i.1 : ℝ) i.2).indicator (fun _ ↦ (1 : ℝ)) x)
        (ENNReal.ofReal q) (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := by
  intro F c
  let μ := volume.restrict (Set.Icc (0 : ℝ) 1)
  let g : ℝ → ℝ := fun x ↦ ∑ i ∈ F, c i *
    (Set.Ioc (i.1 : ℝ) i.2).indicator (fun _ ↦ (1 : ℝ)) x
  have hpqR : p.HolderConjugate q :=
    Real.holderConjugate_iff.mpr ⟨hp, by simpa [div_eq_mul_inv] using hpq⟩
  have hind (i : ℚ × ℚ) : MemLp
      ((Set.Ioc (i.1 : ℝ) i.2).indicator (fun _ ↦ (1 : ℝ)))
        (ENNReal.ofReal q) μ := by
    apply memLp_indicator_const
    · exact measurableSet_Ioc
    · right
      simp only [μ, Measure.restrict_apply measurableSet_Ioc]
      exact ((measure_mono Set.inter_subset_right).trans_lt
        (by simp : volume (Set.Icc (0 : ℝ) 1) < ⊤)).ne
  have hg : MemLp g (ENNReal.ofReal q) μ := by
    dsimp [g]
    induction F using Finset.induction_on with
    | empty => simp
    | @insert i F hi ih =>
        simpa only [Finset.sum_insert hi, Pi.add_apply] using
          ((hind i).const_mul (c i)).add ih
  have hint (n : ℕ) (i : ℚ × ℚ) : Integrable
      (fun x ↦ s n x * (Set.Ioc (i.1 : ℝ) i.2).indicator (fun _ ↦ (1 : ℝ)) x) μ := by
    have hpqE : (ENNReal.ofReal p).HolderConjugate (ENNReal.ofReal q) := by
      apply ENNReal.HolderConjugate.of_toReal
      simpa [ENNReal.toReal_ofReal hpqR.nonneg,
        ENNReal.toReal_ofReal hpqR.symm.nonneg] using hpqR
    letI : (ENNReal.ofReal p).HolderTriple (ENNReal.ofReal q) 1 := hpqE
    exact (hs n).integrable_mul (hind i)
  have heq (n : ℕ) : (∫ x in Set.Icc (0 : ℝ) 1, s n x * g x) =
      ∑ i ∈ F, c i * ∫ x in Set.Icc (0 : ℝ) 1,
        s n x * (Set.Ioc (i.1 : ℝ) i.2).indicator (fun _ ↦ (1 : ℝ)) x := by
    change (∫ x, s n x * g x ∂μ) =
      ∑ i ∈ F, c i * ∫ x, s n x *
        (Set.Ioc (i.1 : ℝ) i.2).indicator (fun _ ↦ (1 : ℝ)) x ∂μ
    simp only [g, Finset.mul_sum]
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall (fun x ↦ by ring)
    · intro i hi
      simpa only [mul_assoc, mul_left_comm] using (hint n i).const_mul (c i)
  have ht : Tendsto (fun n ↦ ∫ x in Set.Icc (0 : ℝ) 1, s n x * g x) atTop
      (nhds (∑ i ∈ F, c i * L i)) := by
    rw [show (fun n ↦ ∫ x in Set.Icc (0 : ℝ) 1, s n x * g x) =
        fun n ↦ ∑ i ∈ F, c i * ∫ x in Set.Icc (0 : ℝ) 1,
          s n x * (Set.Ioc (i.1 : ℝ) i.2).indicator (fun _ ↦ (1 : ℝ)) x from
      funext heq]
    exact tendsto_finset_sum F (fun i _ ↦
      (tendsto_const_nhds.mul (hL i)))
  have hnorm (n : ℕ) :
      |(∫ x in Set.Icc (0 : ℝ) 1, s n x * g x)| ≤
        (eLpNorm (s n) (ENNReal.ofReal p) μ).toReal *
          (eLpNorm g (ENNReal.ofReal q) μ).toReal := by
    calc
      |(∫ x, s n x * g x ∂μ)| ≤ ∫ x, |s n x| * |g x| ∂μ := by
        simpa [abs_mul] using (abs_integral_le_integral_abs
          (f := fun x ↦ s n x * g x) ( μ := μ))
      _ ≤ (∫ x, ‖s n x‖ ^ p ∂μ) ^ (1 / p) *
          (∫ x, ‖g x‖ ^ q ∂μ) ^ (1 / q) :=
        integral_mul_norm_le_Lp_mul_Lq hpqR (hs n) hg
      _ = (eLpNorm (s n) (ENNReal.ofReal p) μ).toReal *
          (eLpNorm g (ENNReal.ofReal q) μ).toReal := by
        have hsNorm := (hs n).eLpNorm_eq_integral_rpow_norm
          (ENNReal.ofReal_ne_zero_iff.mpr hpqR.pos) ENNReal.ofReal_ne_top
        have hgNorm := hg.eLpNorm_eq_integral_rpow_norm
          (ENNReal.ofReal_ne_zero_iff.mpr hpqR.symm.pos) ENNReal.ofReal_ne_top
        rw [hsNorm, hgNorm]
        simp only [ENNReal.toReal_ofReal hpqR.nonneg,
          ENNReal.toReal_ofReal hpqR.symm.nonneg]
        rw [ENNReal.toReal_ofReal (Real.rpow_nonneg
              (integral_nonneg (fun x ↦ Real.rpow_nonneg (norm_nonneg _) _)) _),
            ENNReal.toReal_ofReal (Real.rpow_nonneg
              (integral_nonneg (fun x ↦ Real.rpow_nonneg (norm_nonneg _) _)) _)]
        simp only [one_div]
        rfl
  apply apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_limit_rep_aux_tendsto_abs_le
    ht
  intro n
  exact (hnorm n).trans (mul_le_mul_of_nonneg_right (hbound n)
    (ENNReal.toReal_nonneg))

/-- Banked (lemma-1, round 2): an interval with `b ≤ a` is empty, so its value is `0`. -/
lemma apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_limit_rep_aux_l1_rep_aux_zero
    (q : ℝ) (L : ℚ × ℚ → ℝ) (R : ℝ)
    (hstep : ∀ (F : Finset (ℚ × ℚ)) (c : ℚ × ℚ → ℝ),
      |∑ i ∈ F, c i * L i| ≤ R * (eLpNorm (fun x ↦ ∑ i ∈ F, c i *
          (Set.Ioc (i.1 : ℝ) i.2).indicator (fun _ ↦ (1 : ℝ)) x)
        (ENNReal.ofReal q) (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) :
    ∀ a b : ℚ, b ≤ a → L (a, b) = 0 := by
  intro a b hab
  have h := hstep {(a, b)} (fun _ ↦ 1)
  have hab' : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast hab
  have hi : Set.Ioc (a : ℝ) (b : ℝ) = ∅ := Set.Ioc_eq_empty (not_lt_of_ge hab')
  simp [hi] at h
  exact h

/-- Leaf (clipping). Only the part of an interval inside `[0,1]` counts: with
`clip t := min (max t 0) 1`, `L (a, b) = L (clip a, clip b)`. Route: by `hadd` cut `(a, b)` at
`0` and `1`; a piece outside `[0,1]` meets `Icc 0 1` in at most a point, so its indicator is
a.e. zero for `volume.restrict (Icc 0 1)`, its `eLpNorm` is `0`, and `hstep` with one interval
gives value `0`. For `b ≤ a` both sides are `0` by `_aux_zero`. -/
lemma apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_limit_rep_aux_l1_rep_aux_clip
    (q : ℝ) (hq : 1 < q) (L : ℚ × ℚ → ℝ) (R : ℝ)
    (hadd : ∀ a b c : ℚ, a ≤ b → b ≤ c → L (a, c) = L (a, b) + L (b, c))
    (hstep : ∀ (F : Finset (ℚ × ℚ)) (c : ℚ × ℚ → ℝ),
      |∑ i ∈ F, c i * L i| ≤ R * (eLpNorm (fun x ↦ ∑ i ∈ F, c i *
          (Set.Ioc (i.1 : ℝ) i.2).indicator (fun _ ↦ (1 : ℝ)) x)
        (ENNReal.ofReal q) (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) :
    ∀ a b : ℚ, L (a, b) = L (min (max a 0) 1, min (max b 0) 1) := by
  sorry

/-- Leaf (absolute-continuity bound). For disjoint rational intervals inside `[0,1]`,
`∑ |L (u i, v i)| ≤ R (∑ (v i - u i))^(1/q)`. Route: `hstep` on the image finset with
coefficients `c = sign ∘ L`; the indicators are disjoint, so the step function takes values in
`{-1, 0, 1}` with support of measure `∑ (v i - u i)`, and its `eLpNorm` at `q` is that measure
to the power `1/q` (`eLpNorm_indicator_const`-style computation after rewriting `|step|` as
the indicator of the union). Mind that `Finset.image` may merge equal pairs; disjointness of
nonempty intervals rules that out, and empty ones contribute `0`. -/
lemma apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_limit_rep_aux_l1_rep_aux_abs_sum
    (q : ℝ) (hq : 1 < q) (L : ℚ × ℚ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hstep : ∀ (F : Finset (ℚ × ℚ)) (c : ℚ × ℚ → ℝ),
      |∑ i ∈ F, c i * L i| ≤ R * (eLpNorm (fun x ↦ ∑ i ∈ F, c i *
          (Set.Ioc (i.1 : ℝ) i.2).indicator (fun _ ↦ (1 : ℝ)) x)
        (ENNReal.ofReal q) (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) :
    ∀ (n : ℕ) (u v : ℕ → ℚ), (∀ i ∈ Finset.range n, 0 ≤ u i ∧ u i ≤ v i ∧ v i ≤ 1) →
      Set.PairwiseDisjoint (↑(Finset.range n)) (fun i ↦ Set.Ioc (u i : ℝ) (v i)) →
      ∑ i ∈ Finset.range n, |L (u i, v i)| ≤
        R * (∑ i ∈ Finset.range n, ((v i : ℝ) - u i)) ^ (1 / q) := by
  sorry

/-- Leaf (extension to an absolutely continuous function). From additivity and the
absolute-continuity bound, `L` is the increment of an absolutely continuous `F` on `[0,1]`.
Route: `G r := L (0, r)` on `ℚ ∩ [0,1]`; `habs` with one interval gives
`|G b - G a| ≤ R (b - a)^(1/q)`, so `G` is uniformly continuous and extends (e.g.
`DenseInducing.extend` / `UniformContinuous` extension on the subtype, or by an explicit
`limUnder` along rationals) to a continuous `F` on `Icc 0 1`, set constant outside. Passing to
the limit in `habs` (rational endpoints approximating real ones, keeping disjointness by
shrinking) gives the ε–δ form `absolutelyContinuousOnInterval_iff` with
`δ := (ε / (R + 1))^q`. -/
lemma apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_limit_rep_aux_l1_rep_aux_extend
    (q : ℝ) (hq : 1 < q) (L : ℚ × ℚ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hadd : ∀ a b c : ℚ, a ≤ b → b ≤ c → L (a, c) = L (a, b) + L (b, c))
    (habs : ∀ (n : ℕ) (u v : ℕ → ℚ), (∀ i ∈ Finset.range n, 0 ≤ u i ∧ u i ≤ v i ∧ v i ≤ 1) →
      Set.PairwiseDisjoint (↑(Finset.range n)) (fun i ↦ Set.Ioc (u i : ℝ) (v i)) →
      ∑ i ∈ Finset.range n, |L (u i, v i)| ≤
        R * (∑ i ∈ Finset.range n, ((v i : ℝ) - u i)) ^ (1 / q)) :
    ∃ F : ℝ → ℝ, AbsolutelyContinuousOnInterval F 0 1 ∧
      ∀ a b : ℚ, 0 ≤ a → a ≤ b → b ≤ 1 → L (a, b) = F b - F a := by
  sorry

/-- Leaf (FTC on a clipped interval). For `F` absolutely continuous on `[0,1]` and `a ≤ b`,
pairing `deriv F` with the indicator of `Ioc a b` over `[0,1]` gives `F b' - F a'`, where
`t' := min (max t 0) 1`. Route: on `Icc 0 1` the indicator of `Ioc a b` agrees a.e. (off the
point `0`) with that of `Ioc a' b'`; then `setIntegral_indicator`, `Ioc a' b' ⊆ Icc 0 1`,
`intervalIntegral.integral_of_le`, and `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`
for `F` on `a'..b'` (restrict with `absolutelyContinuousOnInterval_iff` /
`AbsolutelyContinuousOnInterval.disjWithin_mono`). -/
lemma apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_limit_rep_aux_l1_rep_aux_ftc
    (F : ℝ → ℝ) (hF : AbsolutelyContinuousOnInterval F 0 1) (a b : ℝ) (hab : a ≤ b) :
    ∫ x in Set.Icc (0 : ℝ) 1, deriv F x * (Set.Ioc a b).indicator (fun _ ↦ (1 : ℝ)) x =
      F (min (max b 0) 1) - F (min (max a 0) 1) := by
  sorry

/-- Leaf (integrable representative; the analytic core). An interval function on rational
intervals, additive on adjacent intervals and bounded on step functions by `R ‖·‖_q`, is
integration against some `f₀ ∈ L¹([0,1])`. Route: `F t := L (0, t)` is uniformly continuous on
`ℚ ∩ [0,1]` (single-interval bound `R (b - a)^(1/q)`), so extends to a continuous `F`; the step
bound with signs gives `∑ |F b_k - F a_k| ≤ R (∑ (b_k - a_k))^(1/q)` on disjoint intervals, so
`F` is absolutely continuous. Either split `F` into monotone continuous parts, take their
`StieltjesFunction.measure`s (both `≪ volume`) and set `f₀` to the difference of the
`rnDeriv`s, or use the dyadic averages of `L` as an `L¹`-bounded uniformly integrable
martingale and its `limitProcess`. Non-dyadic rational endpoints follow by continuity. -/
lemma apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_limit_rep_aux_l1_rep
    (p q : ℝ) (hp : 1 < p) (hq : 1 < q) (hpq : 1 / p + 1 / q = 1)
    (L : ℚ × ℚ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hadd : ∀ a b c : ℚ, a ≤ b → b ≤ c → L (a, c) = L (a, b) + L (b, c))
    (hstep : ∀ (F : Finset (ℚ × ℚ)) (c : ℚ × ℚ → ℝ),
      |∑ i ∈ F, c i * L i| ≤ R * (eLpNorm (fun x ↦ ∑ i ∈ F, c i *
          (Set.Ioc (i.1 : ℝ) i.2).indicator (fun _ ↦ (1 : ℝ)) x)
        (ENNReal.ofReal q) (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) :
    ∃ f₀, Integrable f₀ (volume.restrict (Set.Icc (0 : ℝ) 1)) ∧
      ∀ i : ℚ × ℚ, ∫ x in Set.Icc (0 : ℝ) 1,
        f₀ x * (Set.Ioc (i.1 : ℝ) i.2).indicator (fun _ ↦ (1 : ℝ)) x = L i := by
  have hzero :=
    apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_limit_rep_aux_l1_rep_aux_zero
      q L R hstep
  have hclip :=
    apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_limit_rep_aux_l1_rep_aux_clip
      q hq L R hadd hstep
  obtain ⟨F, hF, hFL⟩ :=
    apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_limit_rep_aux_l1_rep_aux_extend
      q hq L R hR hadd
      (apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_limit_rep_aux_l1_rep_aux_abs_sum
        q hq L R hR hstep)
  refine ⟨deriv F, ?_, ?_⟩
  · have h := hF.intervalIntegrable_deriv
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one] at h
    exact h
  · rintro ⟨a, b⟩
    rcases le_total a b with hab | hab
    · have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
      rw [apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_limit_rep_aux_l1_rep_aux_ftc
        F hF a b hab', hclip a b,
        hFL _ _ (le_min (le_max_right _ _) zero_le_one) (min_le_min_right _ (max_le_max_right _ hab))
          (min_le_right _ _)]
      push_cast
      rfl
    · have hab' : (b : ℝ) ≤ a := by exact_mod_cast hab
      simp [Set.Ioc_eq_empty (not_lt_of_ge hab'), hzero a b hab]

/-- Banked (lemma-2, round 2): bounded truncations of an integrable function lie in every
finite `Lᵠ` of `[0,1]`. -/
lemma apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_limit_rep_aux_memLp_aux_trunc_memLp
    (q M : ℝ) (hq : 1 < q) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : Integrable f (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    MemLp (fun x ↦ max (-M) (min M (f x))) (ENNReal.ofReal q)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  let μ := volume.restrict (Set.Icc (0 : ℝ) 1)
  have hc : Continuous (fun y : ℝ ↦ max (-M) (min M y)) :=
    continuous_const.max (continuous_const.min continuous_id)
  have hmeas : AEStronglyMeasurable (fun x ↦ max (-M) (min M (f x))) μ :=
    hc.comp_aestronglyMeasurable hf.aestronglyMeasurable
  have htop : MemLp (fun x ↦ max (-M) (min M (f x))) ⊤ μ := by
    apply memLp_top_of_bound hmeas M
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  exact htop.mono_exponent le_top

/-- Leaf (step approximation; no `f₀`). A bounded a.e.-strongly-measurable `g` is the a.e. limit
on `[0,1]` of uniformly bounded rational-interval step functions. Route: approximate `g` in `L¹`
by continuous functions (`MemLp.exists_hasCompactSupport_eLpNorm_sub_le` or
`Integrable.exists_continuous...`), clip them to `[-C, C]`, approximate each uniformly on `[0,1]`
by step functions on the grid `k / N` (uniform continuity), giving `L¹` convergence with bound
`C + 1`; extract an a.e. convergent subsequence (`TendstoInMeasure.exists_seq_tendsto_ae`). -/
-- BEGIN SEAT AREA
lemma apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_limit_rep_aux_memLp_aux_step_approx
    (g : ℝ → ℝ) (hg : AEStronglyMeasurable g (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (C : ℝ) (hC : ∀ x, |g x| ≤ C) :
    ∃ (F : ℕ → Finset (ℚ × ℚ)) (c : ℕ → ℚ × ℚ → ℝ) (D : ℝ),
      (∀ n x, |∑ i ∈ F n, c n i * (Set.Ioc (i.1 : ℝ) i.2).indicator (fun _ ↦ (1 : ℝ)) x| ≤ D) ∧
      ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
        Tendsto (fun n ↦ ∑ i ∈ F n, c n i * (Set.Ioc (i.1 : ℝ) i.2).indicator (fun _ ↦ (1 : ℝ)) x) atTop (nhds (g x)) := by
  sorry
-- END SEAT AREA

/-- Leaf (passing to the limit). If uniformly bounded step functions `s n` converge a.e. on
`[0,1]` to a bounded `g`, the step bound passes to `g`: `|∫ f₀ g| ≤ R ‖g‖_q`. Route: rewrite
`∑ c i ∫ f₀ 1_(a,b]` as `∫ f₀ (s n)` (`integral_finset_sum`, `integral_mul_left`); dominated
convergence with bound `D |f₀|` gives `∫ f₀ (s n) → ∫ f₀ g`; on the finite measure the bounded
a.e. convergence gives `eLpNorm (s n - g) q → 0` (`tendsto_Lp_finite_of_tendsto_ae` /
`tendstoInMeasure` + uniform integrability), hence `‖s n‖_q → ‖g‖_q`; `le_of_tendsto_of_tendsto'`. -/
lemma apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_limit_rep_aux_memLp_aux_pass_limit
    (p q : ℝ) (hp : 1 < p) (hq : 1 < q)
    (f₀ : ℝ → ℝ) (hf₀ : Integrable f₀ (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (R : ℝ) (hR : 0 ≤ R)
    (hstep : ∀ (F : Finset (ℚ × ℚ)) (c : ℚ × ℚ → ℝ),
      |∑ i ∈ F, c i * ∫ x in Set.Icc (0 : ℝ) 1,
          f₀ x * (Set.Ioc (i.1 : ℝ) i.2).indicator (fun _ ↦ (1 : ℝ)) x| ≤
        R * (eLpNorm (fun x ↦ ∑ i ∈ F, c i *
          (Set.Ioc (i.1 : ℝ) i.2).indicator (fun _ ↦ (1 : ℝ)) x)
        (ENNReal.ofReal q) (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal)
    (g : ℝ → ℝ) (hg : AEStronglyMeasurable g (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (C : ℝ) (hC : ∀ x, |g x| ≤ C)
    (F : ℕ → Finset (ℚ × ℚ)) (c : ℕ → ℚ × ℚ → ℝ) (D : ℝ)
    (hD : ∀ n x, |∑ i ∈ F n, c n i * (Set.Ioc (i.1 : ℝ) i.2).indicator (fun _ ↦ (1 : ℝ)) x| ≤ D)
    (hlim : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
        Tendsto (fun n ↦ ∑ i ∈ F n, c n i * (Set.Ioc (i.1 : ℝ) i.2).indicator (fun _ ↦ (1 : ℝ)) x) atTop (nhds (g x))) :
    |∫ x in Set.Icc (0 : ℝ) 1, f₀ x * g x| ≤
      R * (eLpNorm g (ENNReal.ofReal q) (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := by
  sorry

/-- Leaf (truncation bound). If every bounded test `g` has `|∫ f₀ g| ≤ R ‖g‖_q`, each truncation
`f_M := max (-M) (min M f₀)` has `∫ |f_M|^p ≤ R^p`. Route: test `g := sign f_M · |f_M|^(p-1)`
(bounded by `M^(p-1)`); pointwise `f₀ g ≥ |f_M|^p`; `(p-1) q = p` from `hpq`, so
`‖g‖_q = A^(1/q)` with `A := ∫ |f_M|^p` (finite, `_aux_trunc_memLp`); `A ≤ R A^(1/q)` gives
`A^(1/p) ≤ R` (case `A = 0` separately), so `A ≤ R^p`. -/
lemma apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_limit_rep_aux_memLp_aux_trunc_bound
    (p q : ℝ) (hp : 1 < p) (hq : 1 < q) (hpq : 1 / p + 1 / q = 1)
    (f₀ : ℝ → ℝ) (hf₀ : Integrable f₀ (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (R : ℝ) (hR : 0 ≤ R)
    (htest : ∀ g : ℝ → ℝ, AEStronglyMeasurable g (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ C : ℝ, (∀ x, |g x| ≤ C) →
        |∫ x in Set.Icc (0 : ℝ) 1, f₀ x * g x| ≤
          R * (eLpNorm g (ENNReal.ofReal q) (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) :
    ∀ M : ℝ, 0 ≤ M →
      ∫ x in Set.Icc (0 : ℝ) 1, |max (-M) (min M (f₀ x))| ^ p ≤ R ^ p := by
  sorry

/-- Leaf (monotone limit). If the truncations of a measurable `f₀` have `∫ |f_M|^p ≤ K` for all
`M ≥ 0`, then `f₀ ∈ Lᵖ([0,1])`. Route: `|f_n|^p ↑ |f₀|^p` pointwise along `M = n`;
`lintegral_iSup` / `lintegral_tendsto_of_tendsto_of_monotone` bounds `∫⁻ ‖f₀‖ₑ^p` by
`ENNReal.ofReal K` (each truncation is integrable, so `ofReal_integral_eq_lintegral_ofReal`);
conclude with `eLpNorm_lt_top` via `eLpNorm_eq_lintegral_rpow_enorm`. -/
lemma apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_limit_rep_aux_memLp_aux_mono
    (p : ℝ) (hp : 1 < p)
    (f₀ : ℝ → ℝ) (hf₀ : Integrable f₀ (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (K : ℝ)
    (hbd : ∀ M : ℝ, 0 ≤ M →
      ∫ x in Set.Icc (0 : ℝ) 1, |max (-M) (min M (f₀ x))| ^ p ≤ K) :
    MemLp f₀ (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  sorry

/-- Assembly (split 2026-10-19 after lemma-2's partial). An integrable `f₀` whose pairings with rational step functions are
bounded by `R ‖·‖_q` lies in `Lᵖ([0,1])`. Route: for the truncation `f_M := max (-M) (min M f₀)`
test against the bounded `g_M := sign f_M · |f_M|^(p-1)`, so `‖f_M‖_p^p ≤ ∫ f₀ g_M ≤ R ‖g_M‖_q
= R ‖f_M‖_p^(p-1)`; reach `g_M` from rational step functions that converge in `Lᵠ` and a.e.
with a uniform bound (dominated convergence against `f₀ ∈ L¹`); let `M → ∞` (monotone
convergence). -/
lemma apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_limit_rep_aux_memLp
    (p q : ℝ) (hp : 1 < p) (hq : 1 < q) (hpq : 1 / p + 1 / q = 1)
    (f₀ : ℝ → ℝ) (hf₀ : Integrable f₀ (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (R : ℝ) (hR : 0 ≤ R)
    (hstep : ∀ (F : Finset (ℚ × ℚ)) (c : ℚ × ℚ → ℝ),
      |∑ i ∈ F, c i * ∫ x in Set.Icc (0 : ℝ) 1,
          f₀ x * (Set.Ioc (i.1 : ℝ) i.2).indicator (fun _ ↦ (1 : ℝ)) x| ≤
        R * (eLpNorm (fun x ↦ ∑ i ∈ F, c i *
          (Set.Ioc (i.1 : ℝ) i.2).indicator (fun _ ↦ (1 : ℝ)) x)
        (ENNReal.ofReal q) (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal) :
    MemLp f₀ (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  have htest : ∀ g : ℝ → ℝ, AEStronglyMeasurable g (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ C : ℝ, (∀ x, |g x| ≤ C) →
        |∫ x in Set.Icc (0 : ℝ) 1, f₀ x * g x| ≤
          R * (eLpNorm g (ENNReal.ofReal q) (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal := by
    intro g hg C hC
    obtain ⟨F, c, D, hD, hlim⟩ := apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_limit_rep_aux_memLp_aux_step_approx g hg C hC
    exact apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_limit_rep_aux_memLp_aux_pass_limit p q hp hq f₀ hf₀ R hR hstep g hg C hC F c D hD hlim
  exact apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_limit_rep_aux_memLp_aux_mono p hp f₀ hf₀ (R ^ p)
    (apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_limit_rep_aux_memLp_aux_trunc_bound p q hp hq hpq f₀ hf₀ R hR htest)

/-- Leaf (the limit is an `Lᵖ` function). If the interval pairings of a uniformly `Lᵖ`-bounded
sequence converge for every rational interval, the limits are the pairings of one
`f₀ ∈ Lᵖ([0,1])`. Route: `L` is additive on adjacent intervals with
`|L(a,b)| ≤ R (b - a)^(1/q)`; it defines a signed measure `ν ≪ volume` on `[0,1]`; take
`f₀ := ν.rnDeriv`, and show `f₀ ∈ Lᵖ` by testing against step functions. -/
lemma apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_limit_rep
    (p q : ℝ) (hp : 1 < p) (hq : 1 < q) (hpq : 1 / p + 1 / q = 1)
    (s : ℕ → ℝ → ℝ)
    (hs : ∀ n, MemLp (s n) (ENNReal.ofReal p)
      (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ n : ℕ,
      (eLpNorm (s n) (ENNReal.ofReal p)
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ≤ R)
    (L : ℚ × ℚ → ℝ)
    (hL : ∀ i : ℚ × ℚ, Tendsto (fun n ↦ ∫ x in Set.Icc (0 : ℝ) 1,
      s n x * (Set.Ioc (i.1 : ℝ) i.2).indicator (fun _ ↦ (1 : ℝ)) x) atTop (nhds (L i))) :
    ∃ f₀, MemLp f₀ (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)) ∧
      ∀ i : ℚ × ℚ, ∫ x in Set.Icc (0 : ℝ) 1,
        f₀ x * (Set.Ioc (i.1 : ℝ) i.2).indicator (fun _ ↦ (1 : ℝ)) x = L i := by
  have hstep :=
    apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_limit_rep_aux_step_bound
      p q hp hq hpq s hs R hR hbound L hL
  obtain ⟨f₀, hf₀, hrep⟩ :=
    apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_limit_rep_aux_l1_rep
      p q hp hq hpq L R hR
      (apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_limit_rep_aux_add
        p q hp hpq s hs L hL) hstep
  refine ⟨f₀, ?_, hrep⟩
  exact apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_limit_rep_aux_memLp
    p q hp hq hpq f₀ hf₀ R hR (fun F c ↦ by simpa only [hrep] using hstep F c)

/-- Leaf (density). Finite combinations of indicators of rational intervals are dense in
`Lᵠ([0,1])` for `1 < q < ∞`. Route: continuous functions are dense
(`MemLp.exists_hasCompactSupport_eLpNorm_sub_le` or `Lp.boundedContinuousFunction_dense`), and a
uniformly continuous function on `[0,1]` is uniformly close to a rational step function. -/
lemma apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_step_dense
    (q : ℝ) (hq : 1 < q)
    (h : ℝ → ℝ) (hh : MemLp h (ENNReal.ofReal q) (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (F : Finset (ℚ × ℚ)) (c : ℚ × ℚ → ℝ),
      eLpNorm (fun x ↦ h x - ∑ i ∈ F, c i *
          (Set.Ioc (i.1 : ℝ) i.2).indicator (fun _ ↦ (1 : ℝ)) x)
        (ENNReal.ofReal q) (volume.restrict (Set.Icc (0 : ℝ) 1)) < ENNReal.ofReal ε := by
  sorry

/-- Leaf (ε/3 argument). Weak convergence against rational interval indicators, plus a uniform
`Lᵖ` bound and density of rational step functions in `Lᵠ`, gives convergence against every
`h ∈ Lᵠ([0,1])`. Route: linearity of the integral for finite combinations, then Hölder
(`integral_mul_le_Lp_mul_Lq`-type bounds) on `h - g`. -/
lemma apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_extend
    (p q : ℝ) (hp : 1 < p) (hq : 1 < q) (hpq : 1 / p + 1 / q = 1)
    (s : ℕ → ℝ → ℝ)
    (hs : ∀ n, MemLp (s n) (ENNReal.ofReal p)
      (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ n : ℕ,
      (eLpNorm (s n) (ENNReal.ofReal p)
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ≤ R)
    (f₀ : ℝ → ℝ) (hf₀ : MemLp f₀ (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hstep : ∀ i : ℚ × ℚ, Tendsto (fun n ↦ ∫ x in Set.Icc (0 : ℝ) 1,
      s n x * (Set.Ioc (i.1 : ℝ) i.2).indicator (fun _ ↦ (1 : ℝ)) x) atTop
        (nhds (∫ x in Set.Icc (0 : ℝ) 1,
          f₀ x * (Set.Ioc (i.1 : ℝ) i.2).indicator (fun _ ↦ (1 : ℝ)) x)))
    (hdense : ∀ h, MemLp h (ENNReal.ofReal q) (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ ε : ℝ, 0 < ε → ∃ (F : Finset (ℚ × ℚ)) (c : ℚ × ℚ → ℝ),
        eLpNorm (fun x ↦ h x - ∑ i ∈ F, c i *
            (Set.Ioc (i.1 : ℝ) i.2).indicator (fun _ ↦ (1 : ℝ)) x)
          (ENNReal.ofReal q) (volume.restrict (Set.Icc (0 : ℝ) 1)) < ENNReal.ofReal ε) :
    ∀ h, MemLp h (ENNReal.ofReal q) (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      Tendsto (fun n ↦ ∫ x in Set.Icc (0 : ℝ) 1, s n x * h x) atTop
        (nhds (∫ x in Set.Icc (0 : ℝ) 1, f₀ x * h x)) := by
  sorry

/-- The analytic core: weak sequential compactness of a uniformly bounded `Lᵖ` tail,
formulated for representatives and only against the concrete `Lᵠ` integral pairing. -/
lemma apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_core
    (p q : ℝ) (hp : 1 < p) (hq : 1 < q) (hpq : 1 / p + 1 / q = 1)
    (s : ℕ → ℝ → ℝ)
    (hs : ∀ n, MemLp (s n) (ENNReal.ofReal p)
      (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hbounded : ∃ R : ℝ, 0 ≤ R ∧ ∀ n : ℕ,
      (eLpNorm (s n) (ENNReal.ofReal p)
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ≤ R) :
    ∃ f₀, MemLp f₀ (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ h, MemLp h (ENNReal.ofReal q) (volume.restrict (Set.Icc (0 : ℝ) 1)) →
          Tendsto (fun n ↦ ∫ x in Set.Icc (0 : ℝ) 1, s (φ n) x * h x) atTop
            (nhds (∫ x in Set.Icc (0 : ℝ) 1, f₀ x * h x)) := by
  obtain ⟨R, hR, hb⟩ := hbounded
  obtain ⟨φ, hφ, L, hL⟩ :=
    apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_diagonal
      (fun n (i : ℚ × ℚ) ↦ ∫ x in Set.Icc (0 : ℝ) 1,
        s n x * (Set.Ioc (i.1 : ℝ) i.2).indicator (fun _ ↦ (1 : ℝ)) x)
      (fun i ↦ ⟨R, fun n ↦ (apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_indicator_bound
        p q hp hq hpq (s n) (hs n) _ _).trans (hb n)⟩)
  obtain ⟨f₀, hf₀, hrep⟩ :=
    apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_limit_rep
      p q hp hq hpq (fun n ↦ s (φ n)) (fun n ↦ hs (φ n)) R hR (fun n ↦ hb (φ n)) L hL
  refine ⟨f₀, hf₀, φ, hφ, ?_⟩
  exact apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_extend
    p q hp hq hpq (fun n ↦ s (φ n)) (fun n ↦ hs (φ n)) R hR (fun n ↦ hb (φ n)) f₀ hf₀
    (fun i ↦ by rw [hrep i]; exact hL i)
    (fun h hh ε hε ↦
      apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_step_dense
        q hq h hh ε hε)

lemma apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness
    (p q : ℝ) (hp : 1 < p) (hq : 1 < q) (hpq : 1 / p + 1 / q = 1)
    (s : ℕ → ℝ → ℝ)
    (hs : ∀ n, MemLp (s n) (ENNReal.ofReal p)
      (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hbounded : ∃ R : ℝ, 0 ≤ R ∧ ∀ᶠ n in atTop,
      (eLpNorm (s n) (ENNReal.ofReal p)
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ≤ R) :
    ∃ f₀, MemLp f₀ (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ h, MemLp h (ENNReal.ofReal q) (volume.restrict (Set.Icc (0 : ℝ) 1)) →
          Tendsto (fun n => ∫ x in Set.Icc (0 : ℝ) 1, s (φ n) x * h x) atTop
            (nhds (∫ x in Set.Icc (0 : ℝ) 1, f₀ x * h x)) := by
  obtain ⟨R, hR, k, hk⟩ :=
    apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_tail
      p s hbounded
  obtain ⟨f₀, hf₀, φ, hφ, hconv⟩ :=
    apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness_aux_core
      p q hp hq hpq (fun n ↦ s (k + n)) (fun n ↦ hs (k + n)) ⟨R, hR, hk⟩
  refine ⟨f₀, hf₀, fun n ↦ k + φ n, ?_, ?_⟩
  · exact fun a b hab ↦ Nat.add_lt_add_left (hφ hab) k
  · intro h hh
    simpa [add_assoc] using hconv h hh

/-- A coercive minimizing sequence has a weakly convergent subsequence
(eventual boundedness, then `Lp` weak compactness). -/
lemma apm_m93j05_exists_minimizer_weak_subsequence
    (N : ℕ) (p q : ℝ) (hp : 1 < p) (hq : 1 < q)
    (hpq : 1 / p + 1 / q = 1) (g : ℝ → ℝ)
    (hg : MemLp g (ENNReal.ofReal q) (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hcoercive : ∀ A : ℝ, ∃ R : ℝ, 0 ≤ R ∧ ∀ f,
      MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      apm_m93j05_J N p g f ≤ A →
      (eLpNorm f (ENNReal.ofReal p)
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ≤ R)
    (s : ℕ → ℝ → ℝ)
    (hs : ∀ n, MemLp (s n) (ENNReal.ofReal p)
      (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hmin : ∀ f, MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ k : ℕ, ∀ᶠ n in atTop,
        apm_m93j05_J N p g (s n) ≤ apm_m93j05_J N p g f + 1 / (k + 1 : ℝ)) :
    ∃ f₀, MemLp f₀ (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ h, MemLp h (ENNReal.ofReal q) (volume.restrict (Set.Icc (0 : ℝ) 1)) →
          Tendsto (fun n => ∫ x in Set.Icc (0 : ℝ) 1, s (φ n) x * h x) atTop
            (nhds (∫ x in Set.Icc (0 : ℝ) 1, f₀ x * h x)) := by
  apply apm_m93j05_exists_minimizer_weak_subsequence_aux_lp_weak_compactness
    p q hp hq hpq s hs
  exact apm_m93j05_exists_minimizer_weak_subsequence_aux_eventually_bounded
    N p q hp g hcoercive s hs hmin

/-- Weak lower semicontinuity turns an approximately minimizing weakly convergent subsequence into
an actual minimizer.  The analytic inputs are hypotheses, keeping this leaf independent. -/
lemma apm_m93j05_exists_minimizer_lsc_closure
    (N : ℕ) (p q : ℝ) (hp : 1 < p) (hq : 1 < q)
    (hpq : 1 / p + 1 / q = 1) (g : ℝ → ℝ)
    (hg : MemLp g (ENNReal.ofReal q) (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hlsc : let μ := volume.restrict (Set.Icc (0 : ℝ) 1)
      ∀ g, MemLp g (ENNReal.ofReal q) μ → ∀ (f : ℝ → ℝ) (s : ℕ → ℝ → ℝ),
        MemLp f (ENNReal.ofReal p) μ → (∀ n, MemLp (s n) (ENNReal.ofReal p) μ) →
        (∀ h, MemLp h (ENNReal.ofReal q) μ →
          Tendsto (fun n => ∫ x, s n x * h x ∂μ) atTop
            (nhds (∫ x, f x * h x ∂μ))) →
        ∀ r, (∃ᶠ n in atTop, apm_m93j05_J N p g (s n) ≤ r) →
          apm_m93j05_J N p g f ≤ r)
    (s : ℕ → ℝ → ℝ)
    (hs : ∀ n, MemLp (s n) (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hmin : ∀ f, MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      ∀ k : ℕ, ∀ᶠ n in atTop,
        apm_m93j05_J N p g (s n) ≤ apm_m93j05_J N p g f + 1 / (k + 1 : ℝ))
    (f₀ : ℝ → ℝ)
    (hf₀ : MemLp f₀ (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hweak : ∀ h, MemLp h (ENNReal.ofReal q) (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      Tendsto (fun n => ∫ x in Set.Icc (0 : ℝ) 1, s (φ n) x * h x) atTop
        (nhds (∫ x in Set.Icc (0 : ℝ) 1, f₀ x * h x))) :
    ∃ f₀, MemLp f₀ (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)) ∧
      ∀ f, MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)) →
        apm_m93j05_J N p g f₀ ≤ apm_m93j05_J N p g f := by
  refine ⟨f₀, hf₀, ?_⟩
  intro f hf
  have hbound : ∀ k : ℕ,
      apm_m93j05_J N p g f₀ ≤ apm_m93j05_J N p g f + 1 / (k + 1 : ℝ) := by
    intro k
    apply hlsc g hg f₀ (fun n ↦ s (φ n)) hf₀ (fun n ↦ hs (φ n)) hweak
    exact ((hmin f hf k).filter_mono hφ.tendsto_atTop).frequently
  have ht : Tendsto
      (fun k : ℕ ↦ apm_m93j05_J N p g f + 1 / (k + 1 : ℝ)) atTop
      (nhds (apm_m93j05_J N p g f)) := by
    convert tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) using 1 <;> simp
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds ht hbound

theorem apm_m93j05_exists_minimizer
    (N : ℕ) (p q : ℝ) (hp : 1 < p) (hq : 1 < q)
    (hpq : 1 / p + 1 / q = 1) :
    let μ := volume.restrict (Set.Icc (0 : ℝ) 1)
    ∀ g, MemLp g (ENNReal.ofReal q) μ →
      ∃ f₀, MemLp f₀ (ENNReal.ofReal p) μ ∧
        ∀ f, MemLp f (ENNReal.ofReal p) μ →
          apm_m93j05_J N p g f₀ ≤ apm_m93j05_J N p g f := by
  intro μ g hg
  have hcoercive := apm_m93j05_exists_minimizer_coercive N p q hp hq hpq g hg
  obtain ⟨s, hs, hmin⟩ :=
    apm_m93j05_exists_minimizer_minimizing_sequence N p q hp hq hpq g hg
  obtain ⟨f₀, hf₀, φ, hφ, hweak⟩ :=
    apm_m93j05_exists_minimizer_weak_subsequence N p q hp hq hpq g hg
      hcoercive s hs hmin
  exact apm_m93j05_exists_minimizer_lsc_closure N p q hp hq hpq g hg
    (apm_m93j05_weak_lowerSemicontinuous N p q hp hq hpq) s hs hmin
    f₀ hf₀ φ hφ hweak

lemma apm_m93j05_stationary_at_minimizer_aux_memLp_path
    (p t : ℝ) (f h : ℝ → ℝ) (hf : MemLp f (ENNReal.ofReal p)
      (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hh : MemLp h (ENNReal.ofReal p)
      (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    MemLp (f + t • h) (ENNReal.ofReal p)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  exact hf.add (hh.const_smul t)

/-! ### Split of `apm_m93j05_stationary_at_minimizer` (claude-14, 2026-10-13, after a partial that
banked the path-admissibility helper above). (D1) is the analytic core; (D) takes it as a hypothesis;
the Fermat step is assembled below. -/

lemma apm_m93j05_lp_rpow_differentiableAt_aux_memLp_line
    (p t : ℝ) (a b : ℝ → ℝ)
    (ha : MemLp a (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hb : MemLp b (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    MemLp (fun x ↦ a x + t * b x) (ENNReal.ofReal p)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  exact ha.add (hb.const_smul t)

/-! Split of `apm_m93j05_lp_rpow_differentiableAt` (claude-14, after a partial that banked `_aux_memLp_line`):
(D1a) norm power = integral, (D1c) pointwise derivative, (D1b) differentiation under the integral
given (D1c). All parallel. -/

theorem apm_m93j05_rpow_eLpNorm_eq_integral (p : ℝ) (hp : 0 < p) (u : ℝ → ℝ)
    (hu : MemLp u (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    Real.rpow (eLpNorm u (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal p = ∫ x, |u x| ^ p ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  let μ := volume.restrict (Set.Icc (0 : ℝ) 1)
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp
  have hpTop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hnorm := hu.eLpNorm_eq_integral_rpow_norm hp0 hpTop
  have hnonneg : 0 ≤ ∫ x, |u x| ^ p ∂μ :=
    MeasureTheory.integral_nonneg (fun x ↦ by positivity)
  rw [hnorm]
  simp only [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hnonneg _)]
  change ((∫ x, |u x| ^ p ∂μ) ^ p⁻¹) ^ p = ∫ x, |u x| ^ p ∂μ
  rw [← Real.rpow_mul hnonneg]
  field_simp
  exact Real.rpow_one _

theorem apm_m93j05_abs_rpow_line_hasDerivAt (p : ℝ) (hp : 1 < p) (x y s : ℝ) :
    HasDerivAt (fun r : ℝ ↦ |x + r * y| ^ p)
      (p * |x + s * y| ^ (p - 2) * (x + s * y) * y) s := by
  have hinner : HasDerivAt (fun r : ℝ ↦ x + r * y) y s := by
    simpa [id] using ((hasDerivAt_id s).mul_const y).const_add x
  exact (hasDerivAt_abs_rpow (x + s * y) hp).comp s hinner

theorem apm_m93j05_integral_abs_rpow_line_differentiableAt (p : ℝ) (hp : 1 < p)
    (hD1c : ∀ x y s : ℝ, HasDerivAt (fun r : ℝ ↦ |x + r * y| ^ p)
      (p * |x + s * y| ^ (p - 2) * (x + s * y) * y) s)
    (a b : ℝ → ℝ) (ha : MemLp a (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1))) (hb : MemLp b (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    DifferentiableAt ℝ (fun t : ℝ ↦ ∫ x, |a x + t * b x| ^ p ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) 0 := by
  let μ := volume.restrict (Set.Icc (0 : ℝ) 1)
  let F : ℝ → ℝ → ℝ := fun t x ↦ |a x + t * b x| ^ p
  let F' : ℝ → ℝ → ℝ := fun t x ↦
    p * |a x + t * b x| ^ (p - 2) * (a x + t * b x) * b x
  let c : ℝ → ℝ := fun x ↦ |a x| + |b x|
  let q : ENNReal := ENNReal.ofReal (p - 1)
  have hp0 : 0 < p := by linarith
  have hq0 : q ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  have hqtop : q ≠ ⊤ := ENNReal.ofReal_ne_top
  have hc : MemLp c (ENNReal.ofReal p) μ := by
    exact ha.norm.add hb.norm
  have hpow : MemLp (fun x ↦ c x ^ (p - 1))
      (ENNReal.ofReal p / q) μ := by
    have heq : (fun x ↦ ‖c x‖ ^ q.toReal) = fun x ↦ c x ^ (p - 1) := by
      funext x
      rw [show ‖c x‖ = c x by
        rw [Real.norm_eq_abs, abs_of_nonneg]
        exact add_nonneg (abs_nonneg _) (abs_nonneg _)]
      simp [q, ENNReal.toReal_ofReal (by linarith : 0 ≤ p - 1)]
    rw [← heq]
    exact hc.norm_rpow_div q
  have hr : Real.HolderConjugate (p / (p - 1)) p := by
    exact (Real.holderConjugate_iff_eq_conjExponent hp).2 rfl |>.symm
  have hholder : ENNReal.HolderTriple (ENNReal.ofReal p / q) (ENNReal.ofReal p) 1 := by
    simpa [q, ENNReal.ofReal_div_of_pos (by linarith : 0 < p - 1)] using
      hr.ennrealOfReal
  letI := hholder
  have hprod : Integrable (fun x ↦ c x ^ (p - 1) * |b x|) μ :=
    hpow.integrable_mul hb.norm
  have hbound : Integrable (fun x ↦ p * (c x ^ (p - 1) * |b x|)) μ :=
    hprod.const_mul p
  have hF0 : Integrable (F 0) μ := by
    simpa [F, ENNReal.toReal_ofReal hp0.le] using
      ha.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
  have hmeas : ∀ᶠ t in nhds (0 : ℝ), AEStronglyMeasurable (F t) μ := by
    filter_upwards with t
    exact (((ha.1.add (hb.1.const_smul t)).norm.aemeasurable.pow_const p).aestronglyMeasurable)
  have hF'meas : AEStronglyMeasurable (F' 0) μ := by
    simpa [F', mul_assoc] using (((ha.1.norm.aemeasurable.pow_const (p - 2)).mul
      ha.1.aemeasurable |>.mul hb.1.aemeasurable).const_mul p).aestronglyMeasurable
  have hderiv : ∀ᵐ x ∂μ, ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      HasDerivAt (F · x) (F' t x) t := by
    filter_upwards with x
    intro t ht
    exact hD1c (a x) (b x) t
  have hle : ∀ᵐ x ∂μ, ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      ‖F' t x‖ ≤ p * (c x ^ (p - 1) * |b x|) := by
    filter_upwards with x
    intro t ht
    dsimp [F', c]
    have ht' : |t| ≤ 1 := (abs_le).2 ht
    have hz : |a x + t * b x| ≤ |a x| + |b x| := by
      calc
        _ ≤ |a x| + |t| * |b x| := by simpa [abs_mul] using abs_add_le (a x) (t * b x)
        _ ≤ _ := by
          gcongr
          exact mul_le_of_le_one_left (abs_nonneg _) ht'
    have hp1 : 0 ≤ p - 1 := by linarith
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hp0,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    have hid : |a x + t * b x| ^ (p - 2) * |a x + t * b x| =
        |a x + t * b x| ^ (p - 1) := by
      by_cases hzero : |a x + t * b x| = 0
      · rw [hzero, mul_zero, Real.zero_rpow (by linarith)]
      conv_lhs => rhs; rw [← Real.rpow_one |a x + t * b x|]
      rw [← Real.rpow_add (lt_of_le_of_ne (abs_nonneg _) (Ne.symm hzero))]
      congr 1
      ring
    calc
      p * |a x + t * b x| ^ (p - 2) * |a x + t * b x| * |b x| =
          p * (|a x + t * b x| ^ (p - 2) * |a x + t * b x|) * |b x| := by ring
      _ = p * |a x + t * b x| ^ (p - 1) * |b x| := by rw [hid]
      _ ≤ p * (c x ^ (p - 1) * |b x|) := by
        dsimp [c]
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left ?_ hp0.le
        apply mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        exact Real.rpow_le_rpow (abs_nonneg _) hz hp1
  have hs : Set.Icc (-1 : ℝ) 1 ∈ nhds (0 : ℝ) := by
    exact mem_nhds_iff.mpr ⟨Set.Ioo (-1) 1, Set.Ioo_subset_Icc_self,
      isOpen_Ioo, by norm_num⟩
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun x ↦ p * (c x ^ (p - 1) * |b x|))
    hs hmeas hF0 hF'meas hle hbound hderiv).2.differentiableAt

/-- (D1) For `p > 1`, `t ↦ ‖a + t b‖ₚᵖ` is differentiable at `0`
(derivative `p ∫ |a|^(p-2) a b`; dominate the difference quotient by `p (|a|+|b|)^(p-1) |b|`). -/
theorem apm_m93j05_lp_rpow_differentiableAt (p : ℝ) (hp : 1 < p) :
    ∀ (a b : ℝ → ℝ), MemLp a (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)) → MemLp b (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      DifferentiableAt ℝ (fun t : ℝ ↦ Real.rpow
        (eLpNorm (fun x ↦ a x + t * b x) (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal p) 0 := by
  intro a b ha hb
  have hfun : (fun t : ℝ ↦ Real.rpow
      (eLpNorm (fun x ↦ a x + t * b x) (ENNReal.ofReal p)
        (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal p) =
      fun t : ℝ ↦ ∫ x, |a x + t * b x| ^ p ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    funext t
    exact apm_m93j05_rpow_eLpNorm_eq_integral p (by linarith) _
      (apm_m93j05_lp_rpow_differentiableAt_aux_memLp_line p t a b ha hb)
  rw [hfun]
  exact apm_m93j05_integral_abs_rpow_line_differentiableAt p hp
    (apm_m93j05_abs_rpow_line_hasDerivAt p hp) a b ha hb

/-- (D) The energy is differentiable along every admissible line. Truncation is linear along the
line (`f₀`, `h` are integrable), the `L²` term is a quadratic polynomial in `t` (finite trigonometric
sums), the pairing is linear, and the `Lᵖ` term is (D1) applied to `(I − Φ) f₀`, `(I − Φ) h`. -/
theorem apm_m93j05_J_path_differentiableAt (N : ℕ) (p q : ℝ) (hp : 1 < p) (hq : 1 < q)
    (hpq : 1 / p + 1 / q = 1)
    (hD1 : ∀ (a b : ℝ → ℝ), MemLp a (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)) → MemLp b (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      DifferentiableAt ℝ (fun t : ℝ ↦ Real.rpow
        (eLpNorm (fun x ↦ a x + t * b x) (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal p) 0)
    (g f₀ h : ℝ → ℝ) (hg : MemLp g (ENNReal.ofReal q) (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hf₀ : MemLp f₀ (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1))) (hh : MemLp h (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    DifferentiableAt ℝ (fun t : ℝ ↦ apm_m93j05_J N p g (f₀ + t • h)) 0 := by
  let μ := volume.restrict (Set.Icc (0 : ℝ) 1)
  have hfi : Integrable f₀ μ := hf₀.integrable (by rw [ENNReal.one_le_ofReal]; linarith)
  have hhi : Integrable h μ := hh.integrable (by rw [ENNReal.one_le_ofReal]; linarith)
  have htrunc : ∀ (r : ℝ) (v : ℝ → ℝ), MemLp (apm_m93j05_trunc N v)
      (ENNReal.ofReal r) μ := by
    intro r v
    let C : ℝ := |∫ x in Set.Icc (0 : ℝ) 1, v x| +
      ∑ j ∈ Finset.Icc 1 N,
        (|apm_m93j05_cosCoeff v j| + |apm_m93j05_sinCoeff v j|)
    apply MemLp.of_bound (C := C)
    · exact (apm_m93j05_trunc_split_aux_continuous N v).aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs]
      unfold apm_m93j05_trunc
      calc
        |_ + _| ≤ |∫ z in Set.Icc (0 : ℝ) 1, v z| +
            |∑ j ∈ Finset.Icc 1 N, _| := abs_add_le _ _
        _ ≤ C := by
          dsimp [C]
          apply add_le_add le_rfl
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          apply Finset.sum_le_sum
          intro j hj
          calc
            |_ + _| ≤ |_| + |_| := abs_add_le _ _
            _ ≤ |apm_m93j05_cosCoeff v j| + |apm_m93j05_sinCoeff v j| := by
              simp only [abs_mul]
              exact add_le_add
                (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
                (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _))
  have hcos (v : ℝ → ℝ) (hv : Integrable v μ) (j : ℕ) :
      Integrable (fun x ↦ v x * Real.cos (j * 2 * Real.pi * x)) μ := by
    exact hv.mul_bdd
      ((Real.continuous_cos.comp (by fun_prop)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (j * 2 * Real.pi * x))
  have hsin (v : ℝ → ℝ) (hv : Integrable v μ) (j : ℕ) :
      Integrable (fun x ↦ v x * Real.sin (j * 2 * Real.pi * x)) μ := by
    exact hv.mul_bdd
      ((Real.continuous_sin.comp (by fun_prop)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (j * 2 * Real.pi * x))
  have hmean (t : ℝ) : (∫ x, f₀ x + t * h x ∂μ) =
      (∫ x, f₀ x ∂μ) + t * ∫ x, h x ∂μ := by
    rw [MeasureTheory.integral_add hfi (hhi.const_mul t),
      MeasureTheory.integral_const_mul]
  have hcoslin (t : ℝ) (j : ℕ) :
      (∫ x, (f₀ x + t * h x) * Real.cos (j * 2 * Real.pi * x) ∂μ) =
        (∫ x, f₀ x * Real.cos (j * 2 * Real.pi * x) ∂μ) +
          t * ∫ x, h x * Real.cos (j * 2 * Real.pi * x) ∂μ := by
    rw [show (fun x ↦ (f₀ x + t * h x) * Real.cos (j * 2 * Real.pi * x)) =
      fun x ↦ f₀ x * Real.cos (j * 2 * Real.pi * x) +
        t * (h x * Real.cos (j * 2 * Real.pi * x)) by funext x; ring]
    rw [MeasureTheory.integral_add (hcos f₀ hfi j) ((hcos h hhi j).const_mul t),
      MeasureTheory.integral_const_mul]
  have hsinlin (t : ℝ) (j : ℕ) :
      (∫ x, (f₀ x + t * h x) * Real.sin (j * 2 * Real.pi * x) ∂μ) =
        (∫ x, f₀ x * Real.sin (j * 2 * Real.pi * x) ∂μ) +
          t * ∫ x, h x * Real.sin (j * 2 * Real.pi * x) ∂μ := by
    rw [show (fun x ↦ (f₀ x + t * h x) * Real.sin (j * 2 * Real.pi * x)) =
      fun x ↦ f₀ x * Real.sin (j * 2 * Real.pi * x) +
        t * (h x * Real.sin (j * 2 * Real.pi * x)) by funext x; ring]
    rw [MeasureTheory.integral_add (hsin f₀ hfi j) ((hsin h hhi j).const_mul t),
      MeasureTheory.integral_const_mul]
  have hccoeff (t : ℝ) (j : ℕ) : apm_m93j05_cosCoeff (f₀ + t • h) j =
      apm_m93j05_cosCoeff f₀ j + t * apm_m93j05_cosCoeff h j := by
    unfold apm_m93j05_cosCoeff
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hcoslin]
    ring
  have hscoeff (t : ℝ) (j : ℕ) : apm_m93j05_sinCoeff (f₀ + t • h) j =
      apm_m93j05_sinCoeff f₀ j + t * apm_m93j05_sinCoeff h j := by
    unfold apm_m93j05_sinCoeff
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hsinlin]
    ring
  have hlinear (t : ℝ) : apm_m93j05_trunc N (f₀ + t • h) =
      fun x ↦ apm_m93j05_trunc N f₀ x + t * apm_m93j05_trunc N h x := by
    funext x
    unfold apm_m93j05_trunc
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hmean]
    simp_rw [hccoeff, hscoeff]
    rw [show (∑ j ∈ Finset.Icc 1 N,
        ((apm_m93j05_cosCoeff f₀ j + t * apm_m93j05_cosCoeff h j) *
            Real.cos (j * 2 * Real.pi * x) +
          (apm_m93j05_sinCoeff f₀ j + t * apm_m93j05_sinCoeff h j) *
            Real.sin (j * 2 * Real.pi * x))) =
      (∑ j ∈ Finset.Icc 1 N,
        (apm_m93j05_cosCoeff f₀ j * Real.cos (j * 2 * Real.pi * x) +
          apm_m93j05_sinCoeff f₀ j * Real.sin (j * 2 * Real.pi * x))) +
      t * (∑ j ∈ Finset.Icc 1 N,
        (apm_m93j05_cosCoeff h j * Real.cos (j * 2 * Real.pi * x) +
          apm_m93j05_sinCoeff h j * Real.sin (j * 2 * Real.pi * x))) by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring]
    ring
  let a := fun x ↦ f₀ x - apm_m93j05_trunc N f₀ x
  let b := fun x ↦ h x - apm_m93j05_trunc N h x
  have ha : MemLp a (ENNReal.ofReal p) μ := hf₀.sub (htrunc p f₀)
  have hb : MemLp b (ENNReal.ofReal p) μ := hh.sub (htrunc p h)
  have hab (t : ℝ) :
      (fun x ↦ (f₀ + t • h) x - apm_m93j05_trunc N (f₀ + t • h) x) =
        fun x ↦ a x + t * b x := by
    funext x
    rw [hlinear]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    dsimp [a, b]
    ring
  have hhigh : DifferentiableAt ℝ (fun (t : ℝ) ↦ Real.rpow
      (eLpNorm (fun x ↦ (f₀ + t • h) x - apm_m93j05_trunc N (f₀ + t • h) x)
        (ENNReal.ofReal p) μ).toReal p) 0 := by
    simpa only [μ, hab] using hD1 a b ha hb
  have hA2 := htrunc (2 : ℝ) f₀
  have hB2 := htrunc (2 : ℝ) h
  have hc2 : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  letI : ENNReal.HolderTriple (ENNReal.ofReal (2 : ℝ)) (ENNReal.ofReal (2 : ℝ)) 1 :=
    hc2.ennrealOfReal
  have hAA : Integrable (fun x ↦ apm_m93j05_trunc N f₀ x ^ 2) μ := by
    simpa [pow_two] using hA2.integrable_mul hA2
  have hAB : Integrable (fun x ↦ apm_m93j05_trunc N f₀ x *
      apm_m93j05_trunc N h x) μ := hA2.integrable_mul hB2
  have hBB : Integrable (fun x ↦ apm_m93j05_trunc N h x ^ 2) μ := by
    simpa [pow_two] using hB2.integrable_mul hB2
  have hlow_eq : (fun (t : ℝ) ↦ (eLpNorm (apm_m93j05_trunc N (f₀ + t • h)) 2 μ).toReal ^ 2) =
      fun (t : ℝ) ↦ (∫ x, apm_m93j05_trunc N f₀ x ^ 2 ∂μ) +
        2 * t * (∫ x, apm_m93j05_trunc N f₀ x * apm_m93j05_trunc N h x ∂μ) +
        t ^ 2 * (∫ x, apm_m93j05_trunc N h x ^ 2 ∂μ) := by
    funext t
    rw [hlinear]
    have hm := apm_m93j05_rpow_eLpNorm_eq_integral 2 (by norm_num)
      (fun x ↦ apm_m93j05_trunc N f₀ x + t * apm_m93j05_trunc N h x)
      (hA2.add (hB2.const_smul t))
    simp only [Real.rpow_two] at hm
    norm_num [ENNReal.ofReal_ofNat] at hm ⊢
    rw [hm]
    simp_rw [add_sq, mul_pow]
    rw [show (fun x ↦ apm_m93j05_trunc N f₀ x ^ 2 +
          2 * apm_m93j05_trunc N f₀ x * (t * apm_m93j05_trunc N h x) +
          t ^ 2 * apm_m93j05_trunc N h x ^ 2) =
        fun x ↦ apm_m93j05_trunc N f₀ x ^ 2 + (2*t) *
          (apm_m93j05_trunc N f₀ x * apm_m93j05_trunc N h x) +
          (t^2) * apm_m93j05_trunc N h x ^ 2 by funext x; ring]
    change (∫ x, apm_m93j05_trunc N f₀ x ^ 2 + (2*t) *
        (apm_m93j05_trunc N f₀ x * apm_m93j05_trunc N h x) +
        (t^2) * apm_m93j05_trunc N h x ^ 2 ∂μ) = _
    have hiAB : Integrable (fun x ↦ (2*t) *
        (apm_m93j05_trunc N f₀ x * apm_m93j05_trunc N h x)) μ := by
      simpa [mul_comm] using hAB.const_mul (2*t)
    have hiBB : Integrable (fun x ↦ (t^2) * apm_m93j05_trunc N h x ^ 2) μ := by
      simpa [mul_comm] using hBB.const_mul (t^2)
    calc
      _ = (∫ x, apm_m93j05_trunc N f₀ x ^ 2 + (2*t) *
            (apm_m93j05_trunc N f₀ x * apm_m93j05_trunc N h x) ∂μ) +
          ∫ x, (t^2) * apm_m93j05_trunc N h x ^ 2 ∂μ := by
            simpa only [Pi.add_apply] using
              MeasureTheory.integral_add (hAA.add hiAB) hiBB
      _ = ((∫ x, apm_m93j05_trunc N f₀ x ^ 2 ∂μ) +
            ∫ x, (2*t) * (apm_m93j05_trunc N f₀ x *
              apm_m93j05_trunc N h x) ∂μ) +
          ∫ x, (t^2) * apm_m93j05_trunc N h x ^ 2 ∂μ := by
            rw [MeasureTheory.integral_add hAA hiAB]
      _ = _ := by simp only [MeasureTheory.integral_const_mul]
  have hlow : DifferentiableAt ℝ
      (fun (t : ℝ) ↦ (eLpNorm (apm_m93j05_trunc N (f₀ + t • h)) 2 μ).toReal ^ 2) 0 := by
    rw [hlow_eq]
    fun_prop
  have hc : p.HolderConjugate q := Real.holderConjugate_iff.mpr ⟨hp, by
    simpa [div_eq_mul_inv, add_comm] using hpq⟩
  letI : ENNReal.HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal q) 1 := hc.ennrealOfReal
  have hfg : Integrable (f₀ * g) μ := hf₀.integrable_mul hg
  have hhg : Integrable (h * g) μ := hh.integrable_mul hg
  have hpair_eq : (fun (t : ℝ) ↦ ∫ x, (f₀ + t • h) x * g x ∂μ) =
      fun (t : ℝ) ↦ (∫ x, f₀ x * g x ∂μ) + t * (∫ x, h x * g x ∂μ) := by
    funext t
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul]
    calc
      (∫ x, f₀ x * g x + t * h x * g x ∂μ) =
          ∫ x, (f₀ * g) x + (t • (h * g)) x ∂μ := by congr 1; funext x; simp; ring
      _ = (∫ x, (f₀ * g) x ∂μ) + ∫ x, (t • (h * g)) x ∂μ :=
        MeasureTheory.integral_add hfg (hhg.const_mul t)
      _ = _ := by simp [MeasureTheory.integral_const_mul]
  have hpair : DifferentiableAt ℝ (fun (t : ℝ) ↦ ∫ x, (f₀ + t • h) x * g x ∂μ) 0 := by
    exact hpair_eq.symm ▸ (by fun_prop)
  change DifferentiableAt ℝ (fun (t : ℝ) ↦
    Real.rpow (eLpNorm (fun x ↦ (f₀ + t • h) x - apm_m93j05_trunc N (f₀ + t • h) x)
      (ENNReal.ofReal p) μ).toReal p +
    (eLpNorm (apm_m93j05_trunc N (f₀ + t • h)) 2 μ).toReal ^ 2 +
    ∫ x, (f₀ + t • h) x * g x ∂μ) 0
  exact (hhigh.add hlow).add hpair

theorem apm_m93j05_stationary_at_minimizer
    (N : ℕ) (p q : ℝ) (hp : 1 < p) (hq : 1 < q)
    (hpq : 1 / p + 1 / q = 1) :
    let μ := volume.restrict (Set.Icc (0 : ℝ) 1)
    ∀ g, MemLp g (ENNReal.ofReal q) μ →
      ∀ f₀, MemLp f₀ (ENNReal.ofReal p) μ →
        (∀ f, MemLp f (ENNReal.ofReal p) μ →
          apm_m93j05_J N p g f₀ ≤ apm_m93j05_J N p g f) →
        ∀ h, MemLp h (ENNReal.ofReal p) μ →
          HasDerivAt
            (fun t : ℝ => apm_m93j05_J N p g (f₀ + t • h)) 0 0 := by
  intro μ g hg f₀ hf₀ hmin h hh
  have hd := apm_m93j05_J_path_differentiableAt N p q hp hq hpq
    (apm_m93j05_lp_rpow_differentiableAt p hp) g f₀ h hg hf₀ hh
  have hloc : IsLocalMin (fun t : ℝ ↦ apm_m93j05_J N p g (f₀ + t • h)) 0 := by
    refine Filter.Eventually.of_forall (fun t ↦ ?_)
    simpa using hmin (f₀ + t • h)
      (apm_m93j05_stationary_at_minimizer_aux_memLp_path p t f₀ h hf₀ hh)
  have h0 := hloc.hasDerivAt_eq_zero hd.hasDerivAt
  simpa [h0] using hd.hasDerivAt

theorem apm_m93j05 :
    ∀ (N : ℕ) (p q : ℝ), 1 < p → 1 < q → 1 / p + 1 / q = 1 →
    let μ := volume.restrict (Set.Icc (0 : ℝ) 1)
    let Φ := apm_m93j05_trunc N
    (∀ f g, MemLp f (ENNReal.ofReal p) μ → MemLp g (ENNReal.ofReal q) μ →
      ∫ x, Φ f x * g x ∂μ = ∫ x, f x * Φ g x ∂μ) ∧
    (∀ f, Φ f = 0 ↔
      (∫ x in Set.Icc (0 : ℝ) 1, f x = 0 ∧
       ∀ j ∈ Finset.Icc 1 N,
         apm_m93j05_cosCoeff f j = 0 ∧ apm_m93j05_sinCoeff f j = 0)) ∧
    (∀ f, ∃ u v, f = u + v ∧ Φ u = u ∧ Φ v = 0) ∧
    (∀ g, MemLp g (ENNReal.ofReal q) μ →
      (∀ (f : ℝ → ℝ) (s : ℕ → ℝ → ℝ),
        MemLp f (ENNReal.ofReal p) μ →
        (∀ n, MemLp (s n) (ENNReal.ofReal p) μ) →
        (∀ h, MemLp h (ENNReal.ofReal q) μ →
          Tendsto (fun n => ∫ x, s n x * h x ∂μ) atTop
            (nhds (∫ x, f x * h x ∂μ))) →
        ∀ r, (∃ᶠ n in atTop, apm_m93j05_J N p g (s n) ≤ r) →
          apm_m93j05_J N p g f ≤ r) ∧
      (∃ f₀, MemLp f₀ (ENNReal.ofReal p) μ ∧
        ∀ f, MemLp f (ENNReal.ofReal p) μ →
          apm_m93j05_J N p g f₀ ≤ apm_m93j05_J N p g f) ∧
      (∀ f₀, MemLp f₀ (ENNReal.ofReal p) μ →
        (∀ f, MemLp f (ENNReal.ofReal p) μ →
          apm_m93j05_J N p g f₀ ≤ apm_m93j05_J N p g f) →
        ∀ h, MemLp h (ENNReal.ofReal p) μ →
          HasDerivAt
            (fun t : ℝ => apm_m93j05_J N p g (f₀ + t • h)) 0 0)) := by
  intro N p q hp hq hpq
  dsimp only
  obtain ⟨hadj, hker, hsplit⟩ :=
    apm_m93j05_fourier_projection N p q hp hq hpq
  refine ⟨hadj, hker, hsplit, ?_⟩
  intro g hg
  exact ⟨apm_m93j05_weak_lowerSemicontinuous N p q hp hq hpq g hg,
    apm_m93j05_exists_minimizer N p q hp hq hpq g hg,
    apm_m93j05_stationary_at_minimizer N p q hp hq hpq g hg⟩

#print axioms apm_m93j05
