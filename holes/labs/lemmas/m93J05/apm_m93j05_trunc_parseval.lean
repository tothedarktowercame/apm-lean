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

/-- Parseval for the truncation: `∫₀¹ (m + Σ aⱼ cos + bⱼ sin)² = m² + Σ (aⱼ² + bⱼ²)/2`
(from `apm_m93j05_trig_orthogonality` and the mean-zero helpers). -/
-- BEGIN SEAT AREA
theorem apm_m93j05_trunc_parseval (N : ℕ) (f : ℝ → ℝ) :
    (eLpNorm (apm_m93j05_trunc N f) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2 =
      (∫ x in Set.Icc (0 : ℝ) 1, f x) ^ 2 +
        ∑ j ∈ Finset.Icc 1 N, (apm_m93j05_cosCoeff f j ^ 2 + apm_m93j05_sinCoeff f j ^ 2) / 2 := by
  sorry
-- END SEAT AREA

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
  sorry

lemma apm_m93j05_lp_rpow_weak_lsc_aux_limit
    {p r A : ℝ} (hp : 1 < p) (hA : 0 ≤ A)
    {B z : ℕ → ℝ} (hB : ∀ n, 0 ≤ B n)
    (hz : Tendsto z atTop (nhds (Real.rpow A p)))
    (hzB : ∀ n, z n ≤ B n * Real.rpow A (p - 1))
    (hfreq : ∃ᶠ n in atTop, Real.rpow (B n) p ≤ r) :
    Real.rpow A p ≤ r := by
  sorry

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
  sorry

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

theorem apm_m93j05_exists_minimizer
    (N : ℕ) (p q : ℝ) (hp : 1 < p) (hq : 1 < q)
    (hpq : 1 / p + 1 / q = 1) :
    let μ := volume.restrict (Set.Icc (0 : ℝ) 1)
    ∀ g, MemLp g (ENNReal.ofReal q) μ →
      ∃ f₀, MemLp f₀ (ENNReal.ofReal p) μ ∧
        ∀ f, MemLp f (ENNReal.ofReal p) μ →
          apm_m93j05_J N p g f₀ ≤ apm_m93j05_J N p g f := by
  sorry

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
  sorry

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
    (hD1 : ∀ (a b : ℝ → ℝ), MemLp a (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)) → MemLp b (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)) →
      DifferentiableAt ℝ (fun t : ℝ ↦ Real.rpow
        (eLpNorm (fun x ↦ a x + t * b x) (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal p) 0)
    (g f₀ h : ℝ → ℝ) (hg : MemLp g (ENNReal.ofReal q) (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hf₀ : MemLp f₀ (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1))) (hh : MemLp h (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    DifferentiableAt ℝ (fun t : ℝ ↦ apm_m93j05_J N p g (f₀ + t • h)) 0 := by
  sorry

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
  have hd := apm_m93j05_J_path_differentiableAt N p q hp hq
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
