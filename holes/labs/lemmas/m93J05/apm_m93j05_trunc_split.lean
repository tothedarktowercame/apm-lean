import Mathlib

open MeasureTheory Filter

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
theorem apm_m93j05_trig_orthogonality (j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) :
    (∫ x in Set.Icc (0 : ℝ) 1, Real.cos (j * 2 * Real.pi * x) * Real.cos (k * 2 * Real.pi * x))
        = (if j = k then 1 / 2 else 0) ∧
    (∫ x in Set.Icc (0 : ℝ) 1, Real.sin (j * 2 * Real.pi * x) * Real.sin (k * 2 * Real.pi * x))
        = (if j = k then 1 / 2 else 0) ∧
    (∫ x in Set.Icc (0 : ℝ) 1, Real.cos (j * 2 * Real.pi * x) * Real.sin (k * 2 * Real.pi * x))
        = 0 := by
  sorry

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
  sorry

/-- (S) Self-adjointness: both sides equal `m_f m_g + Σ (a_j(f) a_j(g) + b_j(f) b_j(g)) / 2`. -/
theorem apm_m93j05_trunc_selfAdjoint (N : ℕ) (p q : ℝ) (hp : 1 < p) (hq : 1 < q)
    (f g : ℝ → ℝ) (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hg : MemLp g (ENNReal.ofReal q) (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    ∫ x, apm_m93j05_trunc N f x * g x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) =
      ∫ x, f x * apm_m93j05_trunc N g x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  sorry

/-- (K) Kernel: `Φ f = 0` iff the mean and the coefficients up to `N` vanish. -/
theorem apm_m93j05_trunc_kernel (N : ℕ)
    (hC : ∀ f : ℝ → ℝ,
      (∫ x in Set.Icc (0 : ℝ) 1, apm_m93j05_trunc N f x) = ∫ x in Set.Icc (0 : ℝ) 1, f x ∧
      ∀ k ∈ Finset.Icc 1 N, apm_m93j05_cosCoeff (apm_m93j05_trunc N f) k = apm_m93j05_cosCoeff f k ∧ apm_m93j05_sinCoeff (apm_m93j05_trunc N f) k = apm_m93j05_sinCoeff f k)
    (f : ℝ → ℝ) :
    apm_m93j05_trunc N f = 0 ↔
      (∫ x in Set.Icc (0 : ℝ) 1, f x = 0 ∧
       ∀ j ∈ Finset.Icc 1 N, apm_m93j05_cosCoeff f j = 0 ∧ apm_m93j05_sinCoeff f j = 0) := by
  sorry

/-- (Sp) Splitting `f = Φ f + (f − Φ f)`. For `Φ (f − Φ f) = 0`: if `f · cos_k` is integrable the
coefficients subtract; if not, neither is `(f − Φ f) · cos_k`, and both coefficients are `0`. -/
-- BEGIN SEAT AREA
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
-- END SEAT AREA

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
        ∀ r, (∀ᶠ n in atTop, r ≤ apm_m93j05_J N p g (s n)) →
          r ≤ apm_m93j05_J N p g f := by
  sorry

theorem apm_m93j05_exists_minimizer
    (N : ℕ) (p q : ℝ) (hp : 1 < p) (hq : 1 < q)
    (hpq : 1 / p + 1 / q = 1) :
    let μ := volume.restrict (Set.Icc (0 : ℝ) 1)
    ∀ g, MemLp g (ENNReal.ofReal q) μ →
      ∃ f₀, MemLp f₀ (ENNReal.ofReal p) μ ∧
        ∀ f, MemLp f (ENNReal.ofReal p) μ →
          apm_m93j05_J N p g f₀ ≤ apm_m93j05_J N p g f := by
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
  sorry

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
        ∀ r, (∀ᶠ n in atTop, r ≤ apm_m93j05_J N p g (s n)) →
          r ≤ apm_m93j05_J N p g f) ∧
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
