import Mathlib

/-! # APM m03J03: examples and derivatives of distributions

## Statement repairs

None.  Mathlib's distribution convention uses real-valued test functions and
allows complex-valued distributions, which faithfully accommodates every part.
-/

open MeasureTheory Set TopologicalSpace
open scoped Distributions ContDiff BoundedContinuousFunction

noncomputable section

/-- The Heaviside function with the irrelevant value at zero chosen to be zero. -/
def m03J03Heaviside (x : ℝ) : ℝ := if 0 < x then 1 else 0

/-- Multiplication by the chosen Heaviside representative is exactly
restriction of the integral to the positive half-line. -/
lemma m03J03_integral_heaviside_mul (g : ℝ → ℝ) :
    (∫ x : ℝ, m03J03Heaviside x * g x) = ∫ x in Ioi (0 : ℝ), g x := by
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : 0 < x <;> simp [m03J03Heaviside, hx]

/-- The first half-line integration-by-parts identity for `H * sin`. The
compact-support endpoint theorem removes both the value at infinity and the
zero endpoint, since `sin 0 = 0`. -/
lemma m03J03_heaviside_sin_integral_deriv
    (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) :
    -(∫ x : ℝ, m03J03Heaviside x * Real.sin x * deriv φ x) =
      ∫ x : ℝ, m03J03Heaviside x * Real.cos x * φ x := by
  let g : ℝ → ℝ := fun x ↦ Real.sin x * φ x
  have hg : ContDiff ℝ 1 g :=
    Real.contDiff_sin.mul (φ.contDiff.of_le (by simp))
  have hgc : HasCompactSupport g := φ.hasCompactSupport.mul_left
  have hderiv (x : ℝ) : deriv g x =
      Real.cos x * φ x + Real.sin x * deriv φ x := by
    have hs := Real.hasDerivAt_sin x
    have hφ := φ.contDiff.differentiable (by simp) x
    simpa [g] using (hs.mul hφ.hasDerivAt).deriv
  have hint := hgc.integral_Ioi_deriv_eq hg 0
  simp_rw [hderiv] at hint
  have hcos : IntegrableOn (fun x : ℝ ↦ Real.cos x * φ x) (Ioi 0) :=
    (Real.continuous_cos.mul φ.contDiff.continuous).integrable_of_hasCompactSupport
      φ.hasCompactSupport.mul_left |>.integrableOn
  have hsin : IntegrableOn (fun x : ℝ ↦ Real.sin x * deriv φ x) (Ioi 0) :=
    (Real.continuous_sin.mul
      (φ.contDiff.continuous_deriv (by simp))).integrable_of_hasCompactSupport
        φ.hasCompactSupport.deriv.mul_left |>.integrableOn
  rw [integral_add hcos hsin] at hint
  rw [show (∫ x : ℝ, m03J03Heaviside x * Real.sin x * deriv φ x) =
      ∫ x in Ioi (0 : ℝ), Real.sin x * deriv φ x by
        simpa [mul_assoc] using
          m03J03_integral_heaviside_mul (fun x ↦ Real.sin x * deriv φ x),
    show (∫ x : ℝ, m03J03Heaviside x * Real.cos x * φ x) =
      ∫ x in Ioi (0 : ℝ), Real.cos x * φ x by
        simpa [mul_assoc] using
          m03J03_integral_heaviside_mul (fun x ↦ Real.cos x * φ x)]
  have hg0 : g 0 = 0 := by simp [g]
  rw [hg0, neg_zero] at hint
  linarith

/-- The ordinary derivative of a real test function, bundled again as a test
function.  This lets distributional integration-by-parts lemmas be iterated
without reopening compact-support and smoothness obligations. -/
noncomputable def m03J03_derivTestFunction
    (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) :
    TestFunction (⊤ : Opens ℝ) ℝ ⊤ :=
  TestFunction.postcompCLM (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ))
    (TestFunction.fderivCLM ℝ (⊤ : ℕ∞) (⊤ : ℕ∞) φ)

@[simp] lemma m03J03_derivTestFunction_apply
    (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) (x : ℝ) :
    m03J03_derivTestFunction φ x = deriv φ x := by
  change (fderiv ℝ (φ : ℝ → ℝ) x) 1 = deriv φ x
  rw [fderiv_apply_one_eq_deriv]

/-- The second half-line integration-by-parts identity.  The boundary term is
`φ 0`, since differentiating `sin` once produces `cos 0 = 1`. -/
lemma m03J03_heaviside_sin_integral_iteratedDeriv_two
    (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) :
    (∫ x : ℝ, m03J03Heaviside x * Real.sin x * iteratedDeriv 2 φ x) =
      φ 0 - ∫ x : ℝ, m03J03Heaviside x * Real.sin x * φ x := by
  let dφ := m03J03_derivTestFunction φ
  have hfirst := m03J03_heaviside_sin_integral_deriv dφ
  dsimp [dφ] at hfirst
  have hd : (m03J03_derivTestFunction φ : ℝ → ℝ) = fun x ↦ deriv φ x := by
    funext x
    exact m03J03_derivTestFunction_apply φ x
  rw [hd] at hfirst
  have hiter (x : ℝ) : iteratedDeriv 2 φ x = deriv (fun y ↦ deriv φ y) x := by
    simp [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ]
  simp_rw [hiter]
  let g : ℝ → ℝ := fun x ↦ Real.cos x * φ x
  have hg : ContDiff ℝ 1 g :=
    Real.contDiff_cos.mul (φ.contDiff.of_le (by simp))
  have hgc : HasCompactSupport g := φ.hasCompactSupport.mul_left
  have hderiv (x : ℝ) : deriv g x =
      -Real.sin x * φ x + Real.cos x * deriv φ x := by
    have hc := Real.hasDerivAt_cos x
    have hφ := φ.contDiff.differentiable (by simp) x
    simpa [g] using (hc.mul hφ.hasDerivAt).deriv
  have hint := hgc.integral_Ioi_deriv_eq hg 0
  simp_rw [hderiv] at hint
  have hsin : IntegrableOn (fun x : ℝ ↦ -Real.sin x * φ x) (Ioi 0) :=
    (Real.continuous_sin.neg.mul φ.contDiff.continuous).integrable_of_hasCompactSupport
      φ.hasCompactSupport.mul_left |>.integrableOn
  have hcos : IntegrableOn (fun x : ℝ ↦ Real.cos x * deriv φ x) (Ioi 0) :=
    (Real.continuous_cos.mul
      (φ.contDiff.continuous_deriv (by simp))).integrable_of_hasCompactSupport
        φ.hasCompactSupport.deriv.mul_left |>.integrableOn
  rw [integral_add hsin hcos] at hint
  have hsin_restrict :
      (∫ x : ℝ, m03J03Heaviside x * Real.sin x * φ x) =
        ∫ x in Ioi (0 : ℝ), Real.sin x * φ x := by
    simpa [mul_assoc] using
      m03J03_integral_heaviside_mul (fun x ↦ Real.sin x * φ x)
  have hcos_restrict :
      (∫ x : ℝ, m03J03Heaviside x * Real.cos x * deriv φ x) =
        ∫ x in Ioi (0 : ℝ), Real.cos x * deriv φ x := by
    simpa [mul_assoc] using
      m03J03_integral_heaviside_mul (fun x ↦ Real.cos x * deriv φ x)
  rw [hcos_restrict] at hfirst
  simp_rw [neg_mul] at hint
  rw [integral_neg] at hint
  simp [g] at hint
  rw [hsin_restrict]
  linarith

/-- Evaluation at zero as a distribution.  Continuity follows by factoring
through the continuous inclusion of test functions into bounded continuous
functions. -/
noncomputable def m03J03_deltaZero :
    Distribution (⊤ : Opens ℝ) ℝ ⊤ :=
  (BoundedContinuousFunction.evalCLM ℝ (0 : ℝ)).comp
    (TestFunction.toBoundedContinuousFunctionCLM ℝ)

@[simp] lemma m03J03_deltaZero_apply
    (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) :
    m03J03_deltaZero φ = φ 0 := rfl

/-- On each fixed compact support, integration of a bounded continuous weight
over the positive half-line is a continuous linear functional. -/
noncomputable def m03J03_boundedWeightIntegralSupportedIn
    (w : ℝ →ᵇ ℝ) (K : Compacts ℝ) :
    ContDiffMapSupportedIn ℝ ℝ ⊤ K →L[ℝ] ℝ := by
  let L : (ℝ →ᵇ ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f ↦ ∫ x in (K : Set ℝ) ∩ Ioi 0, w x * f x
      map_add' := fun f g ↦ by
        have hf : IntegrableOn (fun x ↦ w x * f x) ((K : Set ℝ) ∩ Ioi 0) :=
          ((w.continuous.mul f.continuous).continuousOn.integrableOn_compact
            K.isCompact).mono_set inter_subset_left
        have hg : IntegrableOn (fun x ↦ w x * g x) ((K : Set ℝ) ∩ Ioi 0) :=
          ((w.continuous.mul g.continuous).continuousOn.integrableOn_compact
            K.isCompact).mono_set inter_subset_left
        simpa [mul_add] using integral_add hf hg
      map_smul' := fun c f ↦ by
        rw [← integral_smul]
        apply integral_congr_ae
        filter_upwards with x
        simp [mul_left_comm] }
  let Lc : (ℝ →ᵇ ℝ) →L[ℝ] ℝ :=
    L.mkContinuous (‖w‖ * volume.real ((K : Set ℝ) ∩ Ioi 0)) (fun f ↦ by
      change ‖∫ x in (K : Set ℝ) ∩ Ioi 0, w x * f x‖ ≤ _
      refine (norm_setIntegral_le_of_norm_le_const (C := ‖w‖ * ‖f‖)
        ((measure_mono inter_subset_left).trans_lt K.isCompact.measure_lt_top) ?_).trans_eq ?_
      · intro x hx
        calc
          ‖w x * f x‖ = ‖w x‖ * ‖f x‖ := norm_mul _ _
          _ ≤ ‖w‖ * ‖f‖ := mul_le_mul (w.norm_coe_le_norm x)
            (f.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _)
      · ring)
  exact Lc.comp (ContDiffMapSupportedIn.toBoundedContinuousFunctionCLM ℝ)

/-- The corresponding global test-function functional, obtained from the LF
universal property. -/
noncomputable def m03J03_boundedWeightIntegralDistribution
    (w : ℝ →ᵇ ℝ) : Distribution (⊤ : Opens ℝ) ℝ ⊤ :=
  TestFunction.limitCLM ℝ
    (fun φ ↦ ∫ x in Ioi (0 : ℝ), w x * φ x)
    (fun K _ ↦ m03J03_boundedWeightIntegralSupportedIn w K)
    (fun K _ f ↦ by
      change (∫ x in Ioi (0 : ℝ), w x * f x) =
        ∫ x in (K : Set ℝ) ∩ Ioi 0, w x * f x
      apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
        inter_subset_right
      intro x hx
      have hxK : x ∉ (K : Set ℝ) := fun hxK ↦ hx.2 ⟨hxK, hx.1⟩
      rw [f.zero_on_compl hxK]
      simp)

@[simp] lemma m03J03_boundedWeightIntegralDistribution_apply
    (w : ℝ →ᵇ ℝ) (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) :
    m03J03_boundedWeightIntegralDistribution w φ =
      ∫ x in Ioi (0 : ℝ), w x * φ x := rfl

noncomputable def m03J03_sinWeight : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup Real.sin Real.continuous_sin 1
    (fun x ↦ by simpa [Real.norm_eq_abs] using Real.abs_sin_le_one x)

noncomputable def m03J03_cosWeight : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup Real.cos Real.continuous_cos 1
    (fun x ↦ by simpa [Real.norm_eq_abs] using Real.abs_cos_le_one x)

noncomputable def m03J03_compactRadius (K : Compacts ℝ) : ℝ :=
  Classical.choose (K.isCompact.isBounded.subset_closedBall (0 : ℝ))

lemma m03J03_compact_subset_closedBall (K : Compacts ℝ) :
    (K : Set ℝ) ⊆ Metric.closedBall 0 (m03J03_compactRadius K) :=
  Classical.choose_spec (K.isCompact.isBounded.subset_closedBall (0 : ℝ))

noncomputable def m03J03_compactCutoff (K : Compacts ℝ) : ℕ :=
  Classical.choose (exists_nat_gt (m03J03_compactRadius K))

lemma m03J03_compactRadius_lt_cutoff (K : Compacts ℝ) :
    m03J03_compactRadius K < (m03J03_compactCutoff K : ℝ) :=
  Classical.choose_spec (exists_nat_gt (m03J03_compactRadius K))

lemma m03J03_nat_not_mem_compact_of_cutoff_le (K : Compacts ℝ) (n : ℕ)
    (hn : m03J03_compactCutoff K ≤ n) : (n : ℝ) ∉ (K : Set ℝ) := by
  intro hnK
  have hball := m03J03_compact_subset_closedBall K hnK
  have hdist : dist (n : ℝ) 0 ≤ m03J03_compactRadius K :=
    Metric.mem_closedBall.mp hball
  rw [Real.dist_0_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)] at hdist
  exact (not_le_of_gt (m03J03_compactRadius_lt_cutoff K))
    ((Nat.cast_le.mpr hn).trans hdist)

/-- The finite Dirac sum seen by test functions supported in `K`. -/
noncomputable def m03J03_diracCombSupportedIn (K : Compacts ℝ) :
    ContDiffMapSupportedIn ℝ ℝ ⊤ K →L[ℝ] ℂ :=
  ∑ n ∈ Finset.range (m03J03_compactCutoff K),
    Complex.ofRealCLM.comp
      ((BoundedContinuousFunction.evalCLM ℝ (n : ℝ)).comp
        (ContDiffMapSupportedIn.toBoundedContinuousFunctionCLM ℝ))

/-- The locally finite one-sided Dirac comb as an LF-continuous functional. -/
noncomputable def m03J03_diracComb :
    Distribution (⊤ : Opens ℝ) ℂ ⊤ :=
  TestFunction.limitCLM ℝ
    (fun φ ↦ ∑' n : ℕ, (φ n : ℂ))
    (fun K _ ↦ m03J03_diracCombSupportedIn K)
    (fun K _ f ↦ by
      change (∑' n : ℕ, (f (n : ℝ) : ℂ)) = m03J03_diracCombSupportedIn K f
      rw [tsum_eq_sum (s := Finset.range (m03J03_compactCutoff K))]
      · simp [m03J03_diracCombSupportedIn]
      · intro n hn
        have hn' : m03J03_compactCutoff K ≤ n := by
          simpa [Finset.mem_range, not_lt] using hn
        have hnot := m03J03_nat_not_mem_compact_of_cutoff_le K n hn'
        rw [f.zero_on_compl hnot]
        simp)

@[simp] lemma m03J03_diracComb_apply
    (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) :
    m03J03_diracComb φ = ∑' n : ℕ, (φ n : ℂ) := rfl

/-- Derivative formula for the Fourier kernel times a test function.  This is
the local algebraic step iterated by the polynomial-decay argument. -/
lemma m03J03_hasDerivAt_fourier_mul
    (n : ℕ) (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ ↦
        Complex.exp ((n : ℂ) * Complex.I * (y : ℂ)) * φ y)
      (Complex.exp ((n : ℂ) * Complex.I * (x : ℂ)) *
        (((n : ℂ) * Complex.I) * φ x +
          ((deriv (φ : ℝ → ℝ) x : ℝ) : ℂ))) x := by
  let c : ℂ := (n : ℂ) * Complex.I
  have hlin : HasDerivAt (fun y : ℝ ↦ c * (y : ℂ)) c x := by
    simpa using (((hasDerivAt_id (x : ℂ)).const_mul c).comp_ofReal)
  have hexp : HasDerivAt
      (fun y : ℝ ↦ Complex.exp (c * (y : ℂ)))
      (Complex.exp (c * (x : ℂ)) * c) x := hlin.cexp
  have hφ : HasDerivAt (fun y : ℝ ↦ (φ y : ℂ))
      ((deriv (φ : ℝ → ℝ) x : ℝ) : ℂ) x :=
    (φ.contDiff.differentiable (by simp) x).hasDerivAt.ofReal_comp
  simpa [c, mul_add, mul_assoc] using hexp.mul hφ

/-- The integral of the derivative of a compactly supported `C¹` complex
function vanishes. -/
lemma m03J03_integral_deriv_eq_zero {g : ℝ → ℂ}
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) :
    (∫ x : ℝ, deriv g x) = 0 := by
  have hint : Integrable (fun x ↦ deriv g x) :=
    (hg.continuous_deriv le_rfl).integrable_of_hasCompactSupport hgc.deriv
  rw [← integral_add_compl measurableSet_Iic hint, compl_Iic]
  rw [hgc.integral_Iic_deriv_eq hg 0, hgc.integral_Ioi_deriv_eq hg 0]
  simp

noncomputable def m03J03_fourierPairing
    (n : ℕ) (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) : ℂ :=
  ∫ x : ℝ, Complex.exp ((n : ℂ) * Complex.I * (x : ℂ)) * φ x

lemma m03J03_contDiff_fourier_mul
    (n : ℕ) (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) :
    ContDiff ℝ 1 (fun x : ℝ ↦
      Complex.exp ((n : ℂ) * Complex.I * (x : ℂ)) * φ x) := by
  rw [contDiff_one_iff_deriv]
  constructor
  · intro x
    exact (m03J03_hasDerivAt_fourier_mul n φ x).differentiableAt
  · have hd : deriv (fun x : ℝ ↦
        Complex.exp ((n : ℂ) * Complex.I * (x : ℂ)) * φ x) =
        fun x : ℝ ↦ Complex.exp ((n : ℂ) * Complex.I * (x : ℂ)) *
          (((n : ℂ) * Complex.I) * φ x +
            ((deriv (φ : ℝ → ℝ) x : ℝ) : ℂ)) := by
      funext x
      exact (m03J03_hasDerivAt_fourier_mul n φ x).deriv
    rw [hd]
    have hx : Continuous (fun x : ℝ ↦ (x : ℂ)) := Complex.continuous_ofReal
    have he : Continuous (fun x : ℝ ↦
        Complex.exp ((n : ℂ) * Complex.I * (x : ℂ))) :=
      (continuous_const.mul hx).cexp
    have hφ : Continuous (fun x : ℝ ↦ (φ x : ℂ)) :=
      Complex.continuous_ofReal.comp φ.contDiff.continuous
    have hdφ : Continuous (fun x : ℝ ↦
        ((deriv (φ : ℝ → ℝ) x : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (φ.contDiff.continuous_deriv (by simp))
    exact he.mul ((continuous_const.mul hφ).add hdφ)

set_option maxHeartbeats 800000 in
lemma m03J03_hasCompactSupport_fourier_mul
    (n : ℕ) (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) :
    HasCompactSupport (fun x : ℝ ↦
      Complex.exp ((n : ℂ) * Complex.I * (x : ℂ)) * φ x) := by
  have hφ : HasCompactSupport (fun x : ℝ ↦ (φ x : ℂ)) :=
    show HasCompactSupport ((fun y : ℝ ↦ (y : ℂ)) ∘ (φ : ℝ → ℝ)) from
      φ.hasCompactSupport.comp_left (by simp)
  exact hφ.mul_left

/-- One integration by parts for the Fourier pairing. -/
lemma m03J03_fourierPairing_mul_freq
    (n : ℕ) (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) :
    ((n : ℂ) * Complex.I) * m03J03_fourierPairing n φ =
      -m03J03_fourierPairing n (m03J03_derivTestFunction φ) := by
  let g : ℝ → ℂ := fun x ↦
    Complex.exp ((n : ℂ) * Complex.I * (x : ℂ)) * φ x
  have hz := m03J03_integral_deriv_eq_zero
    (m03J03_contDiff_fourier_mul n φ)
    (m03J03_hasCompactSupport_fourier_mul n φ)
  have hd : deriv g = fun x : ℝ ↦
      ((n : ℂ) * Complex.I) *
          (Complex.exp ((n : ℂ) * Complex.I * (x : ℂ)) * φ x) +
        Complex.exp ((n : ℂ) * Complex.I * (x : ℂ)) *
          ((deriv (φ : ℝ → ℝ) x : ℝ) : ℂ) := by
    funext x
    rw [(m03J03_hasDerivAt_fourier_mul n φ x).deriv]
    ring
  change (∫ x, deriv g x) = 0 at hz
  rw [hd] at hz
  have h₁ : Integrable (fun x : ℝ ↦
      ((n : ℂ) * Complex.I) *
        (Complex.exp ((n : ℂ) * Complex.I * (x : ℂ)) * φ x)) :=
    ((m03J03_contDiff_fourier_mul n φ).continuous.integrable_of_hasCompactSupport
      (m03J03_hasCompactSupport_fourier_mul n φ)).const_mul _
  have h₂ : Integrable (fun x : ℝ ↦
      Complex.exp ((n : ℂ) * Complex.I * (x : ℂ)) *
        ((deriv (φ : ℝ → ℝ) x : ℝ) : ℂ)) := by
    have hc := m03J03_contDiff_fourier_mul n (m03J03_derivTestFunction φ)
    have hs := m03J03_hasCompactSupport_fourier_mul n (m03J03_derivTestFunction φ)
    simpa [m03J03_derivTestFunction_apply] using
      hc.continuous.integrable_of_hasCompactSupport hs
  rw [integral_add h₁ h₂] at hz
  have hc : (∫ x : ℝ, ((n : ℂ) * Complex.I) *
      (Complex.exp ((n : ℂ) * Complex.I * (x : ℂ)) * φ x)) =
      ((n : ℂ) * Complex.I) *
        ∫ x : ℝ, Complex.exp ((n : ℂ) * Complex.I * (x : ℂ)) * φ x :=
    integral_const_mul ((n : ℂ) * Complex.I) _
  rw [hc] at hz
  change ((n : ℂ) * Complex.I) * m03J03_fourierPairing n φ +
    m03J03_fourierPairing n (m03J03_derivTestFunction φ) = 0 at hz
  exact eq_neg_of_add_eq_zero_left hz

noncomputable def m03J03_iterDerivTestFunction : ℕ →
    TestFunction (⊤ : Opens ℝ) ℝ ⊤ → TestFunction (⊤ : Opens ℝ) ℝ ⊤
  | 0, φ => φ
  | k + 1, φ => m03J03_iterDerivTestFunction k (m03J03_derivTestFunction φ)

@[simp] lemma m03J03_iterDerivTestFunction_apply (k : ℕ)
    (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) (x : ℝ) :
    m03J03_iterDerivTestFunction k φ x = iteratedDeriv k φ x := by
  induction k generalizing φ with
  | zero => rfl
  | succ k ih =>
      rw [m03J03_iterDerivTestFunction, ih,
        show iteratedDeriv (k + 1) (φ : ℝ → ℝ) x =
          iteratedDeriv k (fun y ↦ deriv (φ : ℝ → ℝ) y) x by
            rw [iteratedDeriv_succ']]
      have hd : (m03J03_derivTestFunction φ : ℝ → ℝ) =
          fun y ↦ deriv (φ : ℝ → ℝ) y := by
        funext y
        exact m03J03_derivTestFunction_apply φ y
      rw [hd]

/-- Iterated integration by parts, in a denominator-free form that also
remains valid at frequency zero. -/
lemma m03J03_fourierPairing_mul_freq_pow
    (n k : ℕ) (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) :
    (((n : ℂ) * Complex.I) ^ k) * m03J03_fourierPairing n φ =
      ((-1 : ℂ) ^ k) *
        m03J03_fourierPairing n (m03J03_iterDerivTestFunction k φ) := by
  induction k generalizing φ with
  | zero => simp [m03J03_iterDerivTestFunction]
  | succ k ih =>
      rw [pow_succ, pow_succ, mul_assoc,
        m03J03_fourierPairing_mul_freq n φ]
      rw [mul_neg, ih]
      simp [m03J03_iterDerivTestFunction]

/-- Quantitative denominator-free Fourier decay. -/
lemma m03J03_pow_mul_norm_fourierPairing_le
    (n k : ℕ) (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) :
    (n : ℝ) ^ k * ‖m03J03_fourierPairing n φ‖ ≤
      ∫ x : ℝ, ‖iteratedDeriv k φ x‖ := by
  have hnorm := congrArg norm (m03J03_fourierPairing_mul_freq_pow n k φ)
  have hleft :
      ‖(((n : ℂ) * Complex.I) ^ k) * m03J03_fourierPairing n φ‖ =
        (n : ℝ) ^ k * ‖m03J03_fourierPairing n φ‖ := by
    simp [norm_pow]
  have hright :
      ‖((-1 : ℂ) ^ k) *
          m03J03_fourierPairing n (m03J03_iterDerivTestFunction k φ)‖ =
        ‖m03J03_fourierPairing n (m03J03_iterDerivTestFunction k φ)‖ := by
    simp [norm_pow]
  rw [hleft, hright] at hnorm
  rw [hnorm]
  unfold m03J03_fourierPairing
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply integral_congr_ae
  filter_upwards with x
  rw [norm_mul, Complex.norm_exp]
  simp [m03J03_iterDerivTestFunction_apply]

lemma m03J03_norm_fourier_term_le_inv_sq
    (a : ℕ → ℂ) (A : ℝ) (N n : ℕ) (hA : 0 ≤ A)
    (ha : ∀ m : ℕ, ‖a m‖ ≤ A * (m : ℝ) ^ N) (hn : 0 < n)
    (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) :
    ‖a n * m03J03_fourierPairing n φ‖ ≤
      (A * (∫ x : ℝ, ‖iteratedDeriv (N + 2) φ x‖)) /
        (n : ℝ) ^ 2 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn2 : 0 < (n : ℝ) ^ 2 := pow_pos hnR _
  apply (le_div_iff₀ hn2).2
  rw [norm_mul]
  calc
    ‖a n‖ * ‖m03J03_fourierPairing n φ‖ * (n : ℝ) ^ 2 ≤
        (A * (n : ℝ) ^ N) * ‖m03J03_fourierPairing n φ‖ * (n : ℝ) ^ 2 := by
      gcongr
      exact ha n
    _ = A * ((n : ℝ) ^ (N + 2) * ‖m03J03_fourierPairing n φ‖) := by
      rw [pow_add]
      ring
    _ ≤ A * (∫ x : ℝ, ‖iteratedDeriv (N + 2) φ x‖) :=
      mul_le_mul_of_nonneg_left
        (m03J03_pow_mul_norm_fourierPairing_le n (N + 2) φ) hA
    _ = (A * (∫ x : ℝ, ‖iteratedDeriv (N + 2) φ x‖)) := rfl

lemma m03J03_summable_polynomial_fourier_terms
    (a : ℕ → ℂ) (A : ℝ) (N : ℕ) (hA : 0 ≤ A)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ A * (n : ℝ) ^ N)
    (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) :
    Summable (fun n : ℕ ↦ a n * m03J03_fourierPairing n φ) := by
  rw [← summable_nat_add_iff 1]
  apply Summable.of_norm_bounded
    (((summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))).mul_left
        (A * ∫ x : ℝ, ‖iteratedDeriv (N + 2) φ x‖))
  intro n
  simpa [div_eq_mul_inv, mul_assoc] using
    m03J03_norm_fourier_term_le_inv_sq a A N (n + 1) hA ha (Nat.succ_pos n) φ

/-- On a fixed compact support, the `L¹` norm of an iterated derivative is
controlled by the corresponding defining seminorm. -/
lemma m03J03_integral_norm_iteratedDeriv_le_seminorm
    (K : Compacts ℝ) (k : ℕ) (f : ContDiffMapSupportedIn ℝ ℝ ⊤ K) :
    (∫ x : ℝ, ‖iteratedDeriv k f x‖) ≤
      volume.real (K : Set ℝ) * N[ℝ]_{K, k} f := by
  have hzero : ∀ x, x ∉ (K : Set ℝ) → ‖iteratedDeriv k f x‖ = 0 := by
    intro x hx
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    simp [f.iteratedFDeriv_zero_on_compl hx]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hbound : ‖∫ x : ℝ in (K : Set ℝ), ‖iteratedDeriv k f x‖‖ ≤
      N[ℝ]_{K, k} f * volume.real (K : Set ℝ) :=
    norm_setIntegral_le_of_norm_le_const (μ := volume)
    K.isCompact.measure_lt_top
    (fun x (_hx : x ∈ (K : Set ℝ)) ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
        ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      exact ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top
        (𝕜 := ℝ) (f := f) (x := x))
  have hnonneg : 0 ≤ ∫ x in (K : Set ℝ), ‖iteratedDeriv k f x‖ :=
    integral_nonneg (fun _ ↦ norm_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg] at hbound
  simpa [mul_comm] using hbound

lemma m03J03_fourierPairing_add (n : ℕ)
    (φ ψ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) :
    m03J03_fourierPairing n (φ + ψ) =
      m03J03_fourierPairing n φ + m03J03_fourierPairing n ψ := by
  unfold m03J03_fourierPairing
  have hφ : Integrable (fun x : ℝ ↦
      Complex.exp ((n : ℂ) * Complex.I * (x : ℂ)) * φ x) :=
    (m03J03_contDiff_fourier_mul n φ).continuous.integrable_of_hasCompactSupport
      (m03J03_hasCompactSupport_fourier_mul n φ)
  have hψ : Integrable (fun x : ℝ ↦
      Complex.exp ((n : ℂ) * Complex.I * (x : ℂ)) * ψ x) :=
    (m03J03_contDiff_fourier_mul n ψ).continuous.integrable_of_hasCompactSupport
      (m03J03_hasCompactSupport_fourier_mul n ψ)
  simpa [mul_add] using integral_add hφ hψ

lemma m03J03_fourierPairing_smul (n : ℕ) (c : ℝ)
    (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) :
    m03J03_fourierPairing n (c • φ) = c • m03J03_fourierPairing n φ := by
  unfold m03J03_fourierPairing
  have heq : (fun x : ℝ ↦ Complex.exp ((n : ℂ) * Complex.I * (x : ℂ)) *
      ((c • φ) x : ℂ)) = fun x : ℝ ↦ (c : ℂ) *
        (Complex.exp ((n : ℂ) * Complex.I * (x : ℂ)) * φ x) := by
    funext x
    simp [mul_comm, mul_left_comm]
  rw [heq]
  change (∫ x : ℝ, (c : ℂ) *
      (Complex.exp ((n : ℂ) * Complex.I * (x : ℂ)) * φ x)) =
    (c : ℂ) * ∫ x : ℝ, Complex.exp ((n : ℂ) * Complex.I * (x : ℂ)) * φ x
  exact integral_const_mul (c : ℂ) _

/-- The pointwise-summable Fourier series as an algebraic linear map.  Its
continuity is established compact stage by compact stage below. -/
noncomputable def m03J03_polynomialFourierLinearMap
    (a : ℕ → ℂ) (A : ℝ) (N : ℕ) (hA : 0 ≤ A)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ A * (n : ℝ) ^ N) :
    TestFunction (⊤ : Opens ℝ) ℝ ⊤ →ₗ[ℝ] ℂ where
  toFun φ := ∑' n : ℕ, a n * m03J03_fourierPairing n φ
  map_add' φ ψ := by
    rw [← (m03J03_summable_polynomial_fourier_terms a A N hA ha φ).tsum_add
      (m03J03_summable_polynomial_fourier_terms a A N hA ha ψ)]
    apply tsum_congr
    intro n
    rw [m03J03_fourierPairing_add]
    ring
  map_smul' c φ := by
    have hs := (m03J03_summable_polynomial_fourier_terms a A N hA ha φ).hasSum.const_smul c
    change (∑' n : ℕ, a n * m03J03_fourierPairing n (c • φ)) =
      c • (∑' n : ℕ, a n * m03J03_fourierPairing n φ)
    calc
      (∑' n : ℕ, a n * m03J03_fourierPairing n (c • φ)) =
          ∑' n : ℕ, c • (a n * m03J03_fourierPairing n φ) := by
        apply tsum_congr
        intro n
        rw [m03J03_fourierPairing_smul]
        simp
        ring
      _ = c • (∑' n : ℕ, a n * m03J03_fourierPairing n φ) := hs.tsum_eq

/-- Restriction of the algebraic Fourier sum to one compact-support stage. -/
noncomputable def m03J03_polynomialFourierSupportedLinearMap
    (a : ℕ → ℂ) (A : ℝ) (N : ℕ) (hA : 0 ≤ A)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ A * (n : ℝ) ^ N)
    (K : Compacts ℝ) : ContDiffMapSupportedIn ℝ ℝ ⊤ K →ₗ[ℝ] ℂ :=
  (m03J03_polynomialFourierLinearMap a A N hA ha).comp
    (TestFunction.ofSupportedInCLM ℝ (subset_univ (K : Set ℝ))).toLinearMap

@[simp] lemma m03J03_polynomialFourierSupportedLinearMap_apply
    (a : ℕ → ℂ) (A : ℝ) (N : ℕ) (hA : 0 ≤ A)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ A * (n : ℝ) ^ N)
    (K : Compacts ℝ) (f : ContDiffMapSupportedIn ℝ ℝ ⊤ K) :
    m03J03_polynomialFourierSupportedLinearMap a A N hA ha K f =
      ∑' n : ℕ, a n * m03J03_fourierPairing n
        (TestFunction.ofSupportedIn (subset_univ (K : Set ℝ)) f) := rfl

lemma m03J03_norm_fourier_term_supported_le_inv_sq
    (a : ℕ → ℂ) (A : ℝ) (N n : ℕ) (hA : 0 ≤ A)
    (ha : ∀ m : ℕ, ‖a m‖ ≤ A * (m : ℝ) ^ N) (hn : 0 < n)
    (K : Compacts ℝ) (f : ContDiffMapSupportedIn ℝ ℝ ⊤ K) :
    ‖a n * m03J03_fourierPairing n
        (TestFunction.ofSupportedIn (subset_univ (K : Set ℝ)) f)‖ ≤
      (A * (volume.real (K : Set ℝ) * N[ℝ]_{K, N + 2} f)) /
        (n : ℝ) ^ 2 := by
  refine (m03J03_norm_fourier_term_le_inv_sq a A N n hA ha hn
    (TestFunction.ofSupportedIn (subset_univ (K : Set ℝ)) f)).trans ?_
  gcongr
  simpa using m03J03_integral_norm_iteratedDeriv_le_seminorm K (N + 2) f

lemma m03J03_norm_fourier_term_zero_supported_le
    (a : ℕ → ℂ) (A : ℝ) (N : ℕ) (hA : 0 ≤ A)
    (ha : ∀ m : ℕ, ‖a m‖ ≤ A * (m : ℝ) ^ N)
    (K : Compacts ℝ) (f : ContDiffMapSupportedIn ℝ ℝ ⊤ K) :
    ‖a 0 * m03J03_fourierPairing 0
        (TestFunction.ofSupportedIn (subset_univ (K : Set ℝ)) f)‖ ≤
      A * (volume.real (K : Set ℝ) * N[ℝ]_{K, 0} f) := by
  have ha0 : ‖a 0‖ ≤ A := by
    cases N with
    | zero => simpa using ha 0
    | succ N =>
        have hz : ‖a 0‖ ≤ 0 := by simpa using ha 0
        exact hz.trans hA
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_left _ (norm_nonneg (a 0))).trans
    (mul_le_mul_of_nonneg_right ha0 (by positivity))
  unfold m03J03_fourierPairing
  refine (norm_integral_le_integral_norm _).trans ?_
  simpa using m03J03_integral_norm_iteratedDeriv_le_seminorm K 0 f

noncomputable def m03J03_invSqSum : ℝ :=
  ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ 2

lemma m03J03_summable_invSqShift :
    Summable (fun n : ℕ ↦ 1 / ((n + 1 : ℕ) : ℝ) ^ 2) :=
  (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))

lemma m03J03_invSqSum_nonneg : 0 ≤ m03J03_invSqSum := by
  unfold m03J03_invSqSum
  exact tsum_nonneg fun n ↦ by positivity

lemma m03J03_norm_polynomialFourierSupportedLinearMap_le
    (a : ℕ → ℂ) (A : ℝ) (N : ℕ) (hA : 0 ≤ A)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ A * (n : ℝ) ^ N)
    (K : Compacts ℝ) (f : ContDiffMapSupportedIn ℝ ℝ ⊤ K) :
    ‖m03J03_polynomialFourierSupportedLinearMap a A N hA ha K f‖ ≤
      A * volume.real (K : Set ℝ) *
        (N[ℝ]_{K, 0} f + m03J03_invSqSum * N[ℝ]_{K, N + 2} f) := by
  let φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤ :=
    TestFunction.ofSupportedIn (subset_univ (K : Set ℝ)) f
  have hs := m03J03_summable_polynomial_fourier_terms a A N hA ha φ
  rw [m03J03_polynomialFourierSupportedLinearMap_apply]
  refine (norm_tsum_le_tsum_norm hs.norm).trans ?_
  rw [← hs.norm.sum_add_tsum_nat_add 1]
  simp only [Finset.sum_range_one]
  have htail : (∑' n : ℕ, ‖a (n + 1) * m03J03_fourierPairing (n + 1) φ‖) ≤
      ∑' n : ℕ, (A * (volume.real (K : Set ℝ) * N[ℝ]_{K, N + 2} f)) /
        ((n + 1 : ℕ) : ℝ) ^ 2 := by
    apply Summable.tsum_le_tsum
    · intro n
      exact m03J03_norm_fourier_term_supported_le_inv_sq
        a A N (n + 1) hA ha (Nat.succ_pos n) K f
    · exact (summable_nat_add_iff 1).mpr hs.norm
    · simpa [div_eq_mul_inv] using
        m03J03_summable_invSqShift.mul_left
          (A * (volume.real (K : Set ℝ) * N[ℝ]_{K, N + 2} f))
  calc
    ‖a 0 * m03J03_fourierPairing 0 φ‖ +
        ∑' n : ℕ, ‖a (n + 1) * m03J03_fourierPairing (n + 1) φ‖ ≤
      A * (volume.real (K : Set ℝ) * N[ℝ]_{K, 0} f) +
        ∑' n : ℕ, (A * (volume.real (K : Set ℝ) * N[ℝ]_{K, N + 2} f)) /
          ((n + 1 : ℕ) : ℝ) ^ 2 :=
      add_le_add (m03J03_norm_fourier_term_zero_supported_le a A N hA ha K f) htail
    _ = A * volume.real (K : Set ℝ) *
        (N[ℝ]_{K, 0} f + m03J03_invSqSum * N[ℝ]_{K, N + 2} f) := by
      have hfactor :
          (∑' n : ℕ,
              (A * (volume.real (K : Set ℝ) * N[ℝ]_{K, N + 2} f)) /
                ((n + 1 : ℕ) : ℝ) ^ 2) =
            (A * (volume.real (K : Set ℝ) * N[ℝ]_{K, N + 2} f)) *
              m03J03_invSqSum := by
        unfold m03J03_invSqSum
        simp only [div_eq_mul_inv]
        rw [tsum_mul_left]
        simp only [one_mul]
      rw [hfactor]
      ring

lemma m03J03_norm_polynomialFourierSupportedLinearMap_le_finsetSup
    (a : ℕ → ℂ) (A : ℝ) (N : ℕ) (hA : 0 ≤ A)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ A * (n : ℝ) ^ N)
    (K : Compacts ℝ) (f : ContDiffMapSupportedIn ℝ ℝ ⊤ K) :
    ‖m03J03_polynomialFourierSupportedLinearMap a A N hA ha K f‖ ≤
      (A * volume.real (K : Set ℝ) * (1 + m03J03_invSqSum)) *
        (({0, N + 2} : Finset ℕ).sup
          (ContDiffMapSupportedIn.seminorm ℝ ℝ ℝ ⊤ K)) f := by
  let q := (({0, N + 2} : Finset ℕ).sup
    (ContDiffMapSupportedIn.seminorm ℝ ℝ ℝ ⊤ K)) f
  have h0 : N[ℝ]_{K, 0} f ≤ q :=
    Seminorm.le_finset_sup_apply (by simp)
  have hk : N[ℝ]_{K, N + 2} f ≤ q :=
    Seminorm.le_finset_sup_apply (by simp)
  have hq : 0 ≤ q := apply_nonneg _ _
  have hz := m03J03_invSqSum_nonneg
  refine (m03J03_norm_polynomialFourierSupportedLinearMap_le
    a A N hA ha K f).trans ?_
  have hinner : N[ℝ]_{K, 0} f +
      m03J03_invSqSum * N[ℝ]_{K, N + 2} f ≤
      (1 + m03J03_invSqSum) * q := by
    nlinarith
  simpa [q, mul_assoc] using mul_le_mul_of_nonneg_left hinner
    (mul_nonneg hA measureReal_nonneg)

noncomputable def m03J03_polynomialFourierSupportedCLM
    (a : ℕ → ℂ) (A : ℝ) (N : ℕ) (hA : 0 ≤ A)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ A * (n : ℝ) ^ N)
    (K : Compacts ℝ) : ContDiffMapSupportedIn ℝ ℝ ⊤ K →L[ℝ] ℂ where
  toLinearMap := m03J03_polynomialFourierSupportedLinearMap a A N hA ha K
  cont := by
    apply WithSeminorms.continuous_normedSpace_rng ℂ
      (ContDiffMapSupportedIn.withSeminorms ℝ ℝ ℝ ⊤ K)
    let C : NNReal := ⟨A * volume.real (K : Set ℝ) *
      (1 + m03J03_invSqSum),
      mul_nonneg (mul_nonneg hA measureReal_nonneg)
        (add_nonneg zero_le_one m03J03_invSqSum_nonneg)⟩
    refine ⟨{0, N + 2}, C, ?_⟩
    intro f
    change ‖m03J03_polynomialFourierSupportedLinearMap a A N hA ha K f‖ ≤ _
    simpa [C] using
      m03J03_norm_polynomialFourierSupportedLinearMap_le_finsetSup
        a A N hA ha K f

@[simp] lemma m03J03_polynomialFourierSupportedCLM_apply
    (a : ℕ → ℂ) (A : ℝ) (N : ℕ) (hA : 0 ≤ A)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ A * (n : ℝ) ^ N)
    (K : Compacts ℝ) (f : ContDiffMapSupportedIn ℝ ℝ ⊤ K) :
    m03J03_polynomialFourierSupportedCLM a A N hA ha K f =
      m03J03_polynomialFourierSupportedLinearMap a A N hA ha K f := rfl

noncomputable def m03J03_polynomialFourierDistribution
    (a : ℕ → ℂ) (A : ℝ) (N : ℕ) (hA : 0 ≤ A)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ A * (n : ℝ) ^ N) :
    Distribution (⊤ : Opens ℝ) ℂ ⊤ :=
  TestFunction.limitCLM ℝ
    (m03J03_polynomialFourierLinearMap a A N hA ha)
    (fun K _ ↦ m03J03_polynomialFourierSupportedCLM a A N hA ha K)
    (fun _ _ _ ↦ rfl)

@[simp] lemma m03J03_polynomialFourierDistribution_apply
    (a : ℕ → ℂ) (A : ℝ) (N : ℕ) (hA : 0 ≤ A)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ A * (n : ℝ) ^ N)
    (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) :
    m03J03_polynomialFourierDistribution a A N hA ha φ =
      ∑' n : ℕ, a n * m03J03_fourierPairing n φ := rfl

/-- It is enough to construct the two regular half-line functionals.  The
first integration-by-parts identity identifies `DT`; the second derivative is
then the continuous distribution `δ₀ - T`, and the second identity supplies
its integral presentation. -/
theorem m03J03_heaviside_bridge_of_regular_distributions
    (T DT : Distribution (⊤ : Opens ℝ) ℝ ⊤)
    (hT : ∀ φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤,
      T φ = ∫ x : ℝ, m03J03Heaviside x * Real.sin x * φ x)
    (hDT : ∀ φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤,
      DT φ = ∫ x : ℝ, m03J03Heaviside x * Real.cos x * φ x) :
    ∃ T DT D2T : Distribution (⊤ : Opens ℝ) ℝ ⊤,
      ∀ φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤,
        T φ = ∫ x : ℝ, m03J03Heaviside x * Real.sin x * φ x ∧
        DT φ = -∫ x : ℝ,
          m03J03Heaviside x * Real.sin x * deriv φ x ∧
        DT φ = ∫ x : ℝ, m03J03Heaviside x * Real.cos x * φ x ∧
        D2T φ = ∫ x : ℝ,
          m03J03Heaviside x * Real.sin x * iteratedDeriv 2 φ x ∧
        D2T φ = φ 0 - T φ := by
  refine ⟨T, DT, m03J03_deltaZero - T, fun φ ↦ ?_⟩
  have hfirst := m03J03_heaviside_sin_integral_deriv φ
  have hsecond := m03J03_heaviside_sin_integral_iteratedDeriv_two φ
  constructor
  · exact hT φ
  constructor
  · rw [hDT φ]
    exact hfirst.symm
  constructor
  · exact hDT φ
  constructor
  · change φ 0 - T φ = _
    rw [hT φ]
    exact hsecond.symm
  · change φ 0 - T φ = φ 0 - T φ
    rfl

lemma m03J03_abs_eval_not_distribution :
    ¬ ∃ T : Distribution (⊤ : Opens ℝ) ℝ ⊤,
      ∀ φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤, T φ = |φ 0| := by
  rintro ⟨T, hT⟩
  let b : ContDiffBump (0 : ℝ) := default
  let φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤ :=
    ⟨b, b.contDiff, b.hasCompactSupport, subset_univ _⟩
  have hφ : φ 0 = 1 := by
    exact b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
  have hpos := hT φ
  have hneg := hT (-φ)
  rw [map_neg, hpos] at hneg
  simp [hφ] at hneg
  norm_num at hneg

/-- Why this unblocks `apm_m03j03`: this is the locally finite one-sided
Dirac-comb constructor, including the compact-dependent seminorm estimate
needed for LF-continuity.  It supplies the first conjunct of the main theorem. -/
theorem apm_m03J03_bridge_dirac_comb :
    ∃ T : Distribution (⊤ : Opens ℝ) ℂ ⊤,
      ∀ φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤,
        T φ = ∑' n : ℕ, (φ n : ℂ) := by
  exact ⟨m03J03_diracComb, m03J03_diracComb_apply⟩

/-- Why this unblocks `apm_m03j03`: repeated integration by parts converts
polynomial coefficient growth into summable decay of the Fourier pairings;
the resulting LF-continuous sum is the distribution required by the second
conjunct. -/
theorem apm_m03J03_bridge_polynomial_fourier_series
    (a : ℕ → ℂ) (ha : ∃ (A : ℝ) (N : ℕ), 0 ≤ A ∧
      ∀ n : ℕ, ‖a n‖ ≤ A * (n : ℝ) ^ N) :
    ∃ T : Distribution (⊤ : Opens ℝ) ℂ ⊤,
      ∀ φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤,
        HasSum (fun n : ℕ =>
          a n * (∫ x : ℝ,
            Complex.exp ((n : ℂ) * Complex.I * (x : ℂ)) * φ x)) (T φ) := by
  obtain ⟨A, N, hA, ha⟩ := ha
  refine ⟨m03J03_polynomialFourierDistribution a A N hA ha, fun φ ↦ ?_⟩
  rw [m03J03_polynomialFourierDistribution_apply]
  exact (m03J03_summable_polynomial_fourier_terms a A N hA ha φ).hasSum

/-- Why this unblocks `apm_m03j03`: this bundles the three regular
LF-continuous functionals for `H*sin` and its first two distributional
derivatives.  The last equality contains the missing second half-line
integration-by-parts identity and its Dirac boundary term. -/
theorem apm_m03J03_bridge_heaviside_sin_distributions :
    ∃ T DT D2T : Distribution (⊤ : Opens ℝ) ℝ ⊤,
      ∀ φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤,
        T φ = ∫ x : ℝ, m03J03Heaviside x * Real.sin x * φ x ∧
        DT φ = -∫ x : ℝ,
          m03J03Heaviside x * Real.sin x * deriv φ x ∧
        DT φ = ∫ x : ℝ, m03J03Heaviside x * Real.cos x * φ x ∧
        D2T φ = ∫ x : ℝ,
          m03J03Heaviside x * Real.sin x * iteratedDeriv 2 φ x ∧
        D2T φ = φ 0 - T φ := by
  apply m03J03_heaviside_bridge_of_regular_distributions
    (m03J03_boundedWeightIntegralDistribution m03J03_sinWeight)
    (m03J03_boundedWeightIntegralDistribution m03J03_cosWeight)
  · intro φ
    rw [m03J03_boundedWeightIntegralDistribution_apply]
    change (∫ x in Ioi (0 : ℝ), Real.sin x * φ x) = _
    symm
    simpa [mul_assoc] using
      m03J03_integral_heaviside_mul (fun x ↦ Real.sin x * φ x)
  · intro φ
    rw [m03J03_boundedWeightIntegralDistribution_apply]
    change (∫ x in Ioi (0 : ℝ), Real.cos x * φ x) = _
    symm
    simpa [mul_assoc] using
      m03J03_integral_heaviside_mul (fun x ↦ Real.cos x * φ x)

/-- The one-sided Dirac comb, polynomial-growth Fourier series, the two
distributional derivatives of `H sin`, and the absolute-value non-example. -/
theorem apm_m03j03 :
    (∃ T : Distribution (⊤ : Opens ℝ) ℂ ⊤,
      ∀ φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤,
        T φ = ∑' n : ℕ, (φ n : ℂ)) ∧
    (∀ a : ℕ → ℂ, (∃ (A : ℝ) (N : ℕ), 0 ≤ A ∧
        ∀ n : ℕ, ‖a n‖ ≤ A * (n : ℝ) ^ N) →
      ∃ T : Distribution (⊤ : Opens ℝ) ℂ ⊤,
        ∀ φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤,
          HasSum (fun n : ℕ =>
            a n * (∫ x : ℝ,
              Complex.exp ((n : ℂ) * Complex.I * (x : ℂ)) * φ x)) (T φ)) ∧
    (∃ T DT D2T : Distribution (⊤ : Opens ℝ) ℝ ⊤,
      ∀ φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤,
        T φ = ∫ x : ℝ, m03J03Heaviside x * Real.sin x * φ x ∧
        DT φ = -∫ x : ℝ,
          m03J03Heaviside x * Real.sin x * deriv φ x ∧
        DT φ = ∫ x : ℝ, m03J03Heaviside x * Real.cos x * φ x ∧
        D2T φ = ∫ x : ℝ,
          m03J03Heaviside x * Real.sin x * iteratedDeriv 2 φ x ∧
        D2T φ = φ 0 - T φ) ∧
    (¬ ∃ T : Distribution (⊤ : Opens ℝ) ℝ ⊤,
      ∀ φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤, T φ = |φ 0|) := by
  /-
  CLOSER HOP 1 (partial). The fourth conjunct is now closed independently by
  `m03J03_abs_eval_not_distribution`: a compactly supported smooth bump equals
  one at zero, while distribution linearity sends its negation to the negative
  value, contradicting absolute evaluation.

  The first three distribution-construction clauses remain. Mathlib searches
  found useful constructors and Fourier operations for `TemperedDistribution`
  (including `TemperedDistribution.delta` and regular tempered
  distributions), but no compiled locally finite Dirac-sum constructor or
  polynomial-growth Fourier-series convergence theorem producing the
  `Distribution (⊤ : Opens ℝ) ℂ ⊤` required here.

  Renewed searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, the solved
  distribution corpus, Mathlib source, and git history found no constructor
  that resolves them. A direct proof must separately build continuous linear maps on the LF
  test-function space: local finiteness and compact-dependent seminorm bounds
  for the Dirac comb; `N + 2` integrations by parts and summability for the
  Fourier series; regular distributions plus two half-line integration-by-parts
  identities for `H * sin`; and a bundled test function nonzero at zero to
  refute linearity of `φ ↦ |φ 0|`. Pointwise formulas alone do not discharge
  the continuity fields of `Distribution`. No solved sibling contains this
  combined construction, so no sibling code was reused and the frozen
  statement was left unchanged.

  CLOSER HOP 2: the Heaviside/set-integral conversion needed by both
  integration-by-parts identities is now compiled as
  `m03J03_integral_heaviside_mul`. It proves for an arbitrary real function
  `g` that integrating `m03J03Heaviside x * g x` over `ℝ` is definitionally
  the set integral over `Ioi 0`, by identifying the product a.e. with the
  indicator. This removes the discontinuous Heaviside representative from the
  remaining analytic calculation.

  Searches beyond hop 1 covered the improper-integral integration-by-parts
  theorems, compact-support multiplication/derivative APIs, and regular and
  tempered distribution constructors. The first group supplies the intended
  next route after the new reduction, but completing its endpoint-at-infinity
  limits and then bundling all three functionals as LF-continuous maps remains
  open. No packaged Dirac-comb or polynomial-growth Fourier-series constructor
  was found. The frozen statement remains unchanged.

  CLOSER HOP 3 closes the first derivative identity at function level.
  `m03J03_heaviside_sin_integral_deriv` applies the compact-support endpoint
  theorem directly to `g x = sin x * φ x`, proves the product derivative
  formula, and obtains `-∫ H sin φ' = ∫ H cos φ`. No explicit endpoint limit
  is needed.

  Renewed searches covered the countable sum-of-Dirac measure integral API,
  tempered-measure constructors, TestFunction-to-Schwartz maps, and siblings
  `m02J01` and `m95J05`. The sum-of-Dirac results compute integrals once
  summability is available, but do not establish local finiteness/temperate
  growth of the one-sided counting measure or construct the required
  LF-continuous `Distribution`. The remaining bridge is the second half-line
  identity, construction and LF-continuity of the three regular functionals,
  and the Dirac-comb/Fourier-series constructors. The frozen statement remains
  unchanged.

  CLOSER HOP 4 closes the second derivative identity at function level.
  `m03J03_derivTestFunction` bundles the ordinary derivative while preserving
  smoothness and compact support, allowing the first identity to be applied
  again. Applying compact-support integration by parts to `cos * φ` supplies
  the boundary value `φ 0`; together these give exactly
  `∫ H sin φ'' = φ 0 - ∫ H sin φ`. Thus all analytic equalities required by
  the Heaviside conjunct are proved. The remaining work is representational:
  construct the three LF-continuous integral functionals, plus the independent
  Dirac-comb and polynomial-growth Fourier-series distributions.

  CLOSER HOP 5 reduces the Heaviside distribution construction from three
  functionals to two regular ones. Evaluation at zero is now explicitly
  constructed as a continuous distribution by factoring through bounded
  continuous functions. Given regular distributions for `H*sin` and `H*cos`,
  `m03J03_heaviside_bridge_of_regular_distributions` takes the second
  derivative to be `δ₀ - T` and uses the two compiled integration identities
  to prove every requested formula. The residual Heaviside obligation is now
  precisely LF-continuity of the two order-zero half-line integrals.

  CLOSER HOP 6 closes that LF-continuity obligation and hence the entire
  Heaviside bridge. For a bounded continuous weight, the integral over
  `K ∩ Ioi 0` is bounded by `‖w‖ * volume (K ∩ Ioi 0) * ‖φ‖`; composing this
  fixed-support functional with the bounded-continuous-function inclusion and
  applying `TestFunction.limitCLM` gives the global distribution. Instantiating
  the constructor with `sin` and `cos` completes
  `apm_m03J03_bridge_heaviside_sin_distributions` without axioms. Only the
  independent Dirac-comb and polynomial Fourier-series constructors remain.

  CLOSER HOP 7 closes the Dirac-comb constructor. Each compact support is
  contained in a closed ball and hence misses every natural number beyond an
  explicit Archimedean cutoff. The compact-stage functional is therefore a
  finite sum of continuous point evaluations (postcomposed with `ofReal`),
  while `tsum_eq_sum` identifies it with the requested global series.
  `TestFunction.limitCLM` supplies LF continuity. The only remaining analytic
  constructor is the polynomial-growth Fourier series.

  CLOSER HOP 8 begins the final Fourier constructor at its reusable analytic
  seam. `m03J03_hasDerivAt_fourier_mul` proves the exact derivative formula
  for the complex exponential kernel times a real test function, with all
  real-to-complex derivative coercions explicit. `m03J03_integral_deriv_eq_zero`
  proves the whole-line compact-support endpoint theorem for complex-valued
  functions by combining Mathlib's two half-line endpoint identities. These
  are the two ingredients for the integration-by-parts recurrence; iteration,
  decay, summability, and LF-continuous packaging remain.

  CLOSER HOP 9 compiles the recurrence and its arbitrary iteration.
  `m03J03_fourierPairing_mul_freq` integrates the kernel derivative, separates
  the two integrable summands, and proves `(n*I) F_n(φ) = -F_n(φ')`.
  `m03J03_iterDerivTestFunction` bundles arbitrary derivatives and is proved
  pointwise equal to `iteratedDeriv`; induction then yields the denominator-free
  identity `(n*I)^k F_n(φ) = (-1)^k F_n(φ^(k))`, valid even at `n = 0`.
  Quantitative norm decay for positive frequencies, summability, and LF
  packaging remain.

  CLOSER HOP 10 proves quantitative decay and pointwise summability.
  Taking norms in the iterated recurrence gives
  `n^k * ‖F_n φ‖ ≤ ∫ ‖φ^(k)‖`. With `k = N + 2`, the polynomial coefficient
  bound cancels the first `N` powers and dominates every positive-frequency
  term by a constant times `1 / n^2`; shifting past frequency zero and applying
  the real p-series theorem proves summability. The remaining seam is uniform
  compact-stage control sufficient to package these pointwise sums as an
  LF-continuous linear functional.

  CLOSER HOP 11 establishes the compact-stage seminorm estimate and algebraic
  packaging. For `f` supported in `K`, the integral of `‖f^(k)‖` is bounded by
  `volume K * N_K,k(f)`, using vanishing of the iterated Fréchet derivative off
  `K`. The Fourier pairing is proved additive and real-linear, and pointwise
  summability is bundled into `m03J03_polynomialFourierLinearMap`. What remains
  is solely the continuity proof for this linear map on each fixed-support
  stage and its `TestFunction.limitCLM` lift.

  CLOSER HOP 12 factors the algebraic series through every fixed-support
  inclusion and proves the exact termwise estimates needed for continuity.
  Positive frequencies are bounded by
  `A * volume(K) * N_K,N+2(f) / n^2`; frequency zero is separately bounded by
  `A * volume(K) * N_K,0(f)`, including the `N > 0` case where the growth
  hypothesis forces `a 0 = 0`. Summing these bounds and invoking the generated
  seminorm topology is the remaining continuity step.
  -/
  exact ⟨apm_m03J03_bridge_dirac_comb,
    fun a ha ↦ apm_m03J03_bridge_polynomial_fourier_series a ha,
    apm_m03J03_bridge_heaviside_sin_distributions,
    m03J03_abs_eval_not_distribution⟩
