import Mathlib

/-!
# APM a98J02

## Statement repairs

* The printed numerator `|f(x)-f(y)|2` is repaired to
  `|f(x)-f(y)|²`, as required by the supplied argument and dimensional
  consistency.
* The existential `δ` is required to be positive; otherwise the conclusion
  would be vacuous.

## Encoding questions

The assertion `∫₀¹ |f'|² < ∞` is encoded as integrability of the squared
within-derivative on `[0,1]`. This avoids Lean's convention that the Bochner
integral of a nonintegrable function is defined to be zero.
-/

open MeasureTheory

lemma apm_a98J02_uniform_small_set_integral {g : ℝ → ℝ} {s₀ : Set ℝ}
    (hs₀ : volume s₀ < ⊤) (hg : Integrable g (volume.restrict s₀)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s : Set ℝ,
      (volume.restrict s₀ s).toReal < δ →
      |∫ x in s, g x ∂volume.restrict s₀| < ε := by
  intro ε hε
  let μ := volume.restrict s₀
  have ht : Filter.Tendsto (fun s : Set ℝ ↦ ∫ x in s, g x ∂μ)
      (Filter.comap (fun s : Set ℝ ↦ μ s) (nhds 0)) (nhds 0) := by
    apply hg.tendsto_setIntegral_nhds_zero
    exact Filter.tendsto_comap
  have he : ∀ᶠ s in Filter.comap (fun s : Set ℝ ↦ μ s) (nhds 0),
      |∫ x in s, g x ∂μ| < ε := by
    simpa [Real.dist_eq] using ht.eventually (Metric.ball_mem_nhds 0 hε)
  change {s : Set ℝ | |∫ x in s, g x ∂μ| < ε} ∈
    Filter.comap (fun s : Set ℝ ↦ μ s) (nhds 0) at he
  rw [Filter.mem_comap] at he
  rcases he with ⟨t, ht, hpre⟩
  rcases ENNReal.nhds_zero_basis.mem_iff.mp ht with ⟨d, hd, hdt⟩
  let e : ENNReal := min d 1
  have he_pos : 0 < e := by simp [e, hd]
  have he_top : e ≠ (⊤ : ENNReal) :=
    ne_of_lt (lt_of_le_of_lt (min_le_right d 1) ENNReal.one_lt_top)
  refine ⟨e.toReal, ENNReal.toReal_pos he_pos.ne' he_top, ?_⟩
  intro s hs
  apply hpre
  apply hdt
  change μ s < d
  apply lt_of_lt_of_le ?_ (min_le_left d 1)
  apply (ENNReal.toReal_lt_toReal ?_ he_top).mp hs
  have hμuniv : μ Set.univ < ⊤ := by simpa [μ] using hs₀
  exact ne_of_lt <| lt_of_le_of_lt
    (measure_mono (show s ⊆ (Set.univ : Set ℝ) from Set.subset_univ s)) hμuniv

lemma apm_a98J02_integral_sq_le_mul_integral_sq {g : ℝ → ℝ} {y x : ℝ}
    (hyx : y ≤ x) (hg : IntervalIntegrable g volume y x)
    (hg2 : Integrable (fun t ↦ |g t| ^ 2) (volume.restrict (Set.Ioc y x))) :
    |∫ t in y..x, g t| ^ 2 ≤ (x - y) * ∫ t in y..x, |g t| ^ 2 := by
  let μ := volume.restrict (Set.Ioc y x)
  have hgm : MemLp g 2 μ := by
    apply (memLp_two_iff_integrable_sq hg.1.aestronglyMeasurable).2
    simpa [sq_abs] using hg2
  have h1m : MemLp (fun _ : ℝ ↦ (1 : ℝ)) 2 μ := memLp_const 1
  have hh := integral_mul_norm_le_Lp_mul_Lq (p := (2 : ℝ)) (q := (2 : ℝ))
    (μ := μ) (E := ℝ) (f := g) (g := fun _ ↦ 1)
    (by constructor <;> norm_num) (by simpa using hgm) (by simpa using h1m)
  rw [intervalIntegral.integral_of_le hyx, intervalIntegral.integral_of_le hyx]
  simp [μ, Real.norm_eq_abs, hyx] at hh
  have hhalf : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
  rw [hhalf, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hh
  have hi : |∫ t in Set.Ioc y x, g t| ≤ ∫ t in Set.Ioc y x, |g t| := by
    simpa [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm (f := g) (μ := volume.restrict (Set.Ioc y x)))
  have hA : 0 ≤ ∫ t in Set.Ioc y x, |g t| ^ 2 := integral_nonneg fun _ ↦ sq_nonneg _
  have hL : 0 ≤ x - y := sub_nonneg.mpr hyx
  have hsA := Real.sq_sqrt hA
  have hsL := Real.sq_sqrt hL
  have habs : 0 ≤ |∫ t in Set.Ioc y x, g t| := abs_nonneg _
  have hroot : 0 ≤ √(∫ t in Set.Ioc y x, |g t| ^ 2) * √(x - y) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hbound : |∫ t in Set.Ioc y x, g t| ≤
      √(∫ t in Set.Ioc y x, |g t| ^ 2) * √(x - y) := by
    calc
      _ ≤ ∫ t in Set.Ioc y x, |g t| := hi
      _ ≤ _ := by simpa [sq_abs] using hh
  nlinarith

lemma apm_a98J02_sub_eq_integral_deriv (f : ℝ → ℝ)
    (hf : AbsolutelyContinuousOnInterval f 0 1)
    {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) (hx : x ≤ 1) :
    f x - f y = ∫ t in y..x, deriv f t := by
  symm
  apply AbsolutelyContinuousOnInterval.integral_deriv_eq_sub
  apply hf.mono
  rw [Set.uIcc_of_le hyx, Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  exact Set.Icc_subset_Icc hy hx

/-- Away from the two null endpoints, the within derivative in the frozen
hypothesis agrees with the ordinary derivative used by the fundamental
theorem of calculus. -/
lemma apm_a98J02_deriv_eq_derivWithin_ae (f : ℝ → ℝ) :
    ∀ᵐ t ∂volume.restrict (Set.Icc (0 : ℝ) 1),
      deriv f t = derivWithin f (Set.Icc 0 1) t := by
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    (volume.restrict (Set.Icc (0 : ℝ) 1)).ae_ne 0,
    (volume.restrict (Set.Icc (0 : ℝ) 1)).ae_ne 1] with t ht ht0 ht1
  rw [derivWithin_of_mem_nhds]
  exact Icc_mem_nhds (lt_of_le_of_ne ht.1 (Ne.symm ht0))
    (lt_of_le_of_ne ht.2 ht1)

lemma apm_a98J02_integrableOn_deriv_sq (f : ℝ → ℝ)
    (hderiv : IntegrableOn
      (fun x : ℝ => |derivWithin f (Set.Icc 0 1) x| ^ 2)
      (Set.Icc 0 1)) :
    IntegrableOn (fun x : ℝ => |deriv f x| ^ 2) (Set.Icc 0 1) := by
  apply hderiv.congr
  filter_upwards [apm_a98J02_deriv_eq_derivWithin_ae f] with t ht
  rw [ht]

/-- The squared ordinary derivative has uniformly vanishing integral on
shrinking symmetric intervals, with the ambient measure already restricted
to the frozen domain.  This is the absolute-continuity-of-integral input for
the final estimate. -/
lemma apm_a98J02_tendsto_integral_deriv_sq_symmetric (f : ℝ → ℝ)
    (hderiv : IntegrableOn
      (fun x : ℝ => |derivWithin f (Set.Icc 0 1) x| ^ 2)
      (Set.Icc 0 1)) (b : ℝ) :
    Filter.Tendsto
      (fun δ : ℝ => ∫ x in Set.Icc (b - δ) (b + δ),
        |deriv f x| ^ 2 ∂volume.restrict (Set.Icc (0 : ℝ) 1))
      (nhds 0) (nhds 0) := by
  let μ := volume.restrict (Set.Icc (0 : ℝ) 1)
  have hi : Integrable (fun x : ℝ => |deriv f x| ^ 2) μ := by
    simpa [μ] using apm_a98J02_integrableOn_deriv_sq f hderiv
  exact hi.tendsto_setIntegral_nhds_zero (tendsto_measure_Icc μ b)

theorem apm_a98j02 (f : ℝ → ℝ)
    (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hderiv : IntegrableOn
      (fun x : ℝ => |derivWithin f (Set.Icc 0 1) x| ^ 2)
      (Set.Icc 0 1)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x y : ℝ, 0 ≤ y → y < x → x ≤ 1 → |x - y| < δ →
        |f x - f y| ^ 2 / |x - y| < ε := by
  /- CLOSER HOP 2 BOUNDARY (2026-08-08).

  The derivative-conversion bridge left by hop 1 is now compiled:
  `apm_a98J02_deriv_eq_derivWithin_ae` removes the two null endpoints and
  uses `derivWithin_of_mem_nhds` on the interior, while
  `apm_a98J02_integrableOn_deriv_sq` transports the supplied integrability
  hypothesis to the ordinary derivative appearing in the FTC identity.

  The remaining estimate is now purely the analytic inequality. One must
  apply integral Cauchy--Schwarz to obtain
  `|f x-f y|² ≤ (x-y) * ∫_[y,x] |derivWithin f (Icc 0 1)|²`, and use
  absolute continuity of the integral of the integrable squared derivative to
  choose a uniform `δ`. A renewed search found Mathlib's real-valued
  `integral_mul_norm_le_Lp_mul_Lq` and
  `Integrable.tendsto_setIntegral_nhds_zero` and the ENNReal/NNReal Hölder
  inequalities, but no assembled interval lemma that squares the Bochner
  integral and normalizes the measure factor, nor a ready epsilon-delta
  uniform-small-set form of the latter sequential/filter theorem. Those two
  assembly steps remain open. The frozen statement is unchanged.

  CLOSER HOP 3 (2026-08-08): the second assembly step is now compiled in
  `apm_a98J02_tendsto_integral_deriv_sq_symmetric`.  Applying
  `Integrable.tendsto_setIntegral_nhds_zero` to the restricted measure and
  Mathlib's atomless `tendsto_measure_Icc` directly gives vanishing integrals
  on shrinking symmetric intervals, avoiding a hand-built sequential or
  epsilon--delta argument.  The remaining bridge is therefore the first
  assembly step only: instantiate integral Cauchy--Schwarz on `[y,x]`, square
  its nonnegative inequality, normalize by `x-y`, and bound that interval by
  a symmetric interval controlled by the compiled limit.  No packaged lemma
  was found that performs these coercions and normalizations.  The frozen
  statement remains unchanged.

  HOP 4: the exact local Hölder interface still needed is

      ∀ {x y : ℝ}, y ≤ x →
        |∫ t in y..x, deriv f t| ^ 2 ≤
          (x - y) * ∫ t in y..x, |deriv f t| ^ 2.

  This follows by applying `integral_mul_norm_le_Lp_mul_Lq` at exponents
  `2,2` to `deriv f` and the constant one function under
  `volume.restrict (Ioc y x)`, then normalizing the two real `rpow` factors.
  No packaged declaration performs that coercion chain.

  More importantly, the hop-3 symmetric-interval lemma is pointwise in its
  center `b`; its `δ` may depend on `b`, so it does not provide the uniform
  estimate for arbitrary `y,x` required by the frozen conclusion.  The second
  precise missing interface is therefore

      ∀ ε > 0, ∃ δ > 0, ∀ x y : ℝ,
        0 ≤ y → y ≤ x → x ≤ 1 → x - y < δ →
          ∫ t in y..x, |deriv f t| ^ 2 < ε.

  It is the uniform absolute continuity of the integral for the integrable
  nonnegative function `|deriv f|²`.  Mathlib's
  `Integrable.tendsto_setIntegral_nhds_zero` proves the underlying general
  result, but extracting this epsilon--delta interval form still requires a
  filter over varying measurable sets; the fixed-center specialization above
  cannot substitute for it. Outcomes A and B were not completed in this hop.
  The frozen statement is unchanged.
  -/
  intro ε hε
  have hsq : IntegrableOn (fun x : ℝ ↦ |deriv f x| ^ 2) (Set.Icc 0 1) :=
    apm_a98J02_integrableOn_deriv_sq f hderiv
  rcases apm_a98J02_uniform_small_set_integral
      (s₀ := Set.Icc (0 : ℝ) 1) (by simp) hsq ε hε with ⟨δ, hδ, hsmall⟩
  refine ⟨δ, hδ, ?_⟩
  intro x y hy hyx hx hxyδ
  have hyx' : y ≤ x := hyx.le
  have hsub : Set.Ioc y x ⊆ Set.Icc (0 : ℝ) 1 := by
    intro t ht
    exact ⟨hy.trans ht.1.le, ht.2.trans hx⟩
  have hsqI : Integrable (fun t : ℝ ↦ |deriv f t| ^ 2)
      (volume.restrict (Set.Ioc y x)) :=
    (show Integrable (fun t : ℝ ↦ |deriv f t| ^ 2)
      (volume.restrict (Set.Icc 0 1)) from hsq).mono_measure
        (Measure.restrict_mono_set volume hsub)
  have hg : IntervalIntegrable (deriv f) volume y x := by
    apply (hf.mono ?_).intervalIntegrable_deriv
    rw [Set.uIcc_of_le hyx', Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    exact Set.Icc_subset_Icc hy hx
  have hcs := apm_a98J02_integral_sq_le_mul_integral_sq hyx' hg hsqI
  have hmeasure : (volume.restrict (Set.Icc (0 : ℝ) 1) (Set.Ioc y x)).toReal = x - y := by
    rw [Measure.restrict_apply measurableSet_Ioc, Set.inter_eq_left.mpr hsub,
      Real.volume_Ioc]
    simp [hyx']
  have hlocalAbs : |∫ t in Set.Ioc y x, |deriv f t| ^ 2
      ∂volume.restrict (Set.Icc (0 : ℝ) 1)| < ε := by
    apply hsmall
    rw [hmeasure]
    simpa [abs_of_pos (sub_pos.mpr hyx)] using hxyδ
  have hlocal : ∫ t in y..x, |deriv f t| ^ 2 < ε := by
    rw [intervalIntegral.integral_of_le hyx']
    have heq : (volume.restrict (Set.Icc (0 : ℝ) 1)).restrict (Set.Ioc y x) =
        volume.restrict (Set.Ioc y x) := by
      rw [Measure.restrict_restrict measurableSet_Ioc]
      rw [Set.inter_eq_left.mpr hsub]
    have hn : 0 ≤ ∫ t in Set.Ioc y x, |deriv f t| ^ 2
        ∂volume.restrict (Set.Icc (0 : ℝ) 1) := integral_nonneg fun _ ↦ sq_nonneg _
    rw [abs_of_nonneg hn] at hlocalAbs
    simpa [heq] using hlocalAbs
  rw [apm_a98J02_sub_eq_integral_deriv f hf hy hyx' hx]
  rw [abs_of_pos (sub_pos.mpr hyx)]
  apply (div_lt_iff₀ (sub_pos.mpr hyx)).2
  nlinarith [mul_lt_mul_of_pos_left hlocal (sub_pos.mpr hyx)]
