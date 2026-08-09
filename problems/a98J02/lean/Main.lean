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
  sorry
