import Mathlib

/-!
# APM m98A03

## Statement repairs

None.

## Encoding notes

`C([0,1])` is Mathlib's genuine Banach space of continuous maps on the
subtype `[0,1]`, equipped with its sup norm.  Lebesgue measure on that subtype
is used directly in the Hammerstein integral.
-/

open MeasureTheory Set

abbrev apm_m98a03_C01 := ContinuousMap (Icc (0 : ℝ) 1) ℝ

def apm_m98a03_IsFrechetDerivativeAtOn
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : Set X) (F : X → Y) (x : X) (A : X →L[ℝ] Y) : Prop :=
  IsOpen U ∧ x ∈ U ∧ HasFDerivWithinAt F A U x

def apm_m98a03_IsHammersteinOperator
    (K : ContinuousMap ((Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1)) ℝ)
    (f : ℝ → ℝ) (F : apm_m98a03_C01 → apm_m98a03_C01) : Prop :=
  ∀ (u : apm_m98a03_C01) (x : Icc (0 : ℝ) 1),
    F u x = ∫ y : Icc (0 : ℝ) 1, K (x, y) * f (u y)

lemma apm_m98a03_integrable_kernel_section
    (K : ContinuousMap ((Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1)) ℝ)
    (f : ℝ → ℝ) (hf : Continuous f) (u : apm_m98a03_C01)
    (x : Icc (0 : ℝ) 1) :
    Integrable (fun y : Icc (0 : ℝ) 1 => K (x, y) * f (u y)) := by
  let q : ContinuousMap (Icc (0 : ℝ) 1) ℝ :=
    ⟨fun y => K (x, y) * f (u y), by fun_prop⟩
  simpa [q] using (BoundedContinuousFunction.mkOfCompact q).integrable volume

/-- Every section of the proposed derivative kernel is integrable on the
compact parameter interval. -/
lemma apm_m98a03_integrable_derivative_kernel_section
    (K : ContinuousMap ((Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1)) ℝ)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (u h : apm_m98a03_C01) (x : Icc (0 : ℝ) 1) :
    Integrable (fun y : Icc (0 : ℝ) 1 ↦
      K (x, y) * deriv f (u y) * h y) := by
  let q : ContinuousMap (Icc (0 : ℝ) 1) ℝ :=
    ⟨fun y ↦ K (x, y) * deriv f (u y) * h y, by
      exact ((K.continuous.comp (continuous_const.prodMk continuous_id)).mul
        (hf.continuous_deriv_one.comp u.continuous)).mul h.continuous⟩
  simpa [q] using (BoundedContinuousFunction.mkOfCompact q).integrable volume

/-- A uniform pointwise majorant for the derivative kernel.  This is the
estimate required by the dominated parametric-integral theorem once a bound
for `deriv f` has been chosen on the relevant compact range. -/
lemma apm_m98a03_derivative_kernel_norm_le
    (K : ContinuousMap ((Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1)) ℝ)
    (f : ℝ → ℝ) (u h : apm_m98a03_C01)
    (M : ℝ) (hM : ∀ z : ℝ, |deriv f z| ≤ M)
    (x y : Icc (0 : ℝ) 1) :
    |K (x, y) * deriv f (u y) * h y| ≤ ‖K‖ * M * ‖h‖ := by
  rw [abs_mul, abs_mul]
  exact mul_le_mul
    (mul_le_mul (K.norm_coe_le_norm (x, y)) (hM (u y))
      (abs_nonneg _) (norm_nonneg _))
    (h.norm_coe_le_norm y) (abs_nonneg _) (mul_nonneg (norm_nonneg _) (by
      exact (abs_nonneg _).trans (hM (u y))))

/-- The constant majorant occurring in
`apm_m98a03_derivative_kernel_norm_le` is integrable because the parameter
interval has finite volume. -/
lemma apm_m98a03_integrable_derivative_majorant
    (K : ContinuousMap ((Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1)) ℝ) (M : ℝ) :
    Integrable (fun _ : Icc (0 : ℝ) 1 ↦ ‖K‖ * M) := by
  exact integrable_const _

/-- Continuity of the scalar derivative supplies a uniform bound on every
compact interval. -/
lemma apm_m98a03_exists_deriv_bound_on_Icc
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (a b : ℝ) :
    ∃ M : ℝ, ∀ z ∈ Icc a b, |deriv f z| ≤ M := by
  have hcont : Continuous (fun z : ℝ ↦ |deriv f z|) :=
    hf.continuous_deriv_one.abs
  obtain ⟨M, hM⟩ := bddAbove_def.mp
    (isCompact_Icc.bddAbove_image hcont.continuousOn)
  refine ⟨M, ?_⟩
  intro z hz
  exact hM _ (mem_image_of_mem _ hz)

/-- The compact derivative bound can be chosen uniformly for every function
in the open unit sup-norm neighborhood of a fixed input. -/
lemma apm_m98a03_exists_local_deriv_bound
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (u : apm_m98a03_C01) :
    ∃ M : ℝ, ∀ v : apm_m98a03_C01, dist v u < 1 →
      ∀ y : Icc (0 : ℝ) 1, |deriv f (v y)| ≤ M := by
  obtain ⟨M, hM⟩ := apm_m98a03_exists_deriv_bound_on_Icc f hf
    (-(‖u‖ + 1)) (‖u‖ + 1)
  refine ⟨M, ?_⟩
  intro v hv y
  apply hM
  have hvu : ‖v - u‖ < 1 := by simpa [dist_eq_norm] using hv
  have huv : |v y - u y| < 1 := by
    exact lt_of_le_of_lt (by simpa [Real.norm_eq_abs] using
      (v - u).norm_coe_le_norm y) hvu
  have hu : |u y| ≤ ‖u‖ := by
    simpa [Real.norm_eq_abs] using u.norm_coe_le_norm y
  have hvabs : |v y| < ‖u‖ + 1 := calc
    |v y| = |(v y - u y) + u y| := by ring_nf
    _ ≤ |v y - u y| + |u y| := abs_add_le _ _
    _ < 1 + ‖u‖ := add_lt_add_of_lt_of_le huv hu
    _ = ‖u‖ + 1 := by ring
  exact ⟨by linarith [neg_abs_le (v y)], by linarith [le_abs_self (v y)]⟩

theorem apm_m98a03
    (K : ContinuousMap ((Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1)) ℝ)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
    ∃ (F : apm_m98a03_C01 → apm_m98a03_C01)
      (DF : apm_m98a03_C01 → (apm_m98a03_C01 →L[ℝ] apm_m98a03_C01)),
      apm_m98a03_IsHammersteinOperator K f F ∧
      (∀ u : apm_m98a03_C01,
        HasFDerivAt F (DF u) u ∧
        ∀ (h : apm_m98a03_C01) (x : Icc (0 : ℝ) 1),
          DF u h x = ∫ y : Icc (0 : ℝ) 1,
            K (x, y) * deriv f (u y) * h y) ∧
      Continuous DF := by
  /-
  PARTIAL boundary (codex). The scalar integral in the frozen Hammerstein
  formula is now certified as integrable by
  `apm_m98a03_integrable_kernel_section` (using `hf.continuous`). Mathlib's
  `ContinuousMap.integral_apply` gives the correct evaluation theorem if the
  operator is built as a `ContinuousMap`-valued Bochner integral.

  The remaining construction is substantial: package
  `u ↦ (x ↦ ∫ y, K (x,y) * f (u y))` as a continuous-map-valued operator,
  build its derivative as a bounded integral operator, prove the uniform
  Fréchet remainder estimate for the Nemytskii map from only `ContDiff ℝ 1 f`,
  and prove continuity in operator norm of `u ↦ DF u`. Searches for
  Hammerstein/Nemytskii APIs in Mathlib, all closed artifacts (including the
  partial mixed-exponent sibling `m94A04`), `ConstructionTargets`, and
  `YoungL2.lean` found no compiled theorem packaging this compact-domain
  differentiability argument.

  A further search found Mathlib's general Banach-valued theorem
  `hasFDerivAt_integral_of_dominated_of_fderiv_le` in
  `Mathlib.Analysis.Calculus.ParametricIntegral`.  This gives a viable route
  after rewriting the integrand as a `ContinuousMap` in `x`, and
  `ContinuousMap.integral_apply` then recovers the frozen pointwise formula.
  I also checked `contDiff_one_iff_hasFDerivAt`, which can supply the scalar
  derivative and its continuity.  Applying the parametric theorem still
  requires proving, uniformly for `u` in a sup-norm ball, an integrable bound
  on the `ContinuousMap`-valued derivative, its strong measurability as a map
  into continuous linear operators, and finally continuity of the resulting
  integral in operator norm.  Neither the closed corpus nor the construction
  libraries contain those missing compact-domain Nemytskii packaging lemmas.

  Closer hop 1 proves the corresponding integrability prerequisite for the
  derivative formula as
  `apm_m98a03_integrable_derivative_kernel_section`.  The proof uses
  `ContDiff.continuous_deriv_one` to make
  `y ↦ K(x,y) * deriv f (u y) * h y` a continuous map on the compact interval,
  then applies `BoundedContinuousFunction.mkOfCompact.integrable`.  Further
  searches of `ParametricIntegral`, continuous-map Bochner integration,
  operator-valued measurability, the closed corpus, and construction libraries
  found no theorem discharging the required uniform sup-ball domination or
  continuity of the resulting operator-valued integral.  Thus both frozen
  pointwise integrands are now certified integrable; uniform Fréchet control
  and operator-norm continuity remain open.

  Closer hop 2 compiles the domination arithmetic itself.  The lemma
  `apm_m98a03_derivative_kernel_norm_le` bounds the derivative integrand by
  `‖K‖ * M * ‖h‖` whenever `M` bounds `|deriv f|`; it uses the compact-domain
  sup-norm lemmas `ContinuousMap.norm_coe_le_norm`.  The companion
  `apm_m98a03_integrable_derivative_majorant` proves that the resulting
  constant majorant is integrable on the interval.  Searches of the
  parametric-integral source, closed artifacts, construction libraries, and
  git history found no packaged way to choose `M` uniformly on a sup-norm
  neighborhood and bundle the pointwise derivative as an operator-valued
  measurable map.  That localization/bundling step, followed by continuity in
  operator norm, is the remaining boundary.

  Closer hop 3 closes the previously open localization step.  The lemma
  `apm_m98a03_exists_deriv_bound_on_Icc` obtains a finite bound for
  `|deriv f|` on any compact interval from
  `ContDiff.continuous_deriv_one` and `IsCompact.bddAbove_image`.
  `apm_m98a03_exists_local_deriv_bound` then proves that, for every `u`, one
  such bound works simultaneously for every `v` in the open unit sup-norm
  ball around `u` and every parameter point.  Its proof uses
  `ContinuousMap.norm_coe_le_norm` to place all values of `v` in the fixed
  compact interval `[-(‖u‖+1), ‖u‖+1]`.

  A renewed inspection of `hasFDerivAt_integral_of_dominated_of_fderiv_le`,
  continuous-linear-map integration, the closed corpus, `LEMMA-INDEX.md`, the
  construction libraries, and git history found no wrapper turning the
  scalar kernel derivative into the required
  `C([0,1]) →L[ℝ] C([0,1])`-valued measurable integrand or proving continuity
  of its integral in operator norm.  Thus neighborhood-uniform domination is
  now complete; operator-valued bundling and operator-norm continuity remain
  the exact boundary.
  -/
  sorry
