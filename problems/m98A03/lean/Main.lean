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
  -/
  sorry
