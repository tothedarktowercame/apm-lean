import Mathlib

/-! # APM m99A02: a logarithmic function in `H¹` of a planar disk

## Statement repairs

None.  The value assigned at the singleton `x = 0` is immaterial for both
Sobolev membership and distributional derivatives; it is set to zero below.

## Encoding note

Mathlib does not bundle Sobolev spaces.  Membership in `H¹(Ω)` is therefore
stated by its defining data: the function and its two displayed weak
derivatives lie in `L²(Ω)`, and each derivative satisfies the distributional
integration-by-parts identity against every compactly supported smooth test
function.
-/

open MeasureTheory Set
open scoped ContDiff

noncomputable section

abbrev m99A02Point := EuclideanSpace ℝ (Fin 2)

def m99A02Omega : Set m99A02Point := Metric.ball 0 (1 / 2)

def m99A02Function (x : m99A02Point) : ℝ :=
  if x = 0 then 0 else (-Real.log ‖x‖) ^ (1 / 3 : ℝ)

def m99A02Derivative (i : Fin 2) (x : m99A02Point) : ℝ :=
  if x = 0 then 0
  else -(x i) / (3 * ‖x‖ ^ 2 * (-Real.log ‖x‖) ^ (2 / 3 : ℝ))

def IsM99A02WeakDerivative
    (f g : m99A02Point → ℝ) (i : Fin 2) : Prop :=
  ∀ φ : m99A02Point → ℝ,
    ContDiff ℝ ∞ φ → HasCompactSupport φ → Function.support φ ⊆ m99A02Omega →
      (∫ x in m99A02Omega, f x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        -∫ x in m99A02Omega, g x * φ x

/-- On the punctured domain the logarithmic base used by all real powers is positive. -/
lemma m99A02_neg_log_norm_pos {x : m99A02Point}
    (hx : x ∈ m99A02Omega) (hx0 : x ≠ 0) :
    0 < -Real.log ‖x‖ := by
  have hr : ‖x‖ < (1 / 2 : ℝ) := by
    simpa [m99A02Omega, Metric.mem_ball, dist_zero_right] using hx
  have hr0 : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hr1 : ‖x‖ < 1 := hr.trans (by norm_num)
  exact neg_pos.mpr (Real.log_neg hr0 hr1)

/-- The chosen representative is strictly positive away from the singular point. -/
lemma m99A02Function_pos {x : m99A02Point}
    (hx : x ∈ m99A02Omega) (hx0 : x ≠ 0) :
    0 < m99A02Function x := by
  rw [m99A02Function, if_neg hx0]
  exact Real.rpow_pos_of_pos (m99A02_neg_log_norm_pos hx hx0) _

/-- The singular representative is measurable; the exceptional value at the
origin is handled by a measurable singleton split. -/
lemma m99A02Function_measurable : Measurable m99A02Function := by
  unfold m99A02Function
  have hs : MeasurableSet {x : m99A02Point | x = 0} := by
    simpa only [setOf_eq_eq_singleton] using
      (measurableSet_singleton (0 : m99A02Point))
  apply Measurable.ite hs measurable_const
  exact (Real.continuous_rpow_const (by norm_num)).measurable.comp
    (Real.measurable_log.comp continuous_norm.measurable).neg

/-- Each displayed classical derivative is measurable as well. -/
lemma m99A02Derivative_measurable (i : Fin 2) :
    Measurable (m99A02Derivative i) := by
  unfold m99A02Derivative
  have hs : MeasurableSet {x : m99A02Point | x = 0} := by
    simpa only [setOf_eq_eq_singleton] using
      (measurableSet_singleton (0 : m99A02Point))
  apply Measurable.ite hs measurable_const
  fun_prop

/-- The sum of the squared displayed derivatives is the expected radial
Bertrand-integral density away from the origin. -/
lemma m99A02_sum_derivative_sq {x : m99A02Point}
    (hx : x ∈ m99A02Omega) (hx0 : x ≠ 0) :
    ∑ i : Fin 2, (m99A02Derivative i x) ^ 2 =
      1 / (9 * ‖x‖ ^ 2 * (-Real.log ‖x‖) ^ (4 / 3 : ℝ)) := by
  have hr : ‖x‖ ≠ 0 := (norm_pos_iff.mpr hx0).ne'
  have hl : 0 < -Real.log ‖x‖ := m99A02_neg_log_norm_pos hx hx0
  simp_rw [m99A02Derivative, if_neg hx0]
  rw [show (∑ i : Fin 2, (-(x i) /
      (3 * ‖x‖ ^ 2 * (-Real.log ‖x‖) ^ (2 / 3 : ℝ))) ^ 2) =
      (∑ i : Fin 2, (x i) ^ 2) /
        (3 * ‖x‖ ^ 2 * (-Real.log ‖x‖) ^ (2 / 3 : ℝ)) ^ 2 by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring]
  rw [← EuclideanSpace.real_norm_sq_eq]
  have hlpow : ((-Real.log ‖x‖) ^ (2 / 3 : ℝ)) ^ 2 =
      (-Real.log ‖x‖) ^ (4 / 3 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hl.le]
    congr 1
    norm_num
  rw [mul_pow, mul_pow, hlpow]
  field_simp [hr, ne_of_gt hl]
  ring

/-- Each coordinate derivative is dominated by the single radial density. -/
lemma m99A02_derivative_sq_le_radial (i : Fin 2) {x : m99A02Point}
    (hx : x ∈ m99A02Omega) (hx0 : x ≠ 0) :
    (m99A02Derivative i x) ^ 2 ≤
      1 / (9 * ‖x‖ ^ 2 * (-Real.log ‖x‖) ^ (4 / 3 : ℝ)) := by
  rw [← m99A02_sum_derivative_sq hx hx0]
  exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (m99A02Derivative j x))
    (Finset.mem_univ i)

theorem apm_m99a02 :
    MemLp m99A02Function 2 (volume.restrict m99A02Omega) ∧
    ∀ i : Fin 2,
      MemLp (m99A02Derivative i) 2 (volume.restrict m99A02Omega) ∧
      IsM99A02WeakDerivative m99A02Function (m99A02Derivative i) i := by
  /-
  Boundary (closer hop 3): `m99A02_neg_log_norm_pos` verifies that every real power in the
  displayed function and derivative is evaluated on a positive logarithmic
  base throughout the punctured disk; `m99A02Function_pos` records the
  corresponding pointwise fact about the chosen representative. Completing
  the theorem requires a polar
  integration formula for the two-dimensional Euclidean ball, convergence of
  the Bertrand integral `∫ dr / (r * (-log r)^(4/3))`, and integration by
  parts on punctured disks with a vanishing inner-boundary flux. The prior hop
  also proves `m99A02Function_measurable` and
  `m99A02Derivative_measurable`, so the measurable half of each `MemLp` goal is
  closed.

  This hop proves `m99A02_sum_derivative_sq`, the exact punctured-domain
  identity reducing the sum of the two derivative squares to the radial
  density `1 / (9 * ‖x‖^2 * (-log ‖x‖)^(4/3))`. It uses
  `EuclideanSpace.real_norm_sq_eq` and the real-power multiplication laws.
  Thus the coordinate algebra is closed and the remaining `MemLp` boundary is
  precisely polar transport plus the scalar Bertrand integral.

  Mathlib searches confirmed `Complex.integral_comp_polarCoord_symm`, and the
  closed sibling `a01A07` packages it as
  `integral_closedBall_zero_eq_polar`. That lemma is promising, but it is stated
  on `ℂ`; this problem uses `EuclideanSpace ℝ (Fin 2)`, so one must transport
  volume, norms, coordinates, and the open ball through the standard real
  linear isometry before reducing to the radial Bertrand integrals. No sibling
  supplies that transport or the required improper-log integrability proof.
  The weak-derivative clause additionally still needs integration by parts on
  punctured disks and the vanishing inner-boundary flux.

  Closer hop 3 adds `m99A02_derivative_sq_le_radial`.  It uses the exact sum
  identity and `Finset.single_le_sum` to dominate either coordinate derivative
  square by the same radial density.  Consequently a single transported polar
  integrability theorem will discharge both derivative `MemLp` estimates; no
  further coordinate calculation is needed.  The polar transport/scalar
  Bertrand integral and the weak-derivative boundary-flux argument remain open.
  -/
  sorry
