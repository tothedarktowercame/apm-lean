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

theorem apm_m99a02 :
    MemLp m99A02Function 2 (volume.restrict m99A02Omega) ∧
    ∀ i : Fin 2,
      MemLp (m99A02Derivative i) 2 (volume.restrict m99A02Omega) ∧
      IsM99A02WeakDerivative m99A02Function (m99A02Derivative i) i := by
  have hlog_pos {x : m99A02Point} (hx : x ∈ m99A02Omega) (hx0 : x ≠ 0) :
      0 < -Real.log ‖x‖ := by
    have hr : ‖x‖ < (1 / 2 : ℝ) := by
      simpa [m99A02Omega, Metric.mem_ball, dist_zero_right] using hx
    have hr0 : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hr1 : ‖x‖ < 1 := hr.trans (by norm_num)
    exact neg_pos.mpr (Real.log_neg hr0 hr1)
  /-
  Boundary: the positivity lemma above verifies that every real power in the
  displayed function and derivative is evaluated on a positive logarithmic
  base throughout the punctured disk. Completing the theorem requires a polar
  integration formula for the two-dimensional Euclidean ball, convergence of
  the Bertrand integral `∫ dr / (r * (-log r)^(4/3))`, and integration by
  parts on punctured disks with a vanishing inner-boundary flux. I searched
  Mathlib's polar-coordinate, `MemLp`, real-`rpow`, weak-derivative, and
  divergence/integration-by-parts APIs; no compiled sibling assembled those
  ingredients for this raw custom encoding in this pass.
  -/
  sorry
