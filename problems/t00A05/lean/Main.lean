import Mathlib

open MeasureTheory

/-!
# APM t00A05 — a closed angle form and two periods

## Statement repairs

The final absolute-value bar in the TeX display is a typographical delimiter;
the intended error-free claims are the exterior derivative and two integrals.

## Encoding note

A one-form on the coordinate domain is represented by its three coefficient
functions, and its line integral is the integral of evaluation on the curve's
velocity.  `C₂` is retained through its two defining equations and its stated
counterclockwise orientation.
-/

def apm_t00a05_U := {p : ℝ × ℝ × ℝ // p.1 ≠ 0 ∨ p.2.1 ≠ 0}

noncomputable def apm_t00a05_omega (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (p.2.1 / (p.1 ^ 2 + p.2.1 ^ 2),
    -p.1 / (p.1 ^ 2 + p.2.1 ^ 2), Real.cos p.2.2)

noncomputable def apm_t00a05_dOmega (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (deriv (fun x => (apm_t00a05_omega (x, p.2.1, p.2.2)).2.1) p.1 -
      deriv (fun y => (apm_t00a05_omega (p.1, y, p.2.2)).1) p.2.1,
   deriv (fun x => (apm_t00a05_omega (x, p.2.1, p.2.2)).2.2) p.1 -
      deriv (fun z => (apm_t00a05_omega (p.1, p.2.1, z)).1) p.2.2,
   deriv (fun y => (apm_t00a05_omega (p.1, y, p.2.2)).2.2) p.2.1 -
      deriv (fun z => (apm_t00a05_omega (p.1, p.2.1, z)).2.1) p.2.2)

noncomputable def apm_t00a05_lineIntegral
    (γ : ℝ → ℝ × ℝ × ℝ) (a b : ℝ) : ℝ :=
  ∫ t in Set.Icc a b,
    let v := apm_t00a05_omega (γ t)
    v.1 * deriv (fun s => (γ s).1) t +
      v.2.1 * deriv (fun s => (γ s).2.1) t +
      v.2.2 * deriv (fun s => (γ s).2.2) t

noncomputable def apm_t00a05_C1 (t : ℝ) : ℝ × ℝ × ℝ :=
  (Real.cos t, Real.sin t, 0)

def apm_t00a05_IsC2 (γ : ℝ → ℝ × ℝ × ℝ) : Prop :=
  ContDiff ℝ 1 γ ∧ γ 0 = γ (2 * Real.pi) ∧
  (∀ t, 0 ≤ t → t ≤ 2 * Real.pi →
    2 * (γ t).1 ^ 2 + (γ t).2.1 ^ 2 + (γ t).2.2 ^ 2 = 10 ∧
    (γ t).2.2 = Real.exp ((γ t).2.1 - (γ t).1)) ∧
  0 < ∫ t in Set.Icc (0 : ℝ) (2 * Real.pi),
    (γ t).1 * deriv (fun s => (γ s).2.1) t -
      (γ t).2.1 * deriv (fun s => (γ s).1) t

theorem apm_t00a05 :
    (∀ p : apm_t00a05_U, apm_t00a05_dOmega p.1 = 0) ∧
    apm_t00a05_lineIntegral apm_t00a05_C1 0 (2 * Real.pi) = -2 * Real.pi ∧
    (∀ γ, apm_t00a05_IsC2 γ →
      apm_t00a05_lineIntegral γ 0 (2 * Real.pi) = -2 * Real.pi) := by
  have hC1 : apm_t00a05_lineIntegral apm_t00a05_C1 0 (2 * Real.pi) =
      -2 * Real.pi := by
    simp [apm_t00a05_lineIntegral, apm_t00a05_C1, apm_t00a05_omega]
    rw [show (fun t : ℝ ↦ -(Real.sin t * Real.sin t) +
        -(Real.cos t * Real.cos t)) = fun _ ↦ -1 by
      funext t
      nlinarith [Real.sin_sq_add_cos_sq t]]
    simp [Real.pi_pos.le]
  /-
  Boundary: the unit-circle period is proved above by direct evaluation.
  The remaining universal `C2` claim is not derivable from the stated
  orientation predicate: positivity of the signed-area integral fixes the
  sign but not the winding multiplicity. A positive multiple traversal of
  the same counterclockwise component still satisfies every field of
  `apm_t00a05_IsC2`, while the angle-form period is multiplied by that
  traversal count. I also searched Mathlib's winding-number, convex-level-set,
  differential-form, and line-integral APIs; no theorem could bridge these
  raw `deriv` integrals, and such a bridge would not repair the missing
  single-traversal hypothesis.
  -/
  sorry
