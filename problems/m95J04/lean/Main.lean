import Mathlib

/-!
# APM m95J04: A nonlinear two-point boundary value problem

## Statement repairs

None. The decimal `7.99` is encoded exactly as `799 / 100`.

## Encoding questions

None. A solution is twice continuously differentiable on the exact interval
`[0,1]`, satisfies the differential equation there using within-interval
derivatives, and uniqueness is equality on that interval.
-/

open Set

noncomputable section

def apm_m95J04_green (t s : ℝ) : ℝ :=
  if t ≤ s then t * (1 - s) else s * (1 - t)

def apm_m95J04_isSolution (f : ℝ → ℝ → ℝ) (x : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 x (Icc 0 1) ∧
  x 0 = 0 ∧ x 1 = 0 ∧
  ∀ t ∈ Icc (0 : ℝ) 1,
    iteratedDerivWithin 2 x (Icc 0 1) t = f t (x t)

def apm_m95J04_specific (t x : ℝ) : ℝ :=
  Real.sin (x - t) * Real.sin (x + t - 1)

theorem apm_m95j04 :
    (∀ f : ℝ → ℝ → ℝ,
      ContinuousOn (fun p : ℝ × ℝ ↦ f p.1 p.2)
        (Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ)) →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ u v : ℝ,
        |f t u - f t v| ≤ (799 / 100 : ℝ) * |u - v|) →
      ∃ x : ℝ → ℝ,
        apm_m95J04_isSolution f x ∧
        ∀ y : ℝ → ℝ,
          apm_m95J04_isSolution f y → EqOn x y (Icc 0 1)) ∧
    (∃ x : ℝ → ℝ,
      apm_m95J04_isSolution apm_m95J04_specific x ∧
      (∀ t ∈ Icc (0 : ℝ) 1, x t = x (1 - t)) ∧
      ∀ y : ℝ → ℝ,
        apm_m95J04_isSolution apm_m95J04_specific y →
          EqOn x y (Icc 0 1)) := by
  sorry
