import Mathlib

/-!
# APM m97A02: Local surjectivity of a composition operator

## Statement repairs

None.

## Encoding questions

None. The space consists of the actual `C¹` functions on `[0,1]` anchored at
the cosine fixed point. Smallness is measured solely by the derivative norm
printed in the source, and the nonlinear equation is stated pointwise on the
whole interval.
-/

open Set

noncomputable section

def apm_m97A02_inSpace (α : ℝ) (x : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 1 x (Icc 0 1) ∧ x α = 0

def apm_m97A02_derivativeBound (x : ℝ → ℝ) (r : ℝ) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 1, |derivWithin x (Icc 0 1) t| < r

def apm_m97A02_isSolution (x y : ℝ → ℝ) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 1,
    Real.sin (x t) + x (Real.cos t) = y t

theorem apm_m97a02 :
    ∀ α : ℝ, α ∈ Icc (0 : ℝ) 1 → Real.cos α = α →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ y : ℝ → ℝ,
          apm_m97A02_inSpace α y →
          apm_m97A02_derivativeBound y δ →
            ∃ x : ℝ → ℝ,
              apm_m97A02_inSpace α x ∧
              apm_m97A02_isSolution x y := by
  sorry
