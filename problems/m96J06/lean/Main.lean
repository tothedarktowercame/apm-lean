import Mathlib

/-!
# APM m96J06: A nonlinear functional equation near zero

## Statement repairs

None.

## Encoding questions

None. The open neighborhood is the explicit sup-norm ball
`{y ∈ C([-2,2]) | ‖y‖∞ < 1/48}`. Functions are represented on `ℝ` with all
continuity, bounds, and equations restricted to the exact interval `[-2,2]`.
-/

open Set

noncomputable section

def apm_m96J06_inNeighborhood (y : ℝ → ℝ) : Prop :=
  ContinuousOn y (Icc (-2 : ℝ) 2) ∧
  ∀ t ∈ Icc (-2 : ℝ) 2, |y t| < (1 / 48 : ℝ)

def apm_m96J06_isSolution (x y : ℝ → ℝ) : Prop :=
  ContinuousOn x (Icc (-2 : ℝ) 2) ∧
  ∀ t ∈ Icc (-2 : ℝ) 2,
    x t - 2 * x 0 + x (t / 2 + 1) * x (t / 2 - 1) = y t

/-- The linearization at zero is its own inverse, even before restricting to
the continuous-function Banach space. -/
def apm_m96J06_linearPart (x : ℝ → ℝ) : ℝ → ℝ :=
  fun t ↦ x t - 2 * x 0

lemma apm_m96J06_linearPart_involutive (x : ℝ → ℝ) :
    apm_m96J06_linearPart (apm_m96J06_linearPart x) = x := by
  funext t
  simp [apm_m96J06_linearPart]
  ring

/-- Both rescaled arguments in the quadratic term remain in the domain. -/
lemma apm_m96J06_half_shift_mem {t : ℝ} (ht : t ∈ Icc (-2 : ℝ) 2) :
    t / 2 + 1 ∈ Icc (-2 : ℝ) 2 ∧ t / 2 - 1 ∈ Icc (-2 : ℝ) 2 := by
  constructor <;> constructor <;> linarith [ht.1, ht.2]

theorem apm_m96j06 :
    ∀ y : ℝ → ℝ,
      apm_m96J06_inNeighborhood y →
        ∃ x : ℝ → ℝ,
          apm_m96J06_isSolution x y ∧
          ∀ t ∈ Icc (-2 : ℝ) 2, |x t| ≤ (1 / 12 : ℝ) := by
  /-
  PARTIAL.  `apm_m96J06_linearPart_involutive` proves that the linearization
  `x ↦ x - 2 x(0)` is algebraically its own inverse, and
  `apm_m96J06_half_shift_mem` proves that both arguments of the quadratic term
  remain in `[-2,2]`.

  The remaining construction must bundle continuous functions on `Icc (-2) 2`
  with their sup norm, define the quadratic self-map and prove the estimates
  `‖Q x - Q z‖ ≤ (‖x‖ + ‖z‖) * ‖x-z‖` and `‖L⁻¹‖ ≤ 3`, then apply
  `ContractingWith.exists_fixedPoint'` to the closed ball of radius `1/12`.
  Mathlib supplies that abstract fixed-point theorem (and sibling `t91A04`
  demonstrates its global wrapper), but the closed corpus and
  `ConstructionTargets/` contain no helper assembling this custom restricted
  continuous-function space and its nonlinear self-map.
  -/
  sorry
