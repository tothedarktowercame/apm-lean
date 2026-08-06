import Mathlib
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
# APM t03J06: a non-closed two-form and its bullet-surface integral

## Statement repairs

The hemisphere equation contains `(z - 1)^1`; this is corrected to
`(z - 1)^2`.  Exponent `2` is forced by the word "hemisphere" and by the
stated center `(0,0,1)`, radius `1`, and top point `(0,0,2)`.

## Encoding questions

Mathlib does not define integration of differential forms over oriented
manifolds.  `apm_t03J06_bulletIntegral` is a documented `sorry`-typed
placeholder precisely for integration over the explicitly defined bullet
surface, oriented so `dx ∧ dy` is positive at the top.  The ambient two-form
is a genuine continuous alternating form, its coefficient formula is exact,
and closedness and exactness use Mathlib's actual exterior derivative.
-/

noncomputable section

abbrev apm_t03J06_E3 := EuclideanSpace ℝ (Fin 3)
abbrev apm_t03J06_Form1 :=
  apm_t03J06_E3 → apm_t03J06_E3 [⋀^Fin 1]→L[ℝ] ℝ
abbrev apm_t03J06_Form2 :=
  apm_t03J06_E3 → apm_t03J06_E3 [⋀^Fin 2]→L[ℝ] ℝ

def apm_t03J06_isOmega (omega : apm_t03J06_Form2) : Prop :=
  ∀ (x : apm_t03J06_E3) (v : Fin 2 → apm_t03J06_E3),
    omega x v =
      x 2 * (v 0 0 * v 1 1 - v 0 1 * v 1 0) +
      (x 2 ^ 2 * Real.exp (x 0 * x 2) * Real.log (x 0 ^ 2 + 1) - x 1) *
        (v 0 0 * v 1 2 - v 0 2 * v 1 0) +
      (x 0 + x 1 ^ 2 * x 2 ^ 3 * Real.cos (x 1 ^ 2 + x 2 ^ 2)) *
        (v 0 1 * v 1 2 - v 0 2 * v 1 1)

def apm_t03J06_bullet : Set apm_t03J06_E3 :=
  {x | x 0 ^ 2 + x 1 ^ 2 = 1 ∧ -1 ≤ x 2 ∧ x 2 ≤ 1} ∪
  {x | x 0 ^ 2 + x 1 ^ 2 + (x 2 - 1) ^ 2 = 1 ∧ 1 ≤ x 2}

def apm_t03J06_bulletIntegral
    (_surface : Set apm_t03J06_E3) (_omega : apm_t03J06_Form2) : ℝ := by
  sorry

theorem apm_t03j06
    (omega : apm_t03J06_Form2)
    (homega : apm_t03J06_isOmega omega) :
    ContDiff ℝ (⊤ : ℕ∞) omega ∧
    (∀ x : apm_t03J06_E3,
      extDeriv omega x (fun i ↦ EuclideanSpace.single i (1 : ℝ)) = 3) ∧
    extDeriv omega ≠ 0 ∧
    ¬ (∃ eta : apm_t03J06_Form1,
      ContDiff ℝ (⊤ : ℕ∞) eta ∧ extDeriv eta = omega) ∧
    apm_t03J06_bulletIntegral apm_t03J06_bullet omega = 7 * Real.pi := by
  sorry
