import Mathlib

/-!
# APM m01J05: Contraction mappings and Newton iteration

## Statement repairs

The occurrences `F(X_*)`, `F(X)`, and `x_{x+1}` are editorial variable-name
errors and are read as `F(x_*)`, `F(x)`, and `x_{k+1}` respectively. No
mathematical repair is made.

## Encoding questions

None. Newton's map uses the inverse of the actual Fréchet derivative on
`EuclideanSpace ℝ (Fin n)`, and well-definedness records bijectivity of every
derivative encountered by the iteration.
-/

open Filter

noncomputable section

def apm_m01J05_newtonStep {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  x - (fderiv ℝ F x).inverse (F x)

def apm_m01J05_newtonIterate {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) : ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => x₀
  | k + 1 => apm_m01J05_newtonStep F (apm_m01J05_newtonIterate F x₀ k)

theorem apm_m01j05 :
    (∀ (X : Type*) [MetricSpace X] [CompleteSpace X]
        (T : X → X) (q : ℝ),
      0 ≤ q → q < 1 →
      (∀ x y : X, dist (T x) (T y) ≤ q * dist x y) →
        ∃ xStar : X,
          T xStar = xStar ∧
          (∀ y : X, T y = y → y = xStar) ∧
          ∀ x₀ : X,
            Tendsto (fun k ↦ (T^[k]) x₀) atTop (nhds xStar)) ∧
    (∀ (n : ℕ)
        (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (xStar : EuclideanSpace ℝ (Fin n)),
      ContDiff ℝ ⊤ F →
      F xStar = 0 →
      Function.Bijective (fderiv ℝ F xStar) →
        ∃ ε : ℝ, 0 < ε ∧
          ∀ x₀ : EuclideanSpace ℝ (Fin n), dist x₀ xStar ≤ ε →
            (∀ k : ℕ,
              Function.Bijective
                (fderiv ℝ F (apm_m01J05_newtonIterate F x₀ k))) ∧
            Tendsto (apm_m01J05_newtonIterate F x₀) atTop (nhds xStar)) := by
  /-
  SKIPPED (frozen-statement defect). The contraction-mapping conjunct omits
  `[Nonempty X]`. Take `X := Empty`: it has `MetricSpace` and `CompleteSpace`
  instances, and the map and contraction hypotheses are vacuous for any
  `q ∈ [0,1)`, but the conclusion requires `∃ xStar : Empty, ...`.

  Mathlib's `ContractingWith.fixedPoint`, `fixedPoint_isFixedPt`, and
  `tendsto_iterate_fixedPoint` likewise require `[Nonempty X]`, confirming
  that this is a missing mathematical hypothesis rather than an API gap.
  The statement is frozen, so no repair was made.
  -/
  sorry
