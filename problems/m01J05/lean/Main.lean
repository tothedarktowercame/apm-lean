import Mathlib

/-!
# APM m01J05: Contraction mappings and Newton iteration

## Statement repairs

- Editorial variable-name errors: `F(X_*)`, `F(X)`, `x_{x+1}` are read as
  `F(x_*)`, `F(x)`, `x_{k+1}` respectively.
- Guide repair 1 (after solver refutation): added `[Nonempty X]` to the
  contraction conjunct. Without it `X := Empty` vacuously satisfies every
  hypothesis while the conclusion demands a fixed point in `Empty`, so the
  statement was false as pinned. Mathlib's `ContractingWith` API requires
  the same hypothesis.

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

universe u

theorem apm_m01j05 :
    (∀ (X : Type u) [MetricSpace X] [CompleteSpace X] [Nonempty X]
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
  Statement repair (guide, attempt 1, 2026-08): the original frozen
  contraction conjunct omitted `[Nonempty X]` and was refuted by the solver
  via `X := Empty` (terminal receipt
  4bfde3eda1076303649fb9e1d12e58fe6879ac84e4c8ad092b790281a245a75f,
  invariant :statement-refuted-by-solver). Repair adds `[Nonempty X]`,
  matching Mathlib's `ContractingWith` fixed-point API, which also requires
  it. The counterexample theorem was removed. No other mathematical change.
  -/
  sorry
