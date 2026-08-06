import Mathlib

/-!
# APM m94J02

## Statement repairs

The claimed bound `‖fg‖ ≤ ‖f‖‖g‖` is false for the printed weight
`n² + 1`: for `f = g = z`, the two sides are `5` and `4`. It is
minimally repaired to the sharp bound `‖fg‖ ≤ (5/4)‖f‖‖g‖`, which still
makes the complete normed space a Banach algebra.

## Encoding questions

The space is encoded by its unique coefficient sequences. Compactness of the
dilation is stated in the sequential form for its unit ball, and the spectrum
uses the usual bounded two-sided-inverse definition, both with the displayed
weighted norm.
-/

open Filter Set

/-- Membership in the weighted `ℓ¹` coefficient space. -/
def apm_m94J02_mem (a : ℕ → ℂ) : Prop :=
  Summable (fun n ↦ ‖a n‖ * ((n : ℝ) ^ 2 + 1))

/-- The norm printed in the problem. -/
noncomputable def apm_m94J02_norm (a : ℕ → ℂ) : ℝ :=
  ∑' n, ‖a n‖ * ((n : ℝ) ^ 2 + 1)

/-- Evaluation of the represented power series. -/
noncomputable def apm_m94J02_eval (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑' n, a n * z ^ n

/-- Cauchy-product coefficients. -/
noncomputable def apm_m94J02_mul (a b : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), a k * b (n - k)

/-- Coefficients of the `m`th pointwise power. -/
noncomputable def apm_m94J02_pow (a : ℕ → ℂ) : ℕ → ℕ → ℂ
  | 0 => fun n ↦ if n = 0 then 1 else 0
  | m + 1 => apm_m94J02_mul (apm_m94J02_pow a m) a

/-- The coefficient action of `Tf(z)=f(z/2)`. -/
noncomputable def apm_m94J02_T (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  (2 : ℂ) ^ (-(n : ℤ)) * a n

/-- Scalars for which `T - λI` has no bounded two-sided inverse on `X`. -/
def apm_m94J02_spectrum : Set ℂ :=
  {z | ¬∃ S : (ℕ → ℂ) → (ℕ → ℂ),
    (∀ a, apm_m94J02_mem a → apm_m94J02_mem (S a)) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ a, apm_m94J02_mem a →
      apm_m94J02_norm (S a) ≤ C * apm_m94J02_norm a) ∧
    (∀ a, apm_m94J02_mem a →
      S (fun n ↦ apm_m94J02_T a n - z * a n) = a) ∧
    (∀ a, apm_m94J02_mem a →
      (fun n ↦ apm_m94J02_T (S a) n - z * (S a) n) = a)}

theorem apm_m94j02 :
    (∀ a : ℕ → ℕ → ℂ,
        (∀ k, apm_m94J02_mem (a k)) →
        (∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
          apm_m94J02_norm (fun k ↦ a m k - a n k) < ε) →
        ∃ b, apm_m94J02_mem b ∧
          ∀ ε > 0, ∃ N, ∀ n ≥ N,
            apm_m94J02_norm (fun k ↦ a n k - b k) < ε) ∧
      (∀ a, apm_m94J02_mem a →
        ContinuousOn (apm_m94J02_eval a) (Metric.closedBall 0 1)) ∧
      (∀ a b, apm_m94J02_mem a → apm_m94J02_mem b →
        apm_m94J02_mem (apm_m94J02_mul a b) ∧
        apm_m94J02_norm (apm_m94J02_mul a b) ≤
          (5 / 4 : ℝ) * apm_m94J02_norm a * apm_m94J02_norm b) ∧
      (∀ a, apm_m94J02_mem a →
        ∃ L : ℝ, Tendsto
          (fun n : ℕ ↦ Real.rpow (apm_m94J02_norm (apm_m94J02_pow a n))
            ((n : ℝ)⁻¹)) atTop (nhds L)) ∧
      (∀ a, apm_m94J02_mem a → apm_m94J02_mem (apm_m94J02_T a)) ∧
      (∀ a : ℕ → ℕ → ℂ,
        (∀ k, apm_m94J02_mem (a k) ∧ apm_m94J02_norm (a k) ≤ 1) →
        ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ b, apm_m94J02_mem b ∧
          Tendsto (fun k ↦ apm_m94J02_norm
            (fun n ↦ apm_m94J02_T (a (σ k)) n - b n)) atTop (nhds 0)) ∧
      apm_m94J02_spectrum =
        {0} ∪ Set.range (fun n : ℕ ↦ (2 : ℂ) ^ (-(n : ℤ))) := by
  sorry
