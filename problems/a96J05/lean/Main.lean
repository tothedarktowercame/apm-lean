import Mathlib

/-!
# APM a96J05 — the sum of two Lp spaces

## Statement repairs

None.

The underlying measure is Lebesgue measure restricted to `[0,1]`.  Membership
in `L^p + L^q` and the infimum norm are represented directly using Mathlib's
`Lp` and `AEEqFun` types.  Completeness is stated by the Cauchy criterion for
this norm, avoiding any surrogate normed-space structure.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

def apm_a96J05_measure : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

def apm_a96J05_mem (p q : ℝ≥0∞)
    (f : AEEqFun ℝ ℝ apm_a96J05_measure) : Prop :=
  ∃ g : Lp ℝ p apm_a96J05_measure,
    ∃ h : Lp ℝ q apm_a96J05_measure,
      (g : AEEqFun ℝ ℝ apm_a96J05_measure) +
        (h : AEEqFun ℝ ℝ apm_a96J05_measure) = f

def apm_a96J05_norm (p q : ℝ≥0∞)
    (f : AEEqFun ℝ ℝ apm_a96J05_measure) : ℝ :=
  sInf {r : ℝ | ∃ g : Lp ℝ p apm_a96J05_measure,
    ∃ h : Lp ℝ q apm_a96J05_measure,
      (g : AEEqFun ℝ ℝ apm_a96J05_measure) +
          (h : AEEqFun ℝ ℝ apm_a96J05_measure) = f ∧
        ‖g‖ + ‖h‖ = r}

theorem apm_a96j05 (p q : ℝ≥0∞) (hp : 1 ≤ p) (hpq : p < q) :
    let X := apm_a96J05_mem p q
    let N := apm_a96J05_norm p q
    -- `X` is a real vector space.
    X 0 ∧
    (∀ f g, X f → X g → X (f + g)) ∧
    (∀ (c : ℝ) f, X f → X (c • f)) ∧
    -- The displayed infimum is a norm on `X`.
    (∀ f, X f → 0 ≤ N f) ∧
    (∀ f, X f → (N f = 0 ↔ f = 0)) ∧
    (∀ (c : ℝ) f, X f → N (c • f) = |c| * N f) ∧
    (∀ f g, X f → X g → N (f + g) ≤ N f + N g) ∧
    -- Every Cauchy sequence in this norm converges in `X`.
    (∀ u : ℕ → AEEqFun ℝ ℝ apm_a96J05_measure,
      (∀ n, X (u n)) →
      (∀ ε > 0, ∃ k, ∀ m ≥ k, ∀ n ≥ k, N (u m - u n) < ε) →
      ∃ f, X f ∧ Tendsto (fun n => N (u n - f)) atTop (nhds 0)) := by
  sorry
