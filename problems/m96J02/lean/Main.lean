import Mathlib

/-!
# APM m96J02

## Statement repairs

The printed theorem is false for a merely continuous `g`; for example
`g(t,x)=sqrt |x|` has nonunique solutions at zero. The standard missing
hypothesis, local Lipschitz continuity in the second variable, is added. The
integration variable `dz` in the source is corrected to `ds`, matching the
displayed integrand and the supplied solution.

## Encoding questions

None.
-/

def apm_m96j02_LocallyLipschitzInSecond (g : ℝ → ℝ → ℝ) : Prop :=
  ∀ R : ℝ, 0 < R →
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ t u v : ℝ,
        |t| ≤ R → |u| ≤ R → |v| ≤ R →
          |g t u - g t v| ≤ L * |u - v|

theorem apm_m96j02
    (g : ℝ → ℝ → ℝ) (hg : Continuous fun p : ℝ × ℝ => g p.1 p.2)
    (hLip : apm_m96j02_LocallyLipschitzInSecond g)
    (α β : ℝ) :
    ∃ T : ℝ, 0 < T ∧
      ∀ (x y : ℝ → ℝ),
        ContDiffOn ℝ 2 x (Set.Icc 0 T) →
        x 0 = α → deriv x 0 = β →
        (∀ t ∈ Set.Icc (0 : ℝ) T, deriv (deriv x) t = g t (x t)) →
        ContinuousOn y (Set.Icc 0 T) →
        (∀ t ∈ Set.Icc (0 : ℝ) T,
          y t = (∫ s in (0 : ℝ)..t, (t - s) * g s (y s)) + α + β * t) →
        ∀ t ∈ Set.Icc (0 : ℝ) T, x t = y t := by
  sorry
