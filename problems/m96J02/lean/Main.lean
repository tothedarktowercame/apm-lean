import Mathlib

open MeasureTheory

/-!
# APM m96J02

## Statement repairs

The printed theorem is false for a merely continuous `g`; for example
`g(t,x)=sqrt |x|` has nonunique solutions at zero. The standard missing
hypothesis, local Lipschitz continuity in the second variable, is added. The
integration variable `dz` in the source is corrected to `ds`, matching the
displayed integrand and the supplied solution.

The source's derivatives on the closed interval are encoded with
`derivWithin` on `Icc 0 T`.  Using global `deriv` together with `ContDiffOn`
made the endpoint conditions vacuous for functions such as `|t|`, because
Mathlib totalizes the nonexistent two-sided derivative there as zero.

## Encoding questions

None.
-/

def apm_m96j02_LocallyLipschitzInSecond (g : ℝ → ℝ → ℝ) : Prop :=
  ∀ R : ℝ, 0 < R →
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ t u v : ℝ,
        |t| ≤ R → |u| ≤ R → |v| ≤ R →
          |g t u - g t v| ≤ L * |u - v|

/-- A continuous trajectory remains a continuous trajectory after applying
the continuous nonlinearity along its graph. -/
lemma apm_m96j02_continuousOn_comp_graph
    (g : ℝ → ℝ → ℝ) (hg : Continuous fun p : ℝ × ℝ => g p.1 p.2)
    {T : ℝ} {y : ℝ → ℝ} (hy : ContinuousOn y (Set.Icc 0 T)) :
    ContinuousOn (fun t => g t (y t)) (Set.Icc 0 T) := by
  exact hg.comp_continuousOn (continuousOn_id.prodMk hy)

/-- Consequently, the nonlinear forcing along a continuous trajectory is
interval-integrable on a nonnegative time interval. -/
lemma apm_m96j02_intervalIntegrable_comp_graph
    (g : ℝ → ℝ → ℝ) (hg : Continuous fun p : ℝ × ℝ => g p.1 p.2)
    {T : ℝ} (hT : 0 ≤ T) {y : ℝ → ℝ} (hy : ContinuousOn y (Set.Icc 0 T)) :
    IntervalIntegrable (fun t => g t (y t)) volume 0 T := by
  have hc := apm_m96j02_continuousOn_comp_graph g hg hy
  rw [← Set.uIcc_of_le hT] at hc
  exact hc.intervalIntegrable

theorem apm_m96j02
    (g : ℝ → ℝ → ℝ) (hg : Continuous fun p : ℝ × ℝ => g p.1 p.2)
    (hLip : apm_m96j02_LocallyLipschitzInSecond g)
    (α β : ℝ) :
    ∃ T : ℝ, 0 < T ∧
      ∀ (x y : ℝ → ℝ),
        ContDiffOn ℝ 2 x (Set.Icc 0 T) →
        x 0 = α → derivWithin x (Set.Icc 0 T) 0 = β →
        (∀ t ∈ Set.Icc (0 : ℝ) T,
          derivWithin (derivWithin x (Set.Icc 0 T)) (Set.Icc 0 T) t =
            g t (x t)) →
        ContinuousOn y (Set.Icc 0 T) →
        (∀ t ∈ Set.Icc (0 : ℝ) T,
          y t = (∫ s in (0 : ℝ)..t, (t - s) * g s (y s)) + α + β * t) →
        ∀ t ∈ Set.Icc (0 : ℝ) T, x t = y t := by
  sorry
