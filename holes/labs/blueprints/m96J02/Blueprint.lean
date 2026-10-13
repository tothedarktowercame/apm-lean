import Mathlib

open MeasureTheory

def apm_m96j02_LocallyLipschitzInSecond (g : ℝ → ℝ → ℝ) : Prop :=
  ∀ R : ℝ, 0 < R →
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ t u v : ℝ,
        |t| ≤ R → |u| ≤ R → |v| ≤ R →
          |g t u - g t v| ≤ L * |u - v|

lemma apm_m96j02_continuousOn_comp_graph
    (g : ℝ → ℝ → ℝ) (hg : Continuous fun p : ℝ × ℝ => g p.1 p.2)
    {T : ℝ} {y : ℝ → ℝ} (hy : ContinuousOn y (Set.Icc 0 T)) :
    ContinuousOn (fun t => g t (y t)) (Set.Icc 0 T) := by
  exact hg.comp_continuousOn (continuousOn_id.prodMk hy)

lemma apm_m96j02_intervalIntegrable_comp_graph
    (g : ℝ → ℝ → ℝ) (hg : Continuous fun p : ℝ × ℝ => g p.1 p.2)
    {T : ℝ} (hT : 0 ≤ T) {y : ℝ → ℝ} (hy : ContinuousOn y (Set.Icc 0 T)) :
    IntervalIntegrable (fun t => g t (y t)) volume 0 T := by
  have hc := apm_m96j02_continuousOn_comp_graph g hg hy
  rw [← Set.uIcc_of_le hT] at hc
  exact hc.intervalIntegrable

/-- Taylor's formula with integral remainder, expressed using the same
within-derivatives as the repaired closed-interval statement. -/
theorem apm_m96j02_ivp_to_volterra
    (g : ℝ → ℝ → ℝ) (hg : Continuous fun p : ℝ × ℝ => g p.1 p.2)
    (α β T : ℝ) (hT : 0 ≤ T) (x : ℝ → ℝ)
    (hx : ContDiffOn ℝ 2 x (Set.Icc 0 T))
    (hx0 : x 0 = α)
    (hxd0 : derivWithin x (Set.Icc 0 T) 0 = β)
    (hxode : ∀ t ∈ Set.Icc (0 : ℝ) T,
      derivWithin (derivWithin x (Set.Icc 0 T)) (Set.Icc 0 T) t =
        g t (x t)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      x t = (∫ s in (0 : ℝ)..t, (t - s) * g s (x s)) + α + β * t := by
  sorry

/-- The a-priori box estimate and contraction argument for two continuous
fixed points of the Volterra operator. -/
theorem apm_m96j02_local_volterra_uniqueness
    (g : ℝ → ℝ → ℝ) (hg : Continuous fun p : ℝ × ℝ => g p.1 p.2)
    (hLip : apm_m96j02_LocallyLipschitzInSecond g)
    (α β : ℝ) :
    ∃ T : ℝ, 0 < T ∧
      ∀ (x y : ℝ → ℝ),
        ContinuousOn x (Set.Icc 0 T) →
        ContinuousOn y (Set.Icc 0 T) →
        (∀ t ∈ Set.Icc (0 : ℝ) T,
          x t = (∫ s in (0 : ℝ)..t, (t - s) * g s (x s)) + α + β * t) →
        (∀ t ∈ Set.Icc (0 : ℝ) T,
          y t = (∫ s in (0 : ℝ)..t, (t - s) * g s (y s)) + α + β * t) →
        ∀ t ∈ Set.Icc (0 : ℝ) T, x t = y t := by
  sorry

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
  obtain ⟨T, hT, huniq⟩ :=
    apm_m96j02_local_volterra_uniqueness g hg hLip α β
  refine ⟨T, hT, ?_⟩
  intro x y hx hx0 hxd0 hxode hy hyvolterra
  exact huniq x y hx.continuousOn hy
    (apm_m96j02_ivp_to_volterra g hg α β T hT.le x hx hx0 hxd0 hxode)
    hyvolterra

#print axioms apm_m96j02
