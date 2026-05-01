import Mathlib

open MeasureTheory Set Filter Topology Real

noncomputable section

/-- The local average of f at scale h. -/
def localAverage (f : ℝ → ℂ) (h : ℝ) (t : ℝ) : ℂ :=
  (1 / (2 * h)) • ∫ x in (t - h)..(t + h), f x

/-- L^p bound: |f_h(t)| ≤ (2h)^{-1/p} * ‖f‖_p, via Hölder's inequality. -/
theorem apm_a97A02_pointwise_bound
    (p : ℝ) (hp : 1 ≤ p)
    (f : ℝ → ℂ)
    (hf_supp : ∀ x, x ∉ Set.Icc (0:ℝ) 1 → f x = 0)
    (hf_mem : MemLp f (ENNReal.ofReal p) volume)
    (h : ℝ) (hh : 0 < h)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ‖localAverage f h t‖ ≤
      (2 * h) ^ (-(1 / p)) * (eLpNorm f (ENNReal.ofReal p) volume).toReal := by sorry

/-- Continuity in t of the averaging operator. -/
theorem apm_a97A02_continuous
    (p : ℝ) (hp : 1 ≤ p)
    (f : ℝ → ℂ)
    (hf_supp : ∀ x, x ∉ Set.Icc (0:ℝ) 1 → f x = 0)
    (hf_mem : MemLp f (ENNReal.ofReal p) volume)
    (h : ℝ) (hh : 0 < h) :
    ContinuousOn (localAverage f h) (Set.Icc 0 1) := by sorry

/-- Helper: the L^q norm of 1_{[t-h,t+h]} where q is conjugate to p. -/
theorem apm_a97A02_indicator_Lq_norm
    (p q : ℝ) (hp : 1 < p) (hpq : 1 / p + 1 / q = 1)
    (t h : ℝ) (hh : 0 < h) :
    (eLpNorm (Set.indicator (Set.Icc (t - h) (t + h)) (fun _ : ℝ => (1:ℂ)))
      (ENNReal.ofReal q) volume).toReal = (2 * h) ^ (1 / q) := by sorry

/-- Helper: the symmetric difference of two intervals shifted by Δt
    has measure ≤ 2|Δt|. -/
theorem apm_a97A02_symm_diff_measure
    (t₁ t₂ h : ℝ) (hh : 0 < h) :
    volume (symmDiff (Set.Icc (t₁ - h) (t₁ + h)) (Set.Icc (t₂ - h) (t₂ + h))) ≤
      ENNReal.ofReal (2 * |t₁ - t₂|) := by sorry

/-- Main theorem: f_h is continuous and pointwise bounded. -/
theorem apm_a97A02_main
    (p : ℝ) (hp : 1 ≤ p)
    (f : ℝ → ℂ)
    (hf_supp : ∀ x, x ∉ Set.Icc (0:ℝ) 1 → f x = 0)
    (hf_mem : MemLp f (ENNReal.ofReal p) volume)
    (h : ℝ) (hh : 0 < h) :
    ContinuousOn (localAverage f h) (Set.Icc 0 1) ∧
    ∀ t ∈ Set.Icc (0:ℝ) 1,
      ‖localAverage f h t‖ ≤
        (2 * h) ^ (-(1 / p)) * (eLpNorm f (ENNReal.ofReal p) volume).toReal := by
  constructor
  · exact apm_a97A02_continuous p hp f hf_supp hf_mem h hh
  · intro t ht
    exact apm_a97A02_pointwise_bound p hp f hf_supp hf_mem h hh t ht
