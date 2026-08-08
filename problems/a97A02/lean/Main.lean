import Mathlib

/-!
# APM a97A02 — continuity and bounds for sliding averages

## Statement repairs

None.

## Encoding questions

An `L^p([0,1])` function is represented by a measurable representative on
`ℝ` with `MemLp` for Lebesgue measure restricted to `Icc 0 1`. Consequently
the integral over `[t-h,t+h]` automatically uses the zero extension outside
`[0,1]`. The norm is Mathlib's `snorm` of that representative.
-/

open MeasureTheory Set

noncomputable section

def apm_a97A02_measure : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

def apm_a97A02_average (f : ℝ → ℂ) (h t : ℝ) : ℂ :=
  (∫ x in Set.Icc (t - h) (t + h), f x ∂apm_a97A02_measure) / (2 * h)

lemma apm_a97A02_integrable_of_memLp
    {p : ENNReal} (hp : 1 ≤ p) {f : ℝ → ℂ}
    (hf : MemLp f p apm_a97A02_measure) :
    Integrable f apm_a97A02_measure := by
  letI : IsFiniteMeasure apm_a97A02_measure := by
    unfold apm_a97A02_measure
    infer_instance
  exact hf.integrable hp

lemma apm_a97A02_measure_Icc_le (h t : ℝ) (_hh : 0 < h) :
    apm_a97A02_measure (Set.Icc (t - h) (t + h)) ≤ ENNReal.ofReal (2 * h) := by
  calc
    apm_a97A02_measure (Set.Icc (t - h) (t + h))
        ≤ volume (Set.Icc (t - h) (t + h)) :=
      Measure.restrict_le_self
        (Set.Icc (t - h) (t + h))
    _ = ENNReal.ofReal (2 * h) := by
      rw [Real.volume_Icc]
      congr 1
      linarith

theorem apm_a97a02
    (p : ENNReal) (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    (f : ℝ → ℂ) (hf : MemLp f p apm_a97A02_measure)
    (h : ℝ) (hh : 0 < h) :
    ContinuousOn (apm_a97A02_average f h) (Set.Icc (0 : ℝ) 1) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖apm_a97A02_average f h t‖ ≤
        (2 * h) ^ (-(1 / p.toReal)) *
          (eLpNorm f p apm_a97A02_measure).toReal := by
  /- CLOSER HOP 1 BOUNDARY.

  The helpers above close two prerequisites hidden in the original goal:
  `MemLp.integrable` applies because the restricted unit-interval measure is
  finite, and every moving interval has measure at most `2*h` by
  `Measure.restrict_le_self` and `Real.volume_Icc`.

  The norm estimate now reduces to the finite-measure `Lᵖ ⊆ L¹` inequality
  on the restricted moving interval, followed by the compiled measure bound
  and division by `2*h`.  The continuity clause reduces to continuity of the
  indefinite integral of an integrable function for the atomless measure
  `volume.restrict (Icc 0 1)`, applied at the two continuous endpoints
  `t-h` and `t+h`.  Searches of Mathlib's interval-integral, `eLpNorm`,
  indicator, and Bochner-integral APIs found the constituent results but no
  theorem already combining arbitrary `ENNReal` exponent conversion with this
  set-integral encoding.  No solved sibling or `ConstructionTargets` module
  packages that conversion.  The frozen statement is unchanged.
  -/
  sorry
