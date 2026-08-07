import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue

/-!
# APM a02J04 — a projected planar measure and its Lebesgue decomposition

## Statement repairs

None.

## Encoding questions

None. The planar measure is defined by `Measure.withDensity`, the first-coordinate
pushforward by `Measure.map`, and the Radon–Nikodym derivative by
`Measure.rnDeriv`.
-/

open MeasureTheory Set ENNReal

noncomputable section

def apm_a02J04_g (p : ℝ × ℝ) : ℝ≥0∞ :=
  if 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1 then 2 else 0

def apm_a02J04_mu : Measure (ℝ × ℝ) :=
  volume.withDensity apm_a02J04_g

def apm_a02J04_P : ℝ × ℝ → ℝ := Prod.fst

def apm_a02J04_tau : Measure ℝ :=
  Measure.map apm_a02J04_P apm_a02J04_mu

def apm_a02J04_tauDensity (x : ℝ) : ℝ :=
  if x ∈ Icc 0 1 then 2 * x else 0

theorem apm_a02j04 :
    apm_a02J04_tau =
      volume.withDensity (fun x ↦ ENNReal.ofReal (apm_a02J04_tauDensity x)) ∧
    (volume.restrict (Icc (0 : ℝ) 1)).AbsolutelyContinuous apm_a02J04_tau ∧
    Measure.MutuallySingular (volume.restrict ((Icc (0 : ℝ) 1)ᶜ)) apm_a02J04_tau ∧
    (volume.restrict (Icc (0 : ℝ) 1)).rnDeriv apm_a02J04_tau
      =ᵐ[apm_a02J04_tau]
        fun x ↦ ENNReal.ofReal (1 / (2 * x)) := by
  sorry
