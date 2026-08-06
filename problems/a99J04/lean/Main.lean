import Mathlib

/-!
# APM a99J04: Six Lebesgue decompositions on `[-2,2]`

## Statement repairs

None.

## Encoding questions

None. All measures are defined on `ℝ` and restricted to the source interval.
Each absolutely continuous part is expressed with `Measure.withDensity`; the
real-valued functions below are converted to nonnegative extended reals.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

def apm_a99J04_interval : Set ℝ := Icc (-2) 2

def apm_a99J04_mu1 : Measure ℝ :=
  volume.restrict apm_a99J04_interval

def apm_a99J04_mu2 : Measure ℝ :=
  volume.restrict (Ioo 0 1)

def apm_a99J04_mu3 : Measure ℝ :=
  apm_a99J04_mu1.withDensity (fun x ↦ ENNReal.ofReal (x ^ 2))

/-- Turn a real-valued Radon–Nikodym derivative into a measure density. -/
def apm_a99J04_acPart (μ : Measure ℝ) (f : ℝ → ℝ) : Measure ℝ :=
  μ.withDensity (fun x ↦ ENNReal.ofReal (f x))

def apm_a99J04_f21 (x : ℝ) : ℝ := (Ioo 0 1).indicator (fun _ ↦ 1) x
def apm_a99J04_f31 (x : ℝ) : ℝ := x ^ 2
def apm_a99J04_f13 (x : ℝ) : ℝ := if x = 0 then 0 else 1 / x ^ 2
def apm_a99J04_f23 (x : ℝ) : ℝ :=
  (Ioo 0 1).indicator (fun y ↦ 1 / y ^ 2) x
def apm_a99J04_f12 (_x : ℝ) : ℝ := 1
def apm_a99J04_f32 (x : ℝ) : ℝ := x ^ 2

def apm_a99J04_nu12 : Measure ℝ :=
  apm_a99J04_mu1.restrict (Ioo 0 1)ᶜ

def apm_a99J04_nu32 : Measure ℝ :=
  apm_a99J04_mu3.restrict (Ioo 0 1)ᶜ

theorem apm_a99j04 :
    apm_a99J04_mu2 =
        apm_a99J04_acPart apm_a99J04_mu1 apm_a99J04_f21 + 0 ∧
      (0 : Measure ℝ) ⟂ₘ apm_a99J04_mu1 ∧
    apm_a99J04_mu3 =
        apm_a99J04_acPart apm_a99J04_mu1 apm_a99J04_f31 + 0 ∧
      (0 : Measure ℝ) ⟂ₘ apm_a99J04_mu1 ∧
    apm_a99J04_mu1 =
        apm_a99J04_acPart apm_a99J04_mu3 apm_a99J04_f13 + 0 ∧
      (0 : Measure ℝ) ⟂ₘ apm_a99J04_mu3 ∧
    apm_a99J04_mu2 =
        apm_a99J04_acPart apm_a99J04_mu3 apm_a99J04_f23 + 0 ∧
      (0 : Measure ℝ) ⟂ₘ apm_a99J04_mu3 ∧
    apm_a99J04_mu1 =
        apm_a99J04_acPart apm_a99J04_mu2 apm_a99J04_f12 +
          apm_a99J04_nu12 ∧
      apm_a99J04_nu12 ⟂ₘ apm_a99J04_mu2 ∧
    apm_a99J04_mu3 =
        apm_a99J04_acPart apm_a99J04_mu2 apm_a99J04_f32 +
          apm_a99J04_nu32 ∧
      apm_a99J04_nu32 ⟂ₘ apm_a99J04_mu2 := by
  sorry
