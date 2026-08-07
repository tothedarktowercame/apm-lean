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

lemma apm_a99J04_zero_mutuallySingular (μ : Measure ℝ) :
    (0 : Measure ℝ) ⟂ₘ μ :=
  Measure.MutuallySingular.zero_left

lemma apm_a99J04_mu3_eq_ac31 :
    apm_a99J04_mu3 =
      apm_a99J04_acPart apm_a99J04_mu1 apm_a99J04_f31 := by
  rfl

lemma apm_a99J04_mu2_eq_ac21 :
    apm_a99J04_mu2 =
      apm_a99J04_acPart apm_a99J04_mu1 apm_a99J04_f21 := by
  have hdensity :
      (fun x : ℝ => ENNReal.ofReal (apm_a99J04_f21 x)) =
        (Ioo 0 1).indicator (fun _ => (1 : ENNReal)) := by
    funext x
    by_cases hx : x ∈ Ioo (0 : ℝ) 1 <;> simp [apm_a99J04_f21, hx]
  rw [apm_a99J04_acPart, hdensity]
  calc
    apm_a99J04_mu2 = apm_a99J04_mu1.restrict (Ioo 0 1) := by
      rw [apm_a99J04_mu1, apm_a99J04_mu2,
        Measure.restrict_restrict measurableSet_Ioo]
      congr 1
      ext x
      simp only [mem_inter_iff, mem_Ioo, apm_a99J04_interval, mem_Icc]
      constructor
      · intro h
        exact ⟨h, ⟨by linarith [h.1], by linarith [h.2]⟩⟩
      · exact fun h => h.1
    _ = apm_a99J04_mu1.withDensity
        ((Ioo 0 1).indicator (fun _ => (1 : ENNReal))) :=
      (withDensity_indicator_one measurableSet_Ioo).symm

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
  /-
  PARTIAL boundary (closer hop 1): the forward density computations
  `μ₃ = x² • μ₁` and `μ₂ = 1_(0,1) • μ₁` are now proved above as
  `apm_a99J04_mu3_eq_ac31` and `apm_a99J04_mu2_eq_ac21`.  The latter uses
  Mathlib's `withDensity_indicator_one` and `Measure.restrict_restrict`, with
  the elementary inclusion `(0,1) ⊆ [-2,2]` discharged explicitly.  The four
  singular remainders that are literally zero can all use
  `apm_a99J04_zero_mutuallySingular`.

  The remaining boundary is (1) proving the two reciprocal cancellations
  `ofReal (1/x²) * ofReal (x²) = 1` away from the null singleton `{0}` under
  `withDensity_withDensity`, and (2) splitting `μ₁` and `μ₃` over `(0,1)` and
  its complement, then proving the complementary restrictions mutually
  singular.  Searches of the lemma index and prior artifacts found no helper
  specialized to these six measures; Mathlib's generic with-density and
  restriction APIs reduce the task to these pointwise/a.e. identities.
  -/
  sorry
