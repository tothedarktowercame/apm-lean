import Mathlib

/-!
# APM m98A03

## Statement repairs

None.

## Encoding notes

`C([0,1])` is Mathlib's genuine Banach space of continuous maps on the
subtype `[0,1]`, equipped with its sup norm.  Lebesgue measure on that subtype
is used directly in the Hammerstein integral.
-/

open MeasureTheory Set

abbrev apm_m98a03_C01 := ContinuousMap (Icc (0 : ℝ) 1) ℝ

def apm_m98a03_IsFrechetDerivativeAtOn
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : Set X) (F : X → Y) (x : X) (A : X →L[ℝ] Y) : Prop :=
  IsOpen U ∧ x ∈ U ∧ HasFDerivWithinAt F A U x

def apm_m98a03_IsHammersteinOperator
    (K : ContinuousMap ((Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1)) ℝ)
    (f : ℝ → ℝ) (F : apm_m98a03_C01 → apm_m98a03_C01) : Prop :=
  ∀ (u : apm_m98a03_C01) (x : Icc (0 : ℝ) 1),
    F u x = ∫ y : Icc (0 : ℝ) 1, K (x, y) * f (u y)

theorem apm_m98a03
    (K : ContinuousMap ((Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1)) ℝ)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
    ∃ (F : apm_m98a03_C01 → apm_m98a03_C01)
      (DF : apm_m98a03_C01 → (apm_m98a03_C01 →L[ℝ] apm_m98a03_C01)),
      apm_m98a03_IsHammersteinOperator K f F ∧
      (∀ u : apm_m98a03_C01,
        HasFDerivAt F (DF u) u ∧
        ∀ (h : apm_m98a03_C01) (x : Icc (0 : ℝ) 1),
          DF u h x = ∫ y : Icc (0 : ℝ) 1,
            K (x, y) * deriv f (u y) * h y) ∧
      Continuous DF := by
  sorry
