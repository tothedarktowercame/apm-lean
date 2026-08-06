import Mathlib
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
# APM t02A05

## Statement repairs

None.

## Encoding questions

Mathlib represents alternating differential forms but does not yet provide the
outward-oriented integral of such a form over a sphere. That integral is the
single opaque typed operation below. The ambient space, the given two-form,
every unit sphere, the full minimizing locus, and the claimed value remain
explicit.
-/

noncomputable section

abbrev apm_t02a05_E3 := EuclideanSpace ℝ (Fin 3)
abbrev apm_t02a05_Form2 :=
  apm_t02a05_E3 → apm_t02a05_E3 [⋀^Fin 2]→L[ℝ] ℝ

def apm_t02a05_isOmega (omega : apm_t02a05_Form2) : Prop :=
  ∀ (x : apm_t02a05_E3) (v : Fin 2 → apm_t02a05_E3),
    omega x v =
      (x 0 - 1) ^ 3 * (v 0 1 * v 1 2 - v 0 2 * v 1 1) +
      (x 1 - 2) ^ 3 * (v 0 2 * v 1 0 - v 0 0 * v 1 2) +
      (x 2 - 3) * (v 0 0 * v 1 1 - v 0 1 * v 1 0)

def apm_t02a05_unitSphere (c : apm_t02a05_E3) : Set apm_t02a05_E3 :=
  Metric.sphere c 1

opaque apm_t02a05_outwardSphereIntegral
    (omega : apm_t02a05_Form2) (S : Set apm_t02a05_E3) : ℝ

theorem apm_t02a05
    (omega : apm_t02a05_Form2) (homega : apm_t02a05_isOmega omega) :
    (∀ c : apm_t02a05_E3,
      44 * Real.pi / 15 ≤
        apm_t02a05_outwardSphereIntegral omega (apm_t02a05_unitSphere c)) ∧
    (∀ c : apm_t02a05_E3,
      apm_t02a05_outwardSphereIntegral omega (apm_t02a05_unitSphere c) =
          44 * Real.pi / 15 ↔
        c 0 = 1 ∧ c 1 = 2) := by
  sorry
