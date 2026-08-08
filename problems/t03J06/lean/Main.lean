import Mathlib
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
# APM t03J06 — a two-form and its bullet-surface integral

## Statement repairs

The hemisphere equation contains `(z - 1)^1`; this is corrected to
`(z - 1)^2`. Exponent `2` is forced by “hemisphere,” the stated center and
radius, and the top point `(0,0,2)`.

The surface integral is defined concretely as the sum of pullback integrals
under outward-oriented parametrizations of the cylinder and upper hemisphere.
-/

open MeasureTheory Set
open scoped Interval

noncomputable section

abbrev apm_t03J06_E3 := EuclideanSpace ℝ (Fin 3)
abbrev apm_t03J06_Form1 :=
  apm_t03J06_E3 → apm_t03J06_E3 [⋀^Fin 1]→L[ℝ] ℝ
abbrev apm_t03J06_Form2 :=
  apm_t03J06_E3 → apm_t03J06_E3 [⋀^Fin 2]→L[ℝ] ℝ

def apm_t03J06_isOmega (omega : apm_t03J06_Form2) : Prop :=
  ∀ (x : apm_t03J06_E3) (v : Fin 2 → apm_t03J06_E3),
    omega x v =
      x 2 * (v 0 0 * v 1 1 - v 0 1 * v 1 0) +
      (x 2 ^ 2 * Real.exp (x 0 * x 2) * Real.log (x 0 ^ 2 + 1) - x 1) *
        (v 0 0 * v 1 2 - v 0 2 * v 1 0) +
      (x 0 + x 1 ^ 2 * x 2 ^ 3 * Real.cos (x 1 ^ 2 + x 2 ^ 2)) *
        (v 0 1 * v 1 2 - v 0 2 * v 1 1)

def apm_t03J06_bullet : Set apm_t03J06_E3 :=
  {x | x 0 ^ 2 + x 1 ^ 2 = 1 ∧ -1 ≤ x 2 ∧ x 2 ≤ 1} ∪
  {x | x 0 ^ 2 + x 1 ^ 2 + (x 2 - 1) ^ 2 = 1 ∧ 1 ≤ x 2}

def apm_t03J06_vec3 (a b c : ℝ) : apm_t03J06_E3 :=
  EuclideanSpace.single 0 a + EuclideanSpace.single 1 b +
    EuclideanSpace.single 2 c

def apm_t03J06_cylinderPoint (θ z : ℝ) : apm_t03J06_E3 :=
  apm_t03J06_vec3 (Real.cos θ) (Real.sin θ) z

def apm_t03J06_cylinderTangents (θ : ℝ) : Fin 2 → apm_t03J06_E3 :=
  fun i ↦ if i = 0 then
    apm_t03J06_vec3 (-Real.sin θ) (Real.cos θ) 0
  else apm_t03J06_vec3 0 0 1

def apm_t03J06_hemispherePoint (p : ℝ × ℝ) : apm_t03J06_E3 :=
  apm_t03J06_vec3 p.1 p.2 (1 + Real.sqrt (1 - p.1 ^ 2 - p.2 ^ 2))

def apm_t03J06_hemisphereTangents (p : ℝ × ℝ) :
    Fin 2 → apm_t03J06_E3 :=
  let s := Real.sqrt (1 - p.1 ^ 2 - p.2 ^ 2)
  fun i ↦ if i = 0 then apm_t03J06_vec3 1 0 (-p.1 / s)
  else apm_t03J06_vec3 0 1 (-p.2 / s)

def apm_t03J06_unitDisk : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2 ^ 2 ≤ 1}

/-- Integral of the pullback to the two oriented parametrization domains. -/
def apm_t03J06_bulletIntegral (omega : apm_t03J06_Form2) : ℝ :=
  (∫ θ in (0 : ℝ)..2 * Real.pi,
    ∫ z in (-1 : ℝ)..1,
      omega (apm_t03J06_cylinderPoint θ z)
        (apm_t03J06_cylinderTangents θ)) +
  ∫ p in apm_t03J06_unitDisk,
    omega (apm_t03J06_hemispherePoint p)
      (apm_t03J06_hemisphereTangents p)

theorem apm_t03j06 (omega : apm_t03J06_Form2)
    (homega : apm_t03J06_isOmega omega) :
    ContDiff ℝ (⊤ : ℕ∞) omega ∧
    (∀ x : apm_t03J06_E3,
      extDeriv omega x (fun i ↦ EuclideanSpace.single i (1 : ℝ)) = 3) ∧
    extDeriv omega ≠ 0 ∧
    ¬(∃ eta : apm_t03J06_Form1,
      ContDiff ℝ (⊤ : ℕ∞) eta ∧ extDeriv eta = omega) ∧
    apm_t03J06_bulletIntegral omega = 7 * Real.pi := by
  sorry
