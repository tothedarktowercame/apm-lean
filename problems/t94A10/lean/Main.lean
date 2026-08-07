import Mathlib
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
# APM t94A10 — the solid-angle form on punctured three-space

## Statement repairs

None.

## Encoding questions

Mathlib's exterior derivative is formulated for ambient forms. A form on the
punctured space is extended arbitrarily at the omitted origin and `extDeriv`
is evaluated only at nonzero points; locality makes the value at the origin
irrelevant. Closedness and exactness are thus concrete derivative statements
on the actual punctured space.
-/

noncomputable section

abbrev apm_t94a10_E3 := EuclideanSpace ℝ (Fin 3)
abbrev apm_t94a10_Punctured := {x : apm_t94a10_E3 // x ≠ 0}
abbrev apm_t94a10_Form (k : ℕ) :=
  apm_t94a10_Punctured → apm_t94a10_E3 [⋀^Fin k]→L[ℝ] ℝ

def apm_t94a10_IsOmega (omega : apm_t94a10_Form 2) : Prop :=
  ∀ (x : apm_t94a10_Punctured) (v : Fin 2 → apm_t94a10_E3),
    omega x v =
      (x.1 0 * (v 0 1 * v 1 2 - v 0 2 * v 1 1) -
        x.1 1 * (v 0 0 * v 1 2 - v 0 2 * v 1 0) +
        x.1 2 * (v 0 0 * v 1 1 - v 0 1 * v 1 0)) /
      (Real.sqrt (x.1 0 ^ 2 + x.1 1 ^ 2 + x.1 2 ^ 2)) ^ 3

def apm_t94a10_ambientExtension {k : ℕ}
    (omega : apm_t94a10_Form k) :
    apm_t94a10_E3 → apm_t94a10_E3 [⋀^Fin k]→L[ℝ] ℝ := by
  classical
  exact fun x ↦ if h : x ≠ 0 then omega ⟨x, h⟩ else 0

def apm_t94a10_IsClosed (omega : apm_t94a10_Form 2) : Prop :=
  (∀ x : apm_t94a10_Punctured,
    DifferentiableAt ℝ (apm_t94a10_ambientExtension omega) x.1) ∧
  ∀ x : apm_t94a10_Punctured,
    extDeriv (apm_t94a10_ambientExtension omega) x.1 = 0

def apm_t94a10_IsExact (omega : apm_t94a10_Form 2) : Prop :=
  ∃ eta : apm_t94a10_Form 1,
    (∀ x : apm_t94a10_Punctured,
      DifferentiableAt ℝ (apm_t94a10_ambientExtension eta) x.1) ∧
    ∀ x : apm_t94a10_Punctured,
      extDeriv (apm_t94a10_ambientExtension eta) x.1 = omega x

theorem apm_t94a10 (omega : apm_t94a10_Form 2)
    (homega : apm_t94a10_IsOmega omega) :
    apm_t94a10_IsClosed omega ∧ ¬apm_t94a10_IsExact omega := by
  sorry
