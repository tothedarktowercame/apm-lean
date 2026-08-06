import Mathlib
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
# APM t94A10 — the solid-angle form on punctured three-space

## Statement repairs

None.

## Encoding questions

Mathlib's exterior derivative is presently formulated for ambient forms, not
intrinsic forms on the open manifold `ℝ³ \ {0}` together with its de Rham
exactness relation.  Closedness and exactness on that domain are therefore
typed placeholders.  The punctured space and the given two-form itself remain
fully explicit.
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

def apm_t94a10_IsClosed (_omega : apm_t94a10_Form 2) : Prop := by
  sorry

def apm_t94a10_IsExact (_omega : apm_t94a10_Form 2) : Prop := by
  sorry

theorem apm_t94a10 (omega : apm_t94a10_Form 2)
    (homega : apm_t94a10_IsOmega omega) :
    apm_t94a10_IsClosed omega ∧ ¬apm_t94a10_IsExact omega := by
  sorry
