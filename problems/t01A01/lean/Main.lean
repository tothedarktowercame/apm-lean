import Mathlib

/-!
# APM t01A01

## Statement repairs

None.

## Encoding questions

The real projective plane is encoded as the actual projectivization of `ℝ³`
with quotient topology. Triviality of the induced fundamental-group map is
stated at every basepoint; its codomain is based at `f x`, as required for a
not-necessarily-basepoint-preserving map.
-/

open scoped LinearAlgebra.Projectivization

abbrev apm_t01A01_RP2 := Projectivization ℝ (Fin 3 → ℝ)

noncomputable instance : TopologicalSpace apm_t01A01_RP2 :=
  inferInstanceAs
    (TopologicalSpace
      (Quotient (projectivizationSetoid ℝ (Fin 3 → ℝ))))

theorem apm_t01a01 :
    ∀ f : C(apm_t01A01_RP2, apm_t01A01_RP2),
      ¬Function.Surjective f →
      (∀ (x : apm_t01A01_RP2) (γ : FundamentalGroup apm_t01A01_RP2 x),
        FundamentalGroup.map f x γ = 1) ∧
      ∃ p : apm_t01A01_RP2,
        ContinuousMap.Homotopic f (ContinuousMap.const _ p) := by
  sorry
