import Mathlib

/-!
# APM m98A06

## Statement repairs

The preamble says `y ∈ C¹([0,1])`, but the functional integrates to `a`
and parts (a)–(b) impose a boundary value at `a`.  The domain is minimally
repaired to `C¹([0,a])`.

## Encoding notes

Stationary extremals are defined by vanishing first variation against all
endpoint-zero `C¹` variations.  Genuine global extrema are stated separately.
For the Poincaré clause, `H¹₀(0,π)` is represented by an `L²` function and
its `L²` weak derivative, using the continuous trace-zero representative.
-/

open MeasureTheory Set
open scoped ContDiff ENNReal Interval

noncomputable def apm_m98a06_I (a : ℝ) (y : ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..a, (deriv y x) ^ 2 - (y x) ^ 2

def apm_m98a06_Admissible (a y₀ ya : ℝ) (y : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 1 y (Icc 0 a) ∧ y 0 = y₀ ∧ y a = ya

def apm_m98a06_IsStationary (a y₀ ya : ℝ) (y : ℝ → ℝ) : Prop :=
  apm_m98a06_Admissible a y₀ ya y ∧
  ∀ η : ℝ → ℝ, ContDiffOn ℝ 1 η (Icc 0 a) → η 0 = 0 → η a = 0 →
    ∫ x in (0 : ℝ)..a, 2 * (deriv y x * deriv η x - y x * η x) = 0

def apm_m98a06_IsWeakDerivativeOn
    (s : Set ℝ) (u du : ℝ → ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    Function.support φ ⊆ s →
      ∫ x, u x * deriv φ x ∂(volume.restrict s) =
        -∫ x, du x * φ x ∂(volume.restrict s)

def apm_m98a06_InH10Pi (u du : ℝ → ℝ) : Prop :=
  ContinuousOn u (Icc 0 Real.pi) ∧ u 0 = 0 ∧ u Real.pi = 0 ∧
  MemLp u 2 (volume.restrict (Ioo 0 Real.pi)) ∧
  MemLp du 2 (volume.restrict (Ioo 0 Real.pi)) ∧
  apm_m98a06_IsWeakDerivativeOn (Ioo 0 Real.pi) u du

lemma apm_m98a06_nonresonant_candidate_admissible
    {a : ℝ} (ha : Real.sin a ≠ 0) :
    apm_m98a06_Admissible a 0 1
      (fun x ↦ Real.sin x / Real.sin a) := by
  refine ⟨?_, by simp, ?_⟩
  · fun_prop
  · exact div_self ha

/-- The frozen nonresonance hypothesis is exactly the standard characterization
of the nonzero set of the real sine function. -/
lemma apm_m98a06_sin_ne_zero_of_nonresonant {a : ℝ}
    (ha : ∀ k : ℤ, a ≠ k * Real.pi) : Real.sin a ≠ 0 := by
  rw [Real.sin_ne_zero_iff]
  intro k hk
  exact ha k hk.symm

private lemma apm_m98a06_deriv_sin_half (x : ℝ) :
    deriv (fun t : ℝ ↦ Real.sin (t / 2)) x = Real.cos (x / 2) / 2 := by
  have hinner : HasDerivAt (fun t : ℝ ↦ t / 2) (1 / 2) x :=
    (hasDerivAt_id x).div_const 2
  convert ((Real.hasDerivAt_sin (x / 2)).comp x hinner).deriv using 1 <;> ring

lemma apm_m98a06_negativeMode_admissible :
    apm_m98a06_Admissible (2 * Real.pi) 0 0
      (fun x : ℝ ↦ Real.sin (x / 2)) := by
  refine ⟨by fun_prop, by simp, ?_⟩
  convert Real.sin_pi using 1 <;> ring

lemma apm_m98a06_negativeMode_energy :
    apm_m98a06_I (2 * Real.pi) (fun x : ℝ ↦ Real.sin (x / 2)) =
      -(3 * Real.pi / 4) := by
  simp_rw [apm_m98a06_I, apm_m98a06_deriv_sin_half]
  rw [intervalIntegral.integral_sub]
  · rw [show (fun x : ℝ ↦ (Real.cos (x / 2) / 2) ^ 2) =
        fun x ↦ (1 / 4 : ℝ) * (Real.cos (x / 2)) ^ 2 by funext x; ring]
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_comp_div (fun x : ℝ ↦ Real.cos x ^ 2)
      (by norm_num : (2 : ℝ) ≠ 0)]
    rw [intervalIntegral.integral_comp_div (fun x : ℝ ↦ Real.sin x ^ 2)
      (by norm_num : (2 : ℝ) ≠ 0)]
    simp
    ring
  · exact (by fun_prop : Continuous fun x : ℝ ↦
      (Real.cos (x / 2) / 2) ^ 2).intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun x : ℝ ↦
      Real.sin (x / 2) ^ 2).intervalIntegrable _ _

theorem apm_m98a06 :
    ((∀ y : ℝ → ℝ,
        apm_m98a06_IsStationary (2 * Real.pi) 1 1 y ↔
          ∃ B : ℝ, ∀ x ∈ Icc (0 : ℝ) (2 * Real.pi),
            y x = Real.cos x + B * Real.sin x) ∧
      (∀ y : ℝ → ℝ, apm_m98a06_Admissible (2 * Real.pi) 1 1 y →
        (∃ z : ℝ → ℝ, apm_m98a06_Admissible (2 * Real.pi) 1 1 z ∧
          apm_m98a06_I (2 * Real.pi) z < apm_m98a06_I (2 * Real.pi) y) ∧
        ∃ z : ℝ → ℝ, apm_m98a06_Admissible (2 * Real.pi) 1 1 z ∧
          apm_m98a06_I (2 * Real.pi) y < apm_m98a06_I (2 * Real.pi) z)) ∧
    (∀ a : ℝ, 0 < a → (∀ k : ℤ, a ≠ k * Real.pi) →
      (∀ y : ℝ → ℝ, apm_m98a06_IsStationary a 0 1 y ↔
        ∀ x ∈ Icc (0 : ℝ) a, y x = Real.sin x / Real.sin a) ∧
      (a < Real.pi →
        ∀ z : ℝ → ℝ, apm_m98a06_Admissible a 0 1 z →
          apm_m98a06_I a (fun x ↦ Real.sin x / Real.sin a) ≤ apm_m98a06_I a z) ∧
      (Real.pi < a → ∀ y : ℝ → ℝ, apm_m98a06_Admissible a 0 1 y →
        (∃ z : ℝ → ℝ, apm_m98a06_Admissible a 0 1 z ∧
          apm_m98a06_I a z < apm_m98a06_I a y) ∧
        ∃ z : ℝ → ℝ, apm_m98a06_Admissible a 0 1 z ∧
          apm_m98a06_I a y < apm_m98a06_I a z)) ∧
    ((∀ y dy : ℝ → ℝ, apm_m98a06_InH10Pi y dy →
        ∫ x, (y x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 1 →
        0 ≤ ∫ x, (dy x) ^ 2 - (y x) ^ 2
          ∂(volume.restrict (Ioo (0 : ℝ) Real.pi))) ∧
      (∀ y dy : ℝ → ℝ, apm_m98a06_InH10Pi y dy →
        ∫ x, (y x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 1 →
        (∫ x, (dy x) ^ 2 - (y x) ^ 2
          ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 0 ↔
          ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
            y =ᵐ[volume.restrict (Ioo (0 : ℝ) Real.pi)]
              fun x ↦ s * Real.sqrt (2 / Real.pi) * Real.sin x)) ∧
      (∀ M : ℝ, ∃ y dy : ℝ → ℝ, apm_m98a06_InH10Pi y dy ∧
        ∫ x, (y x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) = 1 ∧
        M < ∫ x, (dy x) ^ 2 - (y x) ^ 2
          ∂(volume.restrict (Ioo (0 : ℝ) Real.pi))) ∧
      IsLeast {C : ℝ | ∀ f df : ℝ → ℝ, apm_m98a06_InH10Pi f df →
        ∫ x, (f x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi)) ≤
          C * ∫ x, (df x) ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) Real.pi))} 1) := by
  have hfamily_admissible (B : ℝ) :
      apm_m98a06_Admissible (2 * Real.pi) 1 1
        (fun x ↦ Real.cos x + B * Real.sin x) := by
    refine ⟨?_, by simp, ?_⟩
    · fun_prop
    · simp
  /-
  PARTIAL boundary (closer hop 2): the resonant family appearing in part (a) has been checked
  above to satisfy the frozen `C¹` endpoint encoding. The nonresonant candidate
  from part (b) is now also certified by
  `apm_m98a06_nonresonant_candidate_admissible` whenever `sin a ≠ 0`.
  This hop closes the exact conversion from the theorem's quantified
  nonresonance assumption to that side condition in
  `apm_m98a06_sin_ne_zero_of_nonresonant`, using Mathlib's
  `Real.sin_ne_zero_iff`.

  This hop also formalizes the explicit negative mode `sin (x/2)` on
  `[0, 2π]`: `apm_m98a06_negativeMode_admissible` proves its endpoint and
  regularity conditions, while `apm_m98a06_negativeMode_energy` evaluates its
  energy exactly as `-3π/4`, using Mathlib's change-of-variables and squared
  trigonometric integral formulas. Thus the negative direction itself is no
  longer part of the boundary.

  Completing the theorem requires an Euler--Lagrange fundamental lemma for
  `ContDiffOn` variations, the corresponding cross-term cancellation for
  arbitrary stationary/admissible functions, positive-direction constructions,
  and the sharp one-dimensional
  Poincaré/Wirtinger theorem for the custom weak-derivative predicate
  `apm_m98a06_InH10Pi` (including its equality case and optimality). I searched
  Mathlib's interval integration-by-parts, weak-derivative, Sobolev, and
  Poincaré APIs, all closed artifacts (including `m02J02`, `m01J06`, and
  `m97A06`), `ConstructionTargets`, and `YoungL2.lean`; no compiled sibling or
  library assembled these results for this bespoke representation. A further
  Mathlib search did find the exact classical integral formulas
  `intervalIntegral.integral_sin_sq`, `integral_cos_sq`,
  `integral_sin_mul_cos₁`, and `integral_comp_div`; the first, second, and
  fourth are used above for the negative-mode calculation, but they do not
  provide the cross-term cancellation for an arbitrary merely
  `ContDiffOn ℝ 1` admissible function. The blocker remains the fundamental
  lemma/integration-by-parts bridge and the sharp weak Poincaré theorem.
  -/
  sorry
