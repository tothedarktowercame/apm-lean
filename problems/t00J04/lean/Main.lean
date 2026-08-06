import Mathlib

/-!
# APM t00J04

## Statement repairs

None.

## Encoding questions

The manifold, its tangent spaces, the prescribed covector, and the global
dependent field of covectors are represented directly.  Mathlib has tangent
bundles and manifold derivatives but no packaged exterior derivative on
differential forms, so smoothness, closedness, and exactness of this genuine
dependent one-form are isolated as typed predicates.
-/

open scoped ContDiff Manifold

noncomputable section

abbrev apm_t00J04_E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A real one-form on an `n`-dimensional smooth manifold. -/
abbrev apm_t00J04_OneForm
    (n : ℕ) (X : Type*) [TopologicalSpace X]
    [ChartedSpace (apm_t00J04_E n) X] :=
  (x : X) → TangentSpace (𝓘(ℝ, apm_t00J04_E n)) x →L[ℝ] ℝ

/-- Smoothness of a section of the cotangent bundle. -/
opaque apm_t00J04_IsSmoothOneForm
    {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (apm_t00J04_E n) X]
    (eta : apm_t00J04_OneForm n X) : Prop

/-- Vanishing exterior derivative of a smooth one-form. -/
opaque apm_t00J04_IsClosedOneForm
    {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (apm_t00J04_E n) X]
    (eta : apm_t00J04_OneForm n X) : Prop

/-- A one-form is the manifold differential of a global smooth function. -/
opaque apm_t00J04_IsExactOneForm
    {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (apm_t00J04_E n) X]
    (eta : apm_t00J04_OneForm n X) : Prop

theorem apm_t00j04
    {n : ℕ} (hn : 1 ≤ n)
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace (apm_t00J04_E n) X]
    [IsManifold (𝓘(ℝ, apm_t00J04_E n)) ∞ X]
    (p : X)
    (eta_p : TangentSpace (𝓘(ℝ, apm_t00J04_E n)) p →L[ℝ] ℝ)
    (heta_p : eta_p ≠ 0) :
    (∃ eta : apm_t00J04_OneForm n X,
      apm_t00J04_IsSmoothOneForm eta ∧ eta p = eta_p) ∧
    ∃ eta : apm_t00J04_OneForm n X,
      apm_t00J04_IsSmoothOneForm eta ∧
      apm_t00J04_IsClosedOneForm eta ∧
      apm_t00J04_IsExactOneForm eta ∧
      eta p = eta_p := by
  sorry
