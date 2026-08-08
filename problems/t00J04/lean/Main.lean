import Mathlib
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
# APM t00J04 — extending a cotangent vector to a closed one-form

The required global form is exhibited as the manifold differential `df` of a
smooth bump-supported function.  Its value at the chosen point is pinned to
the supplied cotangent vector.  Closedness is stated using the genuine
Euclidean exterior derivative in every manifold chart: the coordinate
one-form is the Fréchet derivative of the chart expression of `f`, and its
exterior derivative vanishes.

## Statement repairs

None.

## Encoding questions

Mathlib provides `extDerivFun f` for the manifold differential of a scalar
function, but no general exterior derivative of manifold one-form sections.
The chartwise predicate below is the standard concrete meaning of `d(df)=0`
using Mathlib's existing `extDeriv` API.
-/

open scoped ContDiff Manifold

noncomputable section

abbrev apm_t00j04_E (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev apm_t00j04_I (n : ℕ) := 𝓘(ℝ, apm_t00j04_E n)

abbrev T00J04OneForm {n : ℕ} (X : Type)
    [TopologicalSpace X] [ChartedSpace (apm_t00j04_E n) X] :=
  (x : X) → TangentSpace (apm_t00j04_I n) x →L[ℝ] ℝ

/-- Chartwise `d(df)=0`, expressed using the actual exterior derivative of
the coordinate one-form. -/
def t00J04DifferentialIsClosed
    {n : ℕ} {X : Type} [TopologicalSpace X]
    [ChartedSpace (apm_t00j04_E n) X]
    (f : X → ℝ) : Prop :=
  ∀ x : X,
    extDeriv
      (fun y : apm_t00j04_E n ↦
        (ContinuousAlternatingMap.ofSubsingleton ℝ (apm_t00j04_E n) ℝ
          (0 : Fin 1))
          (fderiv ℝ (fun z : apm_t00j04_E n ↦
            f ((extChartAt (apm_t00j04_I n) x).symm z)) y))
      (extChartAt (apm_t00j04_I n) x x) = 0

theorem apm_t00j04
    {n : ℕ} (hn : 1 ≤ n)
    {X : Type} [TopologicalSpace X] [T2Space X]
    [SecondCountableTopology X]
    [ChartedSpace (apm_t00j04_E n) X]
    [IsManifold (apm_t00j04_I n) ∞ X]
    (p : X)
    (omega_p : TangentSpace (apm_t00j04_I n) p →L[ℝ] ℝ)
    (homega_p : omega_p ≠ 0) :
    ∃ (f : X → ℝ) (omega : T00J04OneForm (n := n) X),
      ContMDiff (apm_t00j04_I n) 𝓘(ℝ, ℝ) ∞ f ∧
      (∀ x : X, omega x = extDerivFun f x) ∧
      omega p = omega_p ∧
      t00J04DifferentialIsClosed (n := n) f := by
  sorry
