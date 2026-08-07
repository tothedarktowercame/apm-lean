import Mathlib
import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime

/-! # APM t92J08: complete integral curves of vector fields

## Statement repairs

None.

## Encoding notes

Vector fields and local/global integral curves use Mathlib's genuine tangent
bundle, `IsMIntegralCurveOn`, and `IsMIntegralCurve`. Compactness of a
boundaryless smooth manifold is the sufficient hypothesis. The counterexample
is the actual field `x ↦ x²` on `ℝ`, with solution `t ↦ 1/(1-t)` on `t < 1`.
-/

open Set
open scoped ContDiff Manifold

noncomputable section

abbrev apm_t92J08_E (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev apm_t92J08_Model (n : ℕ) := 𝓘(ℝ, apm_t92J08_E n)

def apm_t92J08_quadraticField (x : ℝ) : TangentSpace (𝓘(ℝ, ℝ)) x :=
  x ^ 2

def apm_t92J08_blowupCurve (t : ℝ) : ℝ :=
  1 / (1 - t)

theorem apm_t92j08 :
    (∀ (n : ℕ) (M : Type)
        [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
        [CompactSpace M] [ChartedSpace (apm_t92J08_E n) M]
        [IsManifold (apm_t92J08_Model n) ∞ M]
        [BoundarylessManifold (apm_t92J08_Model n) M]
        (v : (x : M) → TangentSpace (apm_t92J08_Model n) x),
      ContMDiff (apm_t92J08_Model n) (apm_t92J08_Model n).tangent 1
        (fun x ↦ (⟨x, v x⟩ : TangentBundle (apm_t92J08_Model n) M)) →
      ∀ (a b : ℝ) (γ : ℝ → M), a < 0 → 0 < b →
        IsMIntegralCurveOn γ v (Ioo a b) →
        ∃ δ : ℝ → M,
          IsMIntegralCurve δ v ∧ EqOn γ δ (Ioo a b)) ∧
    IsMIntegralCurveOn apm_t92J08_blowupCurve
      apm_t92J08_quadraticField (Iio 1) ∧
    ¬∃ δ : ℝ → ℝ,
      IsMIntegralCurve δ apm_t92J08_quadraticField ∧
      EqOn apm_t92J08_blowupCurve δ (Iio 1) := by
  sorry
