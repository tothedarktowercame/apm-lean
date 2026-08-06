import Mathlib

/-!
# APM a98A01

## Statement repairs

None.

## Encoding questions

None. The source's `ℝⁿ` is encoded as `EuclideanSpace ℝ (Fin n)` with
Lebesgue measure. Real powers `k^α` use `Real.rpow`. Uniform convergence is
uniform convergence of the functions on the whole Euclidean space; almost
everywhere convergence uses Lebesgue measure; and `L¹` convergence is stated
through the `eLpNorm` at exponent one, which also represents non-integrability
honestly by the value `⊤`.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

/-- The dilation family `Fₖ(x) = k^α f(k|x|)` on the genuine space `ℝⁿ`. -/
def apm_a98a01_dilation {n : ℕ} (f : ℝ → ℝ) (α : ℝ)
    (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.rpow (k : ℝ) α * f ((k : ℝ) * ‖x‖)

theorem apm_a98a01 (n : ℕ) (hn : 0 < n) (f : ℝ → ℝ)
    (hf_cont : ContinuousOn f (Ici (0 : ℝ)))
    (hf_nonneg : ∀ t ∈ Ici (0 : ℝ), 0 ≤ f t)
    (hf_zero : Tendsto (fun t : ℝ => f t / t) (𝓝[>] 0) (𝓝 1))
    (hf_infty : Tendsto (fun t : ℝ => t ^ 4 * f t) atTop (𝓝 1))
    (α : ℝ) :
    (TendstoUniformly
        (fun k => apm_a98a01_dilation (n := n) f α k)
        (fun _ => 0) atTop ↔ α < 0) ∧
    ((∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        Tendsto (fun k => apm_a98a01_dilation f α k x) atTop (𝓝 0)) ↔
      α < 4) ∧
    (Tendsto
        (fun k => eLpNorm (apm_a98a01_dilation (n := n) f α k) 1 volume)
        atTop (𝓝 0) ↔ n ≤ 3 ∧ α < n) := by
  sorry
