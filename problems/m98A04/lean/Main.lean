import Mathlib

/-!
# APM m98A04

## Statement repairs

The middle expression in part (a), printed as `∂ᵅ * φ`, is missing its
distribution.  It is repaired to the standard identity
`Dᵅ(T * φ) = (Dᵅ T) * φ = T * (Dᵅ φ)`, matching the surrounding
text and the informal solution.

## Encoding notes

Mathlib's genuine LF-topological `TestFunction` and `Distribution` spaces are
used on `ℝⁿ`.  A multiindex is represented by a list of coordinate indices;
repetition records repeated differentiation and every usual multiindex admits
such a list.  Bundled translated and differentiated test functions are
characterized pointwise, avoiding any replacement of distributions by regular
functions.
-/

open MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions Interval

noncomputable def apm_m98a04_partialList {n : ℕ} :
    List (Fin n) → (EuclideanSpace ℝ (Fin n) → ℝ) →
      EuclideanSpace ℝ (Fin n) → ℝ
  | [], f => f
  | i :: is, f => fun x =>
      fderiv ℝ (apm_m98a04_partialList is f) x (EuclideanSpace.single i 1)

def apm_m98a04_IsConvolution {n : ℕ}
    (T : Distribution (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤)
    (φ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤)
    (h : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∀ x : EuclideanSpace ℝ (Fin n),
    ∀ ψ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤,
      (∀ y, ψ y = φ (x - y)) → h x = T ψ

def apm_m98a04_IsDistributionalPartial {n : ℕ}
    (indices : List (Fin n))
    (T DT : Distribution (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤) : Prop :=
  ∀ ψ dψ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤,
    (∀ x, dψ x = apm_m98a04_partialList indices (ψ : _ → ℝ) x) →
      DT ψ = (-1 : ℝ) ^ indices.length * T dψ

theorem apm_m98a04 :
    (∀ (n : ℕ)
      (T : Distribution (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤)
      (φ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤),
      ∃ h : EuclideanSpace ℝ (Fin n) → ℝ,
        apm_m98a04_IsConvolution T φ h ∧ ContDiff ℝ ∞ h ∧
        ∀ indices : List (Fin n),
          ∃ (DT : Distribution (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤)
            (dφ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin n))) ℝ ⊤)
            (hDT hφ : EuclideanSpace ℝ (Fin n) → ℝ),
            apm_m98a04_IsDistributionalPartial indices T DT ∧
            (∀ x, dφ x = apm_m98a04_partialList indices (φ : _ → ℝ) x) ∧
            apm_m98a04_IsConvolution DT φ hDT ∧
            apm_m98a04_IsConvolution T dφ hφ ∧
            apm_m98a04_partialList indices h = hDT ∧ hDT = hφ) ∧
    (∀ x : ℝ,
      ∫ y in (0 : ℝ)..(2 * Real.pi),
        Real.sin y * Real.cos (x - y) = Real.pi * Real.sin x) := by
  constructor
  · /-
    Boundary: the distributional-convolution clause requires constructing
    translated/reflected bundled `TestFunction`s and proving smooth dependence
    on the translation parameter in Mathlib's LF topology. I searched the
    imported `TestFunction`, `Distribution`, translation, `fderiv`, and
    continuous-linear-map APIs; I did not find an assembled API bridging the
    pointwise witness demanded by `apm_m98a04_IsConvolution` to the required
    bundled smoothness and iterated distributional derivatives. The concrete
    periodic convolution clause is proved below.
    -/
    sorry
  · intro x
    have hintegrand :
        (fun y : ℝ ↦ Real.sin y * Real.cos (x - y)) =
          fun y ↦ Real.cos x * (Real.sin y * Real.cos y) +
            Real.sin x * Real.sin y ^ 2 := by
      funext y
      rw [Real.cos_sub]
      ring
    rw [hintegrand, intervalIntegral.integral_add]
    · rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
      simp
      ring
    · exact (by fun_prop : Continuous fun y : ℝ ↦
        Real.cos x * (Real.sin y * Real.cos y)).intervalIntegrable 0 (2 * Real.pi)
    · exact (by fun_prop : Continuous fun y : ℝ ↦
        Real.sin x * Real.sin y ^ 2).intervalIntegrable 0 (2 * Real.pi)
