import Mathlib

/-! # APM b95J03: multiplication from a tensor square

## Statement repairs

None.
-/

open scoped TensorProduct

noncomputable section

/-- Multiplication `E ⊗[F] E → E`. -/
def tensorMultiplication (F E : Type*) [Field F] [Field E] [Algebra F E] :
    E ⊗[F] E →ₗ[F] E :=
  TensorProduct.lift (LinearMap.mul F E)

/-- The map in the problem: multiply the two tensor factors, then let the
result act on `E` by multiplication. -/
def tensorMulRepresentation (F E : Type*) [Field F] [Field E] [Algebra F E] :
    E ⊗[F] E →ₗ[F] Module.End F E :=
  (LinearMap.mul F E).comp (tensorMultiplication F E)

/-- Existence and uniqueness of the specified map, its image and kernel
dimensions in finite degree, and the displayed basis in the `ℂ/ℝ` case. -/
theorem apm_b95j03 :
    (∀ (F E : Type*) [Field F] [Field E] [Algebra F E],
      ∀ φ : E ⊗[F] E →ₗ[F] Module.End F E,
        (∀ a b c : E, φ (a ⊗ₜ[F] b) c = a * b * c) ↔
          φ = tensorMulRepresentation F E) ∧
    (∀ (F E : Type*) [Field F] [Field E] [Algebra F E]
      [FiniteDimensional F E],
      Module.finrank F (tensorMulRepresentation F E).range =
          Module.finrank F E ∧
        Module.finrank F (tensorMulRepresentation F E).ker =
          (Module.finrank F E) ^ 2 - Module.finrank F E) ∧
    (∃ b : Module.Basis (Fin 2) ℝ (tensorMulRepresentation ℝ ℂ).ker,
      (b 0).1 =
          (1 : ℂ) ⊗ₜ[ℝ] (1 : ℂ) + Complex.I ⊗ₜ[ℝ] Complex.I ∧
      (b 1).1 =
          (1 : ℂ) ⊗ₜ[ℝ] Complex.I - Complex.I ⊗ₜ[ℝ] (1 : ℂ)) := by
  sorry
