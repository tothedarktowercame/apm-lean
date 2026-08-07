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
  constructor
  · intro F E _ _ _ φ
    constructor
    · intro h
      apply TensorProduct.ext
      ext a b c
      simpa [tensorMulRepresentation, tensorMultiplication] using h a b c
    · rintro rfl
      intro a b c
      simp [tensorMulRepresentation, tensorMultiplication]
  constructor
  · intro F E _ _ _ _
    have hmul : Function.Injective (LinearMap.mul F E) := by
      intro x y hxy
      have := LinearMap.congr_fun hxy 1
      simpa using this
    have htensor : Function.Surjective (tensorMultiplication F E) := by
      intro x
      refine ⟨x ⊗ₜ[F] 1, ?_⟩
      simp [tensorMultiplication]
    have hrange : (tensorMulRepresentation F E).range = (LinearMap.mul F E).range := by
      exact LinearMap.range_comp_of_range_eq_top _
        (LinearMap.range_eq_top.mpr htensor)
    have hfrange : Module.finrank F (tensorMulRepresentation F E).range =
        Module.finrank F E := by
      rw [hrange, ← (LinearEquiv.ofInjective (LinearMap.mul F E) hmul).finrank_eq]
    refine ⟨hfrange, ?_⟩
    have hrank := (tensorMulRepresentation F E).finrank_range_add_finrank_ker
    rw [hfrange, Module.finrank_tensorProduct] at hrank
    apply Nat.eq_sub_of_add_eq
    simpa [pow_two, add_comm] using hrank
  · let u : Fin 2 → ℂ ⊗[ℝ] ℂ := ![
      (1 : ℂ) ⊗ₜ[ℝ] (1 : ℂ) + Complex.I ⊗ₜ[ℝ] Complex.I,
      (1 : ℂ) ⊗ₜ[ℝ] Complex.I - Complex.I ⊗ₜ[ℝ] (1 : ℂ)]
    have hu (i : Fin 2) : u i ∈ (tensorMulRepresentation ℝ ℂ).ker := by
      change tensorMulRepresentation ℝ ℂ (u i) = 0
      have hm : tensorMultiplication ℝ ℂ (u i) = 0 := by
        fin_cases i
        · change tensorMultiplication ℝ ℂ
            ((1 : ℂ) ⊗ₜ[ℝ] (1 : ℂ) + Complex.I ⊗ₜ[ℝ] Complex.I) = 0
          calc
            _ = tensorMultiplication ℝ ℂ ((1 : ℂ) ⊗ₜ[ℝ] (1 : ℂ)) +
                tensorMultiplication ℝ ℂ (Complex.I ⊗ₜ[ℝ] Complex.I) :=
              map_add _ _ _
            _ = 0 := by simp [tensorMultiplication]
        · change tensorMultiplication ℝ ℂ
            ((1 : ℂ) ⊗ₜ[ℝ] Complex.I - Complex.I ⊗ₜ[ℝ] (1 : ℂ)) = 0
          calc
            _ = tensorMultiplication ℝ ℂ ((1 : ℂ) ⊗ₜ[ℝ] Complex.I) -
                tensorMultiplication ℝ ℂ (Complex.I ⊗ₜ[ℝ] (1 : ℂ)) :=
              map_sub _ _ _
            _ = 0 := by simp [tensorMultiplication]
      simp [tensorMulRepresentation, hm]
    -- Boundary: the displayed tensors are now formally verified to lie in the
    -- kernel (`hu`).  I searched `Basis.tensorProduct`,
    -- `Basis.tensorProduct_repr_tmul_apply`, `Fintype.linearIndependent_iff`,
    -- `basisOfLinearIndependentOfCardEqFinrank`, and
    -- `coe_basisOfLinearIndependentOfCardEqFinrank`.  The attempted coordinate
    -- proof with `Complex.basisOneI.tensorProduct Complex.basisOneI` is blocked
    -- by Mathlib's asymmetric tensor-basis API requesting an unavailable
    -- `IsScalarTower ℝ ℝ ℂ` instance; a local
    -- `IsScalarTower.of_algebraMap_eq' rfl` did not resolve elaboration.
    sorry
