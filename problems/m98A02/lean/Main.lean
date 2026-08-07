import Mathlib

/-!
# APM m98A02 — bounded operators and the Neumann inverse

## Statement repairs

Part (b) forms `I-A`, so its operator must have equal domain and codomain.
The initial `A : X → Y` is therefore minimally specialized there to
`A : X → X`; part (a) remains stated for `X → Y`.
-/

lemma apm_m98a02_trivial_space_obstruction
    (A B : (Fin 0 → ℝ) →L[ℝ] (Fin 0 → ℝ)) :
    ¬ 1 / (1 + ‖A‖) ≤ ‖B‖ := by
  have hA : A = 0 := Subsingleton.elim _ _
  have hB : B = 0 := Subsingleton.elim _ _
  simp [hA, hB]

theorem apm_m98a02 :
    (∀ (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      (A : X →ₗ[ℝ] Y),
      (∃ C ≥ 0, ∀ x, ‖A x‖ ≤ C * ‖x‖) ↔ Continuous A) ∧
    (∀ (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y],
      Nonempty (CompleteSpace (X →L[ℝ] Y))) ∧
    (∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
      (A : X →L[ℝ] X), ‖A‖ < 1 →
      ∃ B : X →L[ℝ] X,
        B.comp (ContinuousLinearMap.id ℝ X - A) = ContinuousLinearMap.id ℝ X ∧
        (ContinuousLinearMap.id ℝ X - A).comp B = ContinuousLinearMap.id ℝ X ∧
        1 / (1 + ‖A‖) ≤ ‖B‖ ∧ ‖B‖ ≤ 1 / (1 - ‖A‖)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro X Y _ _ _ _ A
    constructor
    · rintro ⟨C, hC, hbound⟩
      let Ac : X →L[ℝ] Y := A.mkContinuous C hbound
      simpa only [LinearMap.mkContinuous_apply] using Ac.continuous
    · intro hcont
      let Ac : X →L[ℝ] Y :=
        { toLinearMap := A
          cont := hcont }
      exact ⟨‖Ac‖, norm_nonneg _, fun x ↦ Ac.le_opNorm x⟩
  · intro X Y _ _ _ _ _
    exact ⟨inferInstance⟩
  · /-
    PARTIAL boundary (codex): this final conjunct is false as frozen because
    it does not assume `[Nontrivial X]`.  Take a trivial real normed space
    (for example `X := Fin 0 → ℝ`) and `A = 0`.  Then `‖A‖ < 1`, but
    every `B : X →L[ℝ] X` is zero and has norm zero.  The required lower
    estimate specializes to `1 / (1 + 0) ≤ 0`, i.e. `1 ≤ 0`.
    This contradiction is now formally certified by
    `apm_m98a02_trivial_space_obstruction` above.

    Mathlib's `isUnit_one_sub_of_norm_lt_one`,
    `NormedRing.inverse_one_sub`, and the geometric-series API do prove the
    intended Neumann theorem once `[Nontrivial X]` is added.  Sibling
    `m95A01` demonstrates the same unit construction.  The first two
    conjuncts above are fully proved; this `sorry` is confined to the false
    conjunct, and the frozen statement has not been altered.
    -/
    sorry
