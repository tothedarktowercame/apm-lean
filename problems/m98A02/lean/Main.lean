import Mathlib

/-!
# APM m98A02 — bounded operators and the Neumann inverse

## Statement repairs

Part (b) forms `I-A`, so its operator must have equal domain and codomain.
The initial `A : X → Y` is therefore minimally specialized there to
`A : X → X`; part (a) remains stated for `X → Y`.

Part (b) also assumes `X ≠ {0}` (`[Nontrivial X]`). The printed lower bound
`1/(1+‖A‖) ≤ ‖(I-A)⁻¹‖` fails on the zero space, where `(I-A)⁻¹ = 0`; the
intended proof uses `‖I‖ = 1`, which holds only on a nonzero space.
-/

theorem apm_m98a02 :
    (∀ (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      (A : X →ₗ[ℝ] Y),
      (∃ C ≥ 0, ∀ x, ‖A x‖ ≤ C * ‖x‖) ↔ Continuous A) ∧
    (∀ (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y],
      Nonempty (CompleteSpace (X →L[ℝ] Y))) ∧
    (∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] [Nontrivial X]
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
  · intro X _ _ _ _ A hA
    have hu : IsUnit (1 - A) := isUnit_one_sub_of_norm_lt_one hA
    obtain ⟨u, hu'⟩ := hu
    refine ⟨↑u⁻¹, ?_, ?_, ?_, ?_⟩
    · change (↑u⁻¹ * (1 - A) : X →L[ℝ] X) = 1; rw [← hu']; simp
    · change ((1 - A) * ↑u⁻¹ : X →L[ℝ] X) = 1; rw [← hu']; simp
    · have h1 : (1:ℝ) ≤ ‖(↑u⁻¹ : X →L[ℝ] X)‖ * (1 + ‖A‖) := by
        calc (1:ℝ) = ‖(1 : X →L[ℝ] X)‖ := norm_one.symm
          _ = ‖(↑u⁻¹ : X →L[ℝ] X) * (1 - A)‖ := by rw [← hu']; simp
          _ ≤ ‖(↑u⁻¹ : X →L[ℝ] X)‖ * ‖1 - A‖ := norm_mul_le _ _
          _ ≤ ‖(↑u⁻¹ : X →L[ℝ] X)‖ * (1 + ‖A‖) := by
              gcongr; exact (norm_sub_le _ _).trans (by rw [norm_one])
      rw [div_le_iff₀ (by positivity)]; linarith
    · have hinv : (↑u⁻¹ : X →L[ℝ] X) = Ring.inverse (1 - A) := by
        rw [← hu', Ring.inverse_unit]
      rw [hinv, NormedRing.inverse_one_sub A hA]
      rw [one_div]
      exact tsum_of_norm_bounded (hasSum_geometric_of_lt_one (norm_nonneg _) hA) (fun n => norm_pow_le A n)
