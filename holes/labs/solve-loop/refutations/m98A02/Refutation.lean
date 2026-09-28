import Mathlib

lemma apm_m98a02_trivial_space_obstruction
    (A B : (Fin 0 → ℝ) →L[ℝ] (Fin 0 → ℝ)) :
    ¬ 1 / (1 + ‖A‖) ≤ ‖B‖ := by
  have hA : A = 0 := Subsingleton.elim _ _
  have hB : B = 0 := Subsingleton.elim _ _
  simp [hA, hB]

theorem apm_m98a02_refutation :
    ¬ ((∀ (X Y : Type) [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      (A : X →ₗ[ℝ] Y),
      (∃ C ≥ 0, ∀ x, ‖A x‖ ≤ C * ‖x‖) ↔ Continuous A) ∧
    (∀ (X Y : Type) [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y],
      Nonempty (CompleteSpace (X →L[ℝ] Y))) ∧
    (∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
      (A : X →L[ℝ] X), ‖A‖ < 1 →
      ∃ B : X →L[ℝ] X,
        B.comp (ContinuousLinearMap.id ℝ X - A) = ContinuousLinearMap.id ℝ X ∧
        (ContinuousLinearMap.id ℝ X - A).comp B = ContinuousLinearMap.id ℝ X ∧
        1 / (1 + ‖A‖) ≤ ‖B‖ ∧ ‖B‖ ≤ 1 / (1 - ‖A‖))) := by
  intro h
  let X := Fin 0 → ℝ
  let A : X →L[ℝ] X := 0
  have hnorm : ‖A‖ < 1 := by simp [A]
  obtain ⟨B, _hleft, _hright, hlower, _hupper⟩ := h.2.2 X A hnorm
  exact apm_m98a02_trivial_space_obstruction A B hlower
