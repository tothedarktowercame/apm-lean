import Mathlib

/-!
# APM m98A01 — Banach/Hilbert foundations and closed graphs

## Statement repairs

None.

## Encoding note

Mathlib's structures `NormedSpace`, `CompleteSpace`, and `InnerProductSpace`
are the requested definitions. The example is the actual sup-norm space of
continuous functions on `[0,1]`, not a finite-dimensional surrogate.
-/

abbrev apm_m98a01_C01 := ContinuousMap (Set.Icc (0 : ℝ) 1) ℝ

theorem apm_m98a01 :
    Nonempty (CompleteSpace apm_m98a01_C01) ∧
    (∃ f g : apm_m98a01_C01,
      ‖f + g‖ ^ 2 + ‖f - g‖ ^ 2 ≠ 2 * ‖f‖ ^ 2 + 2 * ‖g‖ ^ 2) ∧
    (∀ (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
      (T : X →L[ℝ] Y), Function.Surjective T → IsOpenMap T) ∧
    (∀ (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
      [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
      (T : X →ₗ[ℝ] Y),
      IsClosed {p : X × Y | p.2 = T p.1} → Continuous T) := by
  refine ⟨⟨inferInstance⟩, ?_, ?_, ?_⟩
  · let f : apm_m98a01_C01 := ContinuousMap.const _ 1
    let g : apm_m98a01_C01 :=
      ⟨fun x => x.1, continuous_subtype_val⟩
    have hf : ‖f‖ = 1 := by simp [f]
    have hg : ‖g‖ = 1 := by
      apply le_antisymm
      · rw [ContinuousMap.norm_le_of_nonempty]
        intro x
        change |(x : ℝ)| ≤ 1
        exact abs_le.mpr ⟨by linarith [x.2.1], by linarith [x.2.2]⟩
      · have h := ContinuousMap.norm_coe_le_norm g ⟨1, by constructor <;> norm_num⟩
        simpa [g] using h
    have hfg : ‖f + g‖ = 2 := by
      apply le_antisymm
      · rw [ContinuousMap.norm_le_of_nonempty]
        intro x
        change |1 + (x : ℝ)| ≤ 2
        rw [abs_of_nonneg (by linarith [x.2.1])]
        linarith [x.2.2]
      · have h := ContinuousMap.norm_coe_le_norm (f + g)
          ⟨1, by constructor <;> norm_num⟩
        calc
          2 = ‖(f + g) ⟨1, by constructor <;> norm_num⟩‖ := by norm_num [f, g]
          _ ≤ ‖f + g‖ := h
    have hfm : ‖f - g‖ = 1 := by
      apply le_antisymm
      · rw [ContinuousMap.norm_le_of_nonempty]
        intro x
        change |1 - (x : ℝ)| ≤ 1
        rw [abs_of_nonneg (by linarith [x.2.2])]
        linarith [x.2.1]
      · have h := ContinuousMap.norm_coe_le_norm (f - g)
          ⟨0, by constructor <;> norm_num⟩
        calc
          1 = ‖(f - g) ⟨0, by constructor <;> norm_num⟩‖ := by norm_num [f, g]
          _ ≤ ‖f - g‖ := h
    refine ⟨f, g, ?_⟩
    rw [hf, hg, hfg, hfm]
    norm_num
  · -- (Sibling: m01J01)
    intro X Y _ _ _ _ _ _ T hT
    exact T.isOpenMap hT
  · -- (Sibling: m01J01)
    intro X Y _ _ _ _ _ _ T hT
    apply T.continuous_of_isClosed_graph
    simpa [LinearMap.graph, eq_comm] using hT
