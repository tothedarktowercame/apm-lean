import Mathlib

/-! # APM m99A03: compact powers and normal nilpotent operators

## Statement repairs

Part (b) cannot hold on every Hilbert space (for example, not on a
finite-dimensional one).  Its instruction to “construct an example” is encoded
as an existential example on the explicit infinite-dimensional Hilbert space
`m99A03ExampleSpace`.
-/

noncomputable section

abbrev m99A03L2 := lp (fun _ : ℕ => ℂ) 2
abbrev m99A03ExampleSpace := m99A03L2 × m99A03L2 × m99A03L2

/-- The three-step block shift used in the non-normal counterexample. -/
def m99A03Shift : m99A03ExampleSpace →L[ℂ] m99A03ExampleSpace where
  toFun x := (x.2.1, x.2.2, 0)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp
  cont := by fun_prop

@[simp] lemma m99A03Shift_apply (x : m99A03ExampleSpace) :
    m99A03Shift x = (x.2.1, x.2.2, 0) := rfl

lemma m99A03Shift_sq_apply (x : m99A03ExampleSpace) :
    (m99A03Shift ^ 2) x = (x.2.2, 0, 0) := by
  simp [pow_two]

lemma m99A03Shift_cube : m99A03Shift ^ 3 = 0 := by
  ext x <;> simp [pow_succ]

theorem apm_m99a03 :
    (∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (A : H →L[ℂ] H),
      IsCompactOperator A → IsStarNormal A → A ^ 3 = 0 → A = 0) ∧
    (∃ A : m99A03ExampleSpace →L[ℂ] m99A03ExampleSpace,
      ¬IsCompactOperator A ∧
      ¬IsCompactOperator
        ((A ^ 2 : m99A03ExampleSpace →L[ℂ] m99A03ExampleSpace) :
          m99A03ExampleSpace → m99A03ExampleSpace) ∧
      IsCompactOperator
        ((A ^ 3 : m99A03ExampleSpace →L[ℂ] m99A03ExampleSpace) :
          m99A03ExampleSpace → m99A03ExampleSpace)) := by
  constructor
  · intro H _ _ _ A _hcompact hnormal hcube
    have hfourth : A ^ 4 = 0 := by
      calc
        A ^ 4 = A ^ 3 * A := by noncomm_ring
        _ = 0 := by rw [hcube, zero_mul]
    letI : IsStarNormal A := hnormal
    have hrad : spectralRadius ℂ A = 0 := by
      have hp := spectrum.spectralRadius_pow_le (𝕜 := ℂ) A 4 (by norm_num)
      rw [hfourth, spectrum.spectralRadius_zero] at hp
      have hp0 : (spectralRadius ℂ A) ^ 4 = 0 := le_antisymm hp bot_le
      exact eq_zero_of_pow_eq_zero hp0
    have hnorm : ‖A‖₊ = 0 := by
      have hs := IsStarNormal.spectralRadius_eq_nnnorm A
      rw [hrad] at hs
      simpa using hs.symm
    exact nnnorm_eq_zero.mp hnorm
  · refine ⟨m99A03Shift, ?_, ?_, ?_⟩
    · /-
      Boundary: proving `m99A03Shift` noncompact requires feeding the bounded
      sequence `(0, lp.single 2 n 1, 0)` into a sequential or totally-bounded
      characterization of `IsCompactOperator` and proving its image is
      pairwise separated. I searched `lp.norm_single`, `lp.single_apply`,
      `IsCompactOperator.isCompact_closure_image_ball`, and compact sequential
      criteria; the separated-sequence bridge was not completed.
      -/
      sorry
    · /-
      Boundary: the analogous argument for `m99A03Shift ^ 2` uses the bounded
      sequence `(0, 0, lp.single 2 n 1)`. The power formula is proved by
      `m99A03Shift_sq_apply`, but the same compactness-to-convergent-subsequence
      interface remains to be assembled.
      -/
      sorry
    · rw [m99A03Shift_cube]
      exact isCompactOperator_zero
