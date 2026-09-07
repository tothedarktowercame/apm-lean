import Mathlib

/-! # APM t94A01: the weighted metric on the countable cube

## Statement repairs

The source's coordinates indexed by `1,2,…` are reindexed by `ℕ`; consequently
the weight is `2⁻(i+1)`.

## Encoding questions

The product topology is Mathlib's topology on the dependent function type
`∀ i : ℕ, Set.Icc (0 : ℝ) 1`.  Rather than install a second global metric
instance, metric openness is stated directly using the concrete `rho` balls.
-/

abbrev APMT94A01.Cube := ∀ _ : ℕ, Set.Icc (0 : ℝ) 1

noncomputable def APMT94A01.rho (f g : APMT94A01.Cube) : ℝ :=
  ∑' i : ℕ, (1 / 2 : ℝ) ^ (i + 1) * |(f i : ℝ) - (g i : ℝ)|

theorem apm_t94a01 (U : Set APMT94A01.Cube) :
    IsOpen U ↔
      ∀ f ∈ U, ∃ ε > (0 : ℝ),
        {g | APMT94A01.rho f g < ε} ⊆ U := by
  sorry
