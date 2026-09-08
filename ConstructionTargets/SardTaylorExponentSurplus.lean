import Mathlib

namespace SardTaylorExponentSurplusProbe

theorem exists_taylor_exponent_surplus
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F] [Nontrivial F] :
    ∃ k d : ℕ, 0 < d ∧
      (k + 1) * Module.finrank ℝ F = Module.finrank ℝ E + d := by
  have hF : 0 < Module.finrank ℝ F := Module.finrank_pos
  have hle : Module.finrank ℝ E + 1 ≤
      (Module.finrank ℝ E + 1) * Module.finrank ℝ F := by
    nlinarith
  have hlt : Module.finrank ℝ E <
      (Module.finrank ℝ E + 1) * Module.finrank ℝ F :=
    lt_of_lt_of_le (Nat.lt_succ_self _) hle
  refine ⟨Module.finrank ℝ E,
    (Module.finrank ℝ E + 1) * Module.finrank ℝ F - Module.finrank ℝ E, ?_, ?_⟩
  · exact Nat.sub_pos_iff_lt.mpr hlt
  · exact (Nat.add_sub_of_le (Nat.le_of_lt hlt)).symm

#print axioms exists_taylor_exponent_surplus

end SardTaylorExponentSurplusProbe
