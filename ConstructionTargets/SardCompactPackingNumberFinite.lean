import Mathlib.Topology.MetricSpace.CoveringNumbers

/-! # Compact sets have finite packing number at nonzero radius -/

open Metric Set
open scoped ENNReal NNReal

/-- In a proper metric space, a compact set has non-infinite packing number at
every nonzero `NNReal` separation radius. -/
theorem IsCompact.packingNumber_ne_top
    {X : Type*} [MetricSpace X] [ProperSpace X]
    {A : Set X} (hA : IsCompact A) (ε : ℝ≥0) (hε : ε ≠ 0) :
    packingNumber ε A ≠ ⊤ := by
  have hhalf : ε / 2 ≠ 0 := div_ne_zero hε (by norm_num)
  have hclosure : IsCompact (closure A) := by
    rw [hA.isClosed.closure_eq]
    exact hA
  obtain ⟨N, hNA, hNfin, hcover⟩ :=
    (isCompact_closure_iff_exists_finite_isCover (s := A) hhalf).mp hclosure
  have hext : externalCoveringNumber (ε / 2) A < ⊤ :=
    lt_of_le_of_lt hcover.externalCoveringNumber_le_encard hNfin.encard_lt_top
  have hpack : packingNumber ε A ≤ externalCoveringNumber (ε / 2) A := by
    convert packingNumber_two_mul_le_externalCoveringNumber (ε / 2) A using 1
    rw [two_mul, add_halves]
  exact ne_of_lt (lt_of_le_of_lt hpack hext)

#print axioms IsCompact.packingNumber_ne_top
