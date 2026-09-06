import Mathlib

/-! # Finite rank-stratum decomposition of a critical set -/

open Set Function
noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]

/-- The critical set of a family of linear maps is its nonsurjective locus. -/
def criticalSet (f' : E → E →ₗ[ℝ] F) : Set E :=
  {x | ¬ Surjective (f' x)}

/-- The locus where a family of linear maps has range of rank exactly `r`. -/
def rankStratum (f' : E → E →ₗ[ℝ] F) (r : ℕ) : Set E :=
  {x | Module.finrank ℝ (LinearMap.range (f' x)) = r}

/-- With finite-dimensional target, the nonsurjective locus is the finite
union of the exact rank strata strictly below the target dimension. -/
theorem criticalSet_eq_iUnion_rankStratum (f' : E → E →ₗ[ℝ] F) :
    criticalSet f' = ⋃ r : Fin (Module.finrank ℝ F), rankStratum f' r := by
  ext x
  simp only [criticalSet, rankStratum, mem_setOf_eq, mem_iUnion]
  constructor
  · intro hx
    have hproper : LinearMap.range (f' x) < ⊤ :=
      (lt_top_iff_ne_top.mpr fun htop => hx (LinearMap.range_eq_top.mp htop))
    have hlt : Module.finrank ℝ (LinearMap.range (f' x)) < Module.finrank ℝ F := by
      simpa using Submodule.finrank_lt_finrank_of_lt hproper
    exact ⟨⟨Module.finrank ℝ (LinearMap.range (f' x)), hlt⟩, rfl⟩
  · rintro ⟨r, hr⟩ hsurj
    have htop : LinearMap.range (f' x) = ⊤ := LinearMap.range_eq_top.mpr hsurj
    have : Module.finrank ℝ (LinearMap.range (f' x)) = Module.finrank ℝ F := by
      rw [htop]
      exact finrank_top ℝ F
    omega

#print axioms criticalSet_eq_iUnion_rankStratum
