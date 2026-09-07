import ConstructionTargets.SardCriticalRankStrata
import ConstructionTargets.SardLocalRankNormalForm

open Set

/-- The locus where the derivative has rank at least `r`. -/
def derivativeRankAtLeast
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (r : ℕ) : Set E :=
  {x | (r : Cardinal) ≤ (fderiv ℝ f x).toLinearMap.rank}

/-- For a `C¹` map between finite-dimensional real normed spaces, the locus
where derivative rank is at least `r` is open. -/
theorem isOpen_derivativeRankAtLeast
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (f : E → F) (r : ℕ) (hf : ContDiff ℝ 1 f) :
    IsOpen (derivativeRankAtLeast f r) := by
  exact isOpen_setOf_nat_le_rank r |>.preimage (hf.continuous_fderiv one_ne_zero)

/-- Near a point of exact derivative rank `r`, the exact-rank stratum is the
upper-rank-bounded locus: the complementary lower bound is supplied by an open
neighborhood of the point. -/
theorem exists_open_inter_rankStratum_eq_rankLE
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (f : E → F) (x : E) (r : ℕ) (hf : ContDiff ℝ 1 f)
    (hx : x ∈ rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
      U ∩ rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r =
        U ∩ {y | Module.finrank ℝ (LinearMap.range (fderiv ℝ f y).toLinearMap) ≤ r} := by
  refine ⟨derivativeRankAtLeast f r, isOpen_derivativeRankAtLeast f r hf, ?_, ?_⟩
  · change (r : Cardinal) ≤ (fderiv ℝ f x).toLinearMap.rank
    change (r : Cardinal) ≤ Module.rank ℝ
      (LinearMap.range (fderiv ℝ f x).toLinearMap)
    rw [← Submodule.finrank_eq_rank]
    exact_mod_cast le_of_eq hx.symm
  · ext y
    simp only [mem_inter_iff, derivativeRankAtLeast, mem_setOf_eq, rankStratum]
    constructor
    · rintro ⟨hlow, heq⟩
      exact ⟨hlow, heq.le⟩
    · rintro ⟨hlow, hupp⟩
      have hlow' : r ≤ Module.finrank ℝ
          (LinearMap.range (fderiv ℝ f y).toLinearMap) := by
        have hcast : (r : Cardinal) ≤
            (Module.finrank ℝ (LinearMap.range (fderiv ℝ f y).toLinearMap) : Cardinal) := by
          rw [Submodule.finrank_eq_rank]
          exact hlow
        exact_mod_cast hcast
      exact ⟨hlow, le_antisymm hupp hlow'⟩

#print axioms isOpen_derivativeRankAtLeast
#print axioms exists_open_inter_rankStratum_eq_rankLE
