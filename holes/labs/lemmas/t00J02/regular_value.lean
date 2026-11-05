import Mathlib
import ConstructionTargets.t00J02Closure

open Set
open scoped Manifold Topology ContDiff

noncomputable section

namespace ConstructionTargets.T00J02Closure

/-- The fixed-target-chart Sard selector can be constrained to any open
neighborhood of the chart centre.  The chart-coordinate image of that
neighborhood is a nonempty open set, hence has positive additive Haar
measure, while the critical image is null. -/
theorem exists_mfderiv_surjective_fiber_mem_open_of_fixedTargetChart
    {E F M N : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) ∞ M] [SecondCountableTopology M]
    [TopologicalSpace N] [ChartedSpace F N]
    [IsManifold (modelWithCornersSelf ℝ F) ∞ N]
    (mu : MeasureTheory.Measure F) [mu.IsAddHaarMeasure]
    (g : M → N) (y : N)
    (hg : ContMDiff (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ F) ∞ g)
    (O : Set N) (hO : IsOpen O) (hyO : y ∈ O) :
    ∃ z ∈ O, ∀ x, g x = z → Function.Surjective
      (mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ F) g x) := by
  let bad : Set F := ((chartAt F y) ∘ g) ''
    {x | x ∈ targetChartDomain (F := F) g y hg.continuous ∧
      ¬ Function.Surjective
        (mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ F)
          ((chartAt F y) ∘ g) x)}
  have hbad : mu bad = 0 := targetChartCoordinate_ambientCriticalImage_null mu g y hg
  let T : Set F := (chartAt F y).target ∩ (chartAt F y).symm ⁻¹' O
  have hTopen : IsOpen T := (chartAt F y).isOpen_inter_preimage_symm hO
  have hyT : chartAt F y y ∈ T := by
    refine ⟨mem_chart_target F y, ?_⟩
    change (chartAt F y).symm (chartAt F y y) ∈ O
    rw [(chartAt F y).left_inv (mem_chart_source F y)]
    exact hyO
  have hT : mu T ≠ 0 := hTopen.measure_ne_zero mu ⟨_, hyT⟩
  have hnsub : ¬ T ⊆ bad := by
    intro hsub
    exact hT (MeasureTheory.measure_mono_null hsub hbad)
  rcases Set.not_subset.mp hnsub with ⟨v, hvT, hvbad⟩
  refine ⟨(chartAt F y).symm v, hvT.2, fun x hx ↦ ?_⟩
  have hxsource : g x ∈ (chartAt F y).source := by
    rw [hx]
    exact (chartAt F y).map_target hvT.1
  by_contra hcrit
  apply hvbad
  refine ⟨x, ⟨hxsource, ?_⟩, ?_⟩
  · intro hs
    exact hcrit ((mfderiv_targetChart_comp_surjective_iff_of_mem_source
      g x y (hg.mdifferentiableAt (by simp)) hxsource).mpr hs)
  · change chartAt F y (g x) = v
    rw [hx, (chartAt F y).right_inv hvT.1]

#print axioms exists_mfderiv_surjective_fiber_mem_open_of_fixedTargetChart

end ConstructionTargets.T00J02Closure
