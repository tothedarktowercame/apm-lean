import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Operations

open Set Metric Filter
open scoped Topology

theorem exists_global_contDiff_germ_of_contDiffOn_open
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (U : Set E) (x : E) (n : ℕ∞)
    (hU : IsOpen U) (hx : x ∈ U) (hf : ContDiffOn ℝ n f U) :
    ∃ g : E → F, ContDiff ℝ n g ∧ g =ᶠ[𝓝 x] f := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (hU.mem_nhds hx)
  let b : ContDiffBump x :=
    { rIn := r / 4
      rOut := r / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  refine ⟨fun y => b y • f y, contDiff_iff_contDiffAt.2 ?_, ?_⟩
  · intro y
    by_cases hy : y ∈ closedBall x (r / 2)
    · have hyU : y ∈ U := hball (closedBall_subset_ball (by linarith) hy)
      exact b.contDiff.contDiffAt.smul ((hf y hyU).contDiffAt (hU.mem_nhds hyU))
    · apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
      filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hy] with z hz
      have hzdist : r / 2 ≤ dist z x := by
        have : ¬ dist z x ≤ r / 2 := hz
        linarith
      simp only [b.zero_of_le_dist hzdist, zero_smul]
  · filter_upwards [b.eventuallyEq_one] with y hy
    simp only [hy, Pi.one_apply, one_smul]

#print axioms exists_global_contDiff_germ_of_contDiffOn_open
