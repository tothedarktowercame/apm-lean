import Mathlib

open Set

noncomputable section

private noncomputable def outsideBump : ContDiffBump (2 : ℝ) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

lemma outsideBump_smooth : ContDiff ℝ 2 (outsideBump : ℝ → ℝ) := by
  exact outsideBump.contDiff

lemma outsideBump_zero_on_unit_interval :
    ∀ x ∈ Icc (0 : ℝ) 1, outsideBump x = 0 := by
  intro x hx
  apply outsideBump.zero_of_le_dist
  rw [Real.dist_eq]
  have : x - 2 ≤ -1 := by linarith [hx.2]
  rw [abs_of_nonpos (by linarith)]
  norm_num [outsideBump]
  linarith

lemma outsideBump_nonzero : outsideBump (2 : ℝ) = 1 := by
  exact outsideBump.one_of_mem_closedBall (by simp [outsideBump])

lemma outsideBump_not_zero : (outsideBump : ℝ → ℝ) ≠ 0 := by
  intro h
  have := congrFun h 2
  simpa [outsideBump_nonzero] using this

lemma outsideBump_eventually_zero_on_unit_interval
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (outsideBump : ℝ → ℝ) =ᶠ[nhds x] 0 := by
  have hnhds : Iio (3 / 2 : ℝ) ∈ nhds x :=
    Iio_mem_nhds (by linarith [hx.2])
  filter_upwards [hnhds] with y hy
  change y < (3 / 2 : ℝ) at hy
  apply outsideBump.zero_of_le_dist
  rw [Real.dist_eq, abs_of_nonpos (by linarith)]
  norm_num [outsideBump]
  linarith

lemma outsideBump_deriv_zero_on_unit_interval
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    deriv (outsideBump : ℝ → ℝ) x = 0 := by
  rw [(outsideBump_eventually_zero_on_unit_interval hx).deriv_eq]
  simp
