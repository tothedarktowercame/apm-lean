import Mathlib.Analysis.Complex.JensenFormula

/-!
# Rouché root-count transfer on a disk

This file gives the reusable statement needed by `a92J05` and `a94A10`.
The elementary boundary-homotopy part is proved below.  The remaining theorem
is precisely the missing argument-principle/homotopy-invariance step.
-/

open Complex Filter MeromorphicOn Metric Set

noncomputable section

namespace ConstructionTargets.Rouche

/-- Total zero multiplicity of `f` in a closed disk, expressed using Mathlib's
meromorphic divisor.  For a nonzero function analytic on a neighborhood of the
disk, the divisor has finite support there and all its values are nonnegative. -/
def zeroCountInClosedBall (f : ℂ → ℂ) (c : ℂ) (R : ℝ) : ℤ :=
  ∑ᶠ z, divisor f (closedBall c R) z

/-- The strict Rouché inequality keeps the straight-line homotopy away from
zero on the boundary.  This is the pointwise topological core of the theorem. -/
lemma add_smul_ne_zero_of_norm_le_one
    {f g : ℂ → ℂ} {z t : ℂ}
    (ht : ‖t‖ ≤ 1) (hfg : ‖g z‖ < ‖f z‖) :
    f z + t * g z ≠ 0 := by
  intro hzero
  have heq : f z = -(t * g z) := eq_neg_of_add_eq_zero_left hzero
  have hle : ‖f z‖ ≤ ‖g z‖ := by
    rw [heq, norm_neg, norm_mul]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right ht (norm_nonneg (g z))
  exact (not_lt_of_ge hle) hfg

/-- Under the strict boundary inequality, the dominant function has no zero
on the boundary circle. -/
lemma dominant_ne_zero_on_sphere
    {f g : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hfg : ∀ z ∈ sphere c R, ‖g z‖ < ‖f z‖) :
    ∀ z ∈ sphere c R, f z ≠ 0 := by
  intro z hz hfz
  have := hfg z hz
  rw [hfz, norm_zero] at this
  exact (not_lt_of_ge (norm_nonneg (g z))) this

/-- Every member of the straight-line homotopy `f + t • g`, `0 ≤ t ≤ 1`,
is nonzero on the boundary circle. -/
lemma rouche_homotopy_ne_zero_on_sphere
    {f g : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hfg : ∀ z ∈ sphere c R, ‖g z‖ < ‖f z‖) :
    ∀ t : Set.Icc (0 : ℝ) 1, ∀ z ∈ sphere c R,
      f z + (t.1 : ℂ) * g z ≠ 0 := by
  intro t z hz
  apply add_smul_ne_zero_of_norm_le_one
  · simpa [abs_of_nonneg t.2.1] using t.2.2
  · exact hfg z hz

/-- Every member of the Rouché straight-line homotopy remains analytic on the
same neighborhood.  Together with `rouche_homotopy_ne_zero_on_sphere`, this
packages the complete analytic/topological input expected by an argument
principle homotopy-invariance theorem. -/
lemma rouche_homotopy_analyticOnNhd
    {f g : ℂ → ℂ} {s : Set ℂ}
    (hf : AnalyticOnNhd ℂ f s) (hg : AnalyticOnNhd ℂ g s) (t : ℝ) :
    AnalyticOnNhd ℂ (fun z ↦ f z + (t : ℂ) * g z) s := by
  simpa only [Pi.add_apply] using
    hf.add (analyticOnNhd_const.mul hg)

/-- The straight-line homotopy simultaneously has the required analyticity
and boundary nonvanishing properties.  This is the exact input left after
separating Rouché's elementary estimate from the argument principle. -/
lemma rouche_homotopy_analyticOnNhd_and_ne_zero
    {f g : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hfg : ∀ z ∈ sphere c R, ‖g z‖ < ‖f z‖)
    (t : Set.Icc (0 : ℝ) 1) :
    AnalyticOnNhd ℂ (fun z ↦ f z + (t.1 : ℂ) * g z) (closedBall c R) ∧
      ∀ z ∈ sphere c R, f z + (t.1 : ℂ) * g z ≠ 0 := by
  exact ⟨rouche_homotopy_analyticOnNhd hf hg t.1,
    rouche_homotopy_ne_zero_on_sphere hfg t⟩

/-- **Rouché's theorem on a closed disk.** If `f` and `g` are holomorphic on
a neighborhood of the closed disk and `‖g‖ < ‖f‖` on its boundary, then `f`
and `f + g` have the same number of zeros in the disk, counted with
multiplicity.

The current Mathlib divisor/Jensen API supplies the zero multiplicities and
their local finiteness.  The missing bridge is invariance of the total divisor
under a boundary-nonvanishing holomorphic homotopy (equivalently, the argument
principle). `rouche_homotopy_analyticOnNhd_and_ne_zero` proves the complete
analytic and boundary input for the standard straight-line homotopy. -/
theorem zeroCountInClosedBall_add_eq
    {f g : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hfg : ∀ z ∈ sphere c R, ‖g z‖ < ‖f z‖) :
    zeroCountInClosedBall (f + g) c R = zeroCountInClosedBall f c R := by
  sorry

end ConstructionTargets.Rouche
