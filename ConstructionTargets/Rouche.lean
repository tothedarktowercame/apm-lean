import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Calculus.LogDeriv

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

/-- Away from its finite support, the logarithmic derivative of a factorized
rational function is the finite sum of its elementary logarithmic
derivatives.  This is the algebraic local-to-global step in the argument
principle. -/
lemma logDeriv_factorizedRational_eq_finsum
    {U : Set ℂ} (D : Function.locallyFinsuppWithin U ℤ)
    (hD : D.support.Finite) {x : ℂ} (hx : x ∉ D.support) :
    logDeriv (∏ᶠ u, (· - u) ^ D u) x =
      ∑ᶠ u, (D u : ℂ) / (x - u) := by
  classical
  let s := hD.toFinset
  have hprod :
      (∏ᶠ u, (· - u) ^ D u) = fun z ↦ ∏ u ∈ s, (z - u) ^ D u := by
    rw [finprod_eq_prod_of_mulSupport_subset (s := s)]
    · ext z
      simp only [Finset.prod_apply, Pi.pow_apply]
    · simpa [s, Function.FactorizedRational.mulSupport]
  have hsum :
      ∑ᶠ u, (D u : ℂ) / (x - u) = ∑ u ∈ s, (D u : ℂ) / (x - u) := by
    rw [finsum_eq_sum_of_support_subset]
    intro u hu
    simp only [Function.mem_support] at hu
    have hDu : D u ≠ 0 := by
      intro h
      simp [h] at hu
    simpa [s] using hDu
  rw [hprod, hsum]
  rw [logDeriv_prod]
  · apply Finset.sum_congr rfl
    intro u hu
    rw [logDeriv_fun_zpow (f := fun z ↦ z - u)
      (differentiableAt_id.sub_const u)]
    simp only [logDeriv_apply]
    rw [deriv_sub_const]
    simp [deriv_id'', div_eq_mul_inv]
  · intro u hu
    have hux : u ≠ x := by
      intro h
      apply hx
      rw [← h]
      simpa [s] using hu
    exact zpow_ne_zero _ (sub_ne_zero.mpr hux.symm)
  · intro u hu
    exact DifferentiableAt.zpow (differentiableAt_id.sub_const u)
      (Or.inl <| sub_ne_zero.mpr <| by
        intro h
        apply hx
        rw [h]
        simpa [s] using hu)

/-- The argument-principle integral for a finite factorized rational
function whose divisor is supported strictly inside the circle. -/
lemma circleIntegral_logDeriv_factorizedRational
    {U : Set ℂ} (D : Function.locallyFinsuppWithin U ℤ)
    (hD : D.support.Finite) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hDb : D.support ⊆ ball c R) :
    (∮ z in C(c, R), logDeriv (∏ᶠ u, (· - u) ^ D u) z) =
      (∑ᶠ u, (D u : ℂ)) * (2 * Real.pi * I) := by
  classical
  let s := hD.toFinset
  have hsphere : ∀ z ∈ sphere c R, z ∉ D.support := by
    intro z hz hzD
    have hzball := hDb hzD
    rw [mem_sphere] at hz
    rw [mem_ball] at hzball
    linarith
  rw [circleIntegral.integral_congr hR.le fun z hz ↦
    logDeriv_factorizedRational_eq_finsum D hD (hsphere z hz)]
  have hsumfun :
      (fun z ↦ ∑ᶠ u, (D u : ℂ) / (z - u)) =
        fun z ↦ ∑ u ∈ s, (D u : ℂ) / (z - u) := by
    funext z
    rw [finsum_eq_sum_of_support_subset]
    intro u hu
    simp only [Function.mem_support] at hu
    have hDu : D u ≠ 0 := by
      intro h
      simp [h] at hu
    simpa [s] using hDu
  rw [hsumfun, circleIntegral.integral_fun_sum]
  · have hterm : ∀ u ∈ s,
        (∮ z in C(c, R), (D u : ℂ) / (z - u)) =
          (D u : ℂ) * (2 * Real.pi * I) := by
      intro u hu
      have huD : u ∈ D.support := by simpa [s] using hu
      change (∮ z in C(c, R), (D u : ℂ) * (z - u)⁻¹) = _
      rw [circleIntegral.integral_const_mul,
        circleIntegral.integral_sub_inv_of_mem_ball (hDb huD)]
    rw [Finset.sum_congr rfl hterm]
    rw [finsum_eq_sum_of_support_subset (s := s)]
    · rw [Finset.sum_mul]
    · simpa [s]
  · intro u hu
    have huD : u ∈ D.support := by simpa [s] using hu
    have husphere : ∀ z ∈ sphere c R, z - u ≠ 0 := by
      intro z hz hzu
      have hzu' : z = u := sub_eq_zero.mp hzu
      subst z
      exact hsphere u hz huD
    exact (continuousOn_const.mul
      ((continuousOn_id.sub continuousOn_const).inv₀ husphere)).circleIntegrable hR.le

/-- A zero-free analytic factor contributes zero to the argument-principle
integral.  This is the analytic remainder term produced by
`MeromorphicOn.extract_zeros_poles`. -/
lemma circleIntegral_logDeriv_eq_zero_of_analyticOnNhd_of_ne_zero
    {h : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hh : AnalyticOnNhd ℂ h (closedBall c R))
    (hne : ∀ z ∈ closedBall c R, h z ≠ 0) :
    (∮ z in C(c, R), logDeriv h z) = 0 := by
  have hlog : AnalyticOnNhd ℂ (logDeriv h) (closedBall c R) := by
    simpa only [logDeriv_apply, div_eq_mul_inv] using hh.deriv.mul (hh.inv hne)
  apply circleIntegral_eq_zero_of_differentiable_on_off_countable hR countable_empty
  · exact hlog.continuousOn
  · intro z hz
    exact (hlog z (ball_subset_closedBall hz.1)).differentiableAt

/-- Extract the finite divisor of an analytic function which is nonzero on the
boundary of a positive-radius disk.  The residual factor is analytic and
zero-free on the whole closed disk. -/
lemma exists_zeroFree_factorization_on_closedBall
    {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hne : ∀ z ∈ sphere c R, f z ≠ 0) :
    ∃ h : ℂ → ℂ,
      AnalyticOnNhd ℂ h (closedBall c R) ∧
        (∀ z : closedBall c R, h z ≠ 0) ∧
        f =ᶠ[codiscreteWithin (closedBall c R)]
          (∏ᶠ u, (· - u) ^ divisor f (closedBall c R) u) * h := by
  have hfm : MeromorphicOn f (closedBall c R) := hf.meromorphicOn
  let z : ℂ := c + R
  have hz : z ∈ sphere c R := by
    rw [mem_sphere]
    simp [z, abs_of_pos hR]
  have hzcb : z ∈ closedBall c R := sphere_subset_closedBall hz
  have hzorder : meromorphicOrderAt f z ≠ ⊤ := by
    have hz0 : meromorphicOrderAt f z = 0 :=
      (hf z hzcb).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr (hne z hz)
    simp [hz0]
  have hord : ∀ u : closedBall c R, meromorphicOrderAt f u ≠ ⊤ :=
    (hfm.exists_meromorphicOrderAt_ne_top_iff_forall
      (isConnected_closedBall hR.le)).1 ⟨⟨z, hzcb⟩, hzorder⟩
  exact hfm.extract_zeros_poles hord
    ((divisor f (closedBall c R)).finiteSupport (isCompact_closedBall c R))

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
