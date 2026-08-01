import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Instances.ZMultiples

/-!
# Rouché root-count transfer on a disk

This file gives the reusable statement needed by `a92J05` and `a94A10`.
The elementary boundary-homotopy part is proved below.  The remaining theorem
is precisely the missing argument-principle/homotopy-invariance step.
-/

open Complex Filter MeromorphicOn Metric Set
open scoped Topology

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

/-- Every point of a positive-radius complex sphere is an accumulation point
of that sphere, hence also of the corresponding closed ball. -/
lemma accPt_closedBall_of_mem_sphere
    {c z : ℂ} {R : ℝ} (hR : 0 < R) (hz : z ∈ sphere c R) :
    AccPt z (𝓟 (closedBall c R)) := by
  let zp : sphere c R := ⟨c + R, by
    rw [mem_sphere]
    simp [abs_of_pos hR]⟩
  let zm : sphere c R := ⟨c - R, by
    rw [mem_sphere]
    simp [abs_of_pos hR]⟩
  letI : Nontrivial (sphere c R) := ⟨⟨zp, zm, by
    intro h
    have h' : c + (R : ℂ) = c - (R : ℂ) := congrArg Subtype.val h
    have hr := congrArg Complex.re h'
    norm_num at hr
    linarith⟩⟩
  letI : ConnectedSpace (sphere c R) :=
    isConnected_iff_connectedSpace.mp (isConnected_sphere (by simp) c hR.le)
  have hsub : AccPt (⟨z, hz⟩ : sphere c R) (𝓟 Set.univ) := by
    rw [accPt_principal_iff_nhdsWithin]
    have heq : (Set.univ \ {⟨z, hz⟩} : Set (sphere c R)) = {⟨z, hz⟩}ᶜ := by
      ext y
      constructor
      · exact fun hy => hy.2
      · exact fun hy => ⟨mem_univ y, hy⟩
    rw [heq]
    infer_instance
  rw [accPt_iff_frequently] at hsub ⊢
  have hsub' : ∃ᶠ y in 𝓝[sphere c R] z, y ≠ z :=
    (frequently_nhds_subtype_iff (sphere c R) ⟨z, hz⟩ (fun y : ℂ => y ≠ z)).mp
      (hsub.mono fun y hy hcoe => hy.1 (Subtype.ext hcoe))
  have hamb : ∃ᶠ y in 𝓝 z, y ≠ z ∧ y ∈ sphere c R := by
    rw [nhdsWithin, frequently_inf_principal] at hsub'
    exact hsub'.mono fun y hy => ⟨hy.2, hy.1⟩
  exact hamb.mono fun y hy => ⟨hy.1, sphere_subset_closedBall hy.2⟩

/-- The argument-principle boundary identity for an analytic function which
does not vanish on the boundary circle. -/
lemma circleIntegral_logDeriv_eq_divisor_sum
    {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hne : ∀ z ∈ sphere c R, f z ≠ 0) :
    (∮ z in C(c, R), logDeriv f z) =
      (∑ᶠ z, (divisor f (closedBall c R) z : ℂ)) * (2 * Real.pi * I) := by
  classical
  let D := divisor f (closedBall c R)
  let q : ℂ → ℂ := ∏ᶠ u, (· - u) ^ D u
  have hD : D.support.Finite :=
    (divisor f (closedBall c R)).finiteSupport (isCompact_closedBall c R)
  have hDb : D.support ⊆ ball c R := by
    intro z hzD
    have hzcb : z ∈ closedBall c R := D.supportWithinDomain hzD
    rw [mem_ball]
    have hzle : dist z c ≤ R := by
      simpa [dist_comm] using (mem_closedBall.mp hzcb)
    exact lt_of_le_of_ne hzle fun heq => by
      have hzs : z ∈ sphere c R := by
        rw [mem_sphere]
        exact heq
      have hDz : D z = 0 := by
        have hzorder : meromorphicOrderAt f z = 0 :=
          (hf z hzcb).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
            (hne z hzs)
        simp [D, MeromorphicOn.divisor_apply hf.meromorphicOn hzcb, hzorder]
      exact (Function.mem_support.mp hzD) hDz
  obtain ⟨h, hh, hhne, hfac⟩ :=
    exists_zeroFree_factorization_on_closedBall hR hf hne
  have hq_analytic : AnalyticOnNhd ℂ q (sphere c R) := by
    intro z hz
    have hzcb : z ∈ closedBall c R := sphere_subset_closedBall hz
    have hzD : D z = 0 := by
      apply not_ne_iff.mp
      intro hzD
      have hzball := hDb (Function.mem_support.mpr hzD)
      rw [mem_ball] at hzball
      rw [mem_sphere] at hz
      linarith
    apply ((Function.FactorizedRational.meromorphicNFOn D
      (closedBall c R)) hzcb).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [Function.FactorizedRational.meromorphicOrderAt_eq D hD, hzD]
    exact le_rfl
  have hqne : ∀ z ∈ sphere c R, q z ≠ 0 := by
    intro z hz
    apply Function.FactorizedRational.ne_zero
    apply not_ne_iff.mp
    intro hzD
    have hzball := hDb (Function.mem_support.mpr hzD)
    rw [mem_ball] at hzball
    rw [mem_sphere] at hz
    linarith
  have hpoint : ∀ z ∈ sphere c R,
      logDeriv f z = logDeriv q z + logDeriv h z := by
    intro z hz
    have hzcb : z ∈ closedBall c R := sphere_subset_closedBall hz
    have hprod : AnalyticAt ℂ (q * h) z :=
      (hq_analytic z hz).mul (hh z hzcb)
    have hlocalNE : f =ᶠ[𝓝[≠] z] q * h :=
      (hf z hzcb).meromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
        hprod.meromorphicAt hzcb (accPt_closedBall_of_mem_sphere hR hz) hfac
    have hvalue : f z = (q * h) z := by
      letI := NormedField.nhdsNE_neBot (α := ℂ) z
      exact tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[≠] z)
        ((hf z hzcb).continuousAt.tendsto.mono_left inf_le_left)
        (hprod.continuousAt.tendsto.mono_left inf_le_left)
        hlocalNE
    have hlocal : f =ᶠ[𝓝 z] q * h :=
      eventuallyEq_nhds_of_eventuallyEq_nhdsNE hlocalNE hvalue
    rw [show logDeriv f z = logDeriv (q * h) z by
      simp only [logDeriv_apply, hlocal.deriv_eq, hlocal.self_of_nhds]]
    exact logDeriv_mul z (hqne z hz) (hhne ⟨z, hzcb⟩)
      (hq_analytic z hz).differentiableAt (hh z hzcb).differentiableAt
  have hqlog : AnalyticOnNhd ℂ (logDeriv q) (sphere c R) := by
    simpa only [logDeriv_apply, div_eq_mul_inv] using
      hq_analytic.deriv.mul (hq_analytic.inv hqne)
  have hhlog : AnalyticOnNhd ℂ (logDeriv h) (closedBall c R) := by
    simpa only [logDeriv_apply, div_eq_mul_inv] using
      hh.deriv.mul (hh.inv fun z hz => hhne ⟨z, hz⟩)
  rw [circleIntegral.integral_congr hR.le hpoint,
    circleIntegral.integral_add (hqlog.continuousOn.circleIntegrable hR.le)
      ((hhlog.continuousOn.mono sphere_subset_closedBall).circleIntegrable hR.le),
    show (∮ z in C(c, R), logDeriv q z) =
        (∑ᶠ z, (D z : ℂ)) * (2 * Real.pi * I) by
      exact circleIntegral_logDeriv_factorizedRational D hD hR hDb,
    circleIntegral_logDeriv_eq_zero_of_analyticOnNhd_of_ne_zero hR.le hh
      (fun z hz => hhne ⟨z, hz⟩),
    add_zero]

/-- Casting the integer-valued zero count commutes with its finite divisor
sum. -/
lemma intCast_zeroCountInClosedBall (f : ℂ → ℂ) (c : ℂ) (R : ℝ) :
    (zeroCountInClosedBall f c R : ℂ) =
      ∑ᶠ z, (divisor f (closedBall c R) z : ℂ) := by
  unfold zeroCountInClosedBall
  exact (Int.castAddHom ℂ).map_finsum
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

/-- The logarithmic-derivative boundary integral varies continuously along
the straight-line Rouché homotopy. -/
lemma continuous_circleIntegral_logDeriv_roucheHomotopy
    {f g : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hfg : ∀ z ∈ sphere c R, ‖g z‖ < ‖f z‖) :
    Continuous (fun t : Set.Icc (0 : ℝ) 1 ↦
      ∮ z in C(c, R), logDeriv (fun w ↦ f w + (t.1 : ℂ) * g w) z) := by
  let z : Set.Icc (0 : ℝ) 1 × ℝ → ℂ := fun p ↦ circleMap c R p.2
  have hzcont : Continuous z := (continuous_circleMap c R).comp continuous_snd
  have hzsphere : ∀ p, z p ∈ sphere c R := fun p ↦ by
    exact circleMap_mem_sphere c hR.le p.2
  have hzcb : ∀ p, z p ∈ closedBall c R :=
    fun p ↦ sphere_subset_closedBall (hzsphere p)
  have hfcont : Continuous (fun p ↦ f (z p)) :=
    hf.continuousOn.comp_continuous hzcont hzcb
  have hgcont : Continuous (fun p ↦ g (z p)) :=
    hg.continuousOn.comp_continuous hzcont hzcb
  have hdfcont : Continuous (fun p ↦ deriv f (z p)) :=
    hf.deriv.continuousOn.comp_continuous hzcont hzcb
  have hdgcont : Continuous (fun p ↦ deriv g (z p)) :=
    hg.deriv.continuousOn.comp_continuous hzcont hzcb
  have htcont : Continuous (fun p : Set.Icc (0 : ℝ) 1 × ℝ ↦ (p.1.1 : ℂ)) := by
    fun_prop
  have hdenom : ∀ p : Set.Icc (0 : ℝ) 1 × ℝ,
      f (z p) + (p.1.1 : ℂ) * g (z p) ≠ 0 := by
    intro p
    apply rouche_homotopy_ne_zero_on_sphere hfg p.1 (z p)
    exact hzsphere p
  have hcircder : Continuous (fun p : Set.Icc (0 : ℝ) 1 × ℝ ↦
      deriv (circleMap c R) p.2) := by
    simpa only [deriv_circleMap] using
      (((continuous_circleMap 0 R).comp continuous_snd).mul continuous_const)
  have hint : Continuous (Function.uncurry (fun t : Set.Icc (0 : ℝ) 1 ↦ fun θ : ℝ ↦
      deriv (circleMap c R) θ *
        ((deriv f (circleMap c R θ) + (t.1 : ℂ) * deriv g (circleMap c R θ)) /
          (f (circleMap c R θ) + (t.1 : ℂ) * g (circleMap c R θ))))) := by
    exact hcircder.mul
      ((hdfcont.add (htcont.mul hdgcont)).div (hfcont.add (htcont.mul hgcont)) hdenom)
  have hcont := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := MeasureTheory.volume) hint 0 (2 * Real.pi)
  convert hcont using 1
  funext t
  rw [circleIntegral]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [logDeriv_apply]
  have hd : HasDerivAt (fun w ↦ f w + (t.1 : ℂ) * g w)
      (deriv f (circleMap c R θ) + (t.1 : ℂ) * deriv g (circleMap c R θ))
      (circleMap c R θ) :=
    (hf (circleMap c R θ) (hzcb (t, θ))).differentiableAt.hasDerivAt.add
      ((hg (circleMap c R θ) (hzcb (t, θ))).differentiableAt.hasDerivAt.const_mul
        (t.1 : ℂ))
  rw [hd.deriv]
  rfl

/-- **Rouché's theorem on a closed disk.** If `f` and `g` are holomorphic on
a neighborhood of the closed disk and `‖g‖ < ‖f‖` on its boundary, then `f`
and `f + g` have the same number of zeros in the disk, counted with
multiplicity.

`circleIntegral_logDeriv_eq_divisor_sum` above supplies the argument principle
for each member of the homotopy.  The remaining bridge is invariance of its
boundary integral under a boundary-nonvanishing holomorphic homotopy.  One
concrete route is continuity in the homotopy parameter: the preceding identity
puts every value in the discrete lattice `(2 * π * I) • ℤ`, so connectedness of
`[0, 1]` makes the value constant.

`rouche_homotopy_analyticOnNhd_and_ne_zero` proves the complete analytic and
boundary input for the standard straight-line homotopy. -/
theorem zeroCountInClosedBall_add_eq
    {f g : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hfg : ∀ z ∈ sphere c R, ‖g z‖ < ‖f z‖) :
    zeroCountInClosedBall (f + g) c R = zeroCountInClosedBall f c R := by
  let C : ℂ := 2 * Real.pi * I
  let N : Set.Icc (0 : ℝ) 1 → ℤ := fun t ↦
    zeroCountInClosedBall (fun z ↦ f z + (t.1 : ℂ) * g z) c R
  let H : Set.Icc (0 : ℝ) 1 → ℂ := fun t ↦
    ∮ z in C(c, R), logDeriv (fun w ↦ f w + (t.1 : ℂ) * g w) z
  have hH : Continuous H :=
    continuous_circleIntegral_logDeriv_roucheHomotopy hR hf hg hfg
  have hHN : ∀ t, H t = (N t : ℂ) * C := by
    intro t
    have ht := rouche_homotopy_analyticOnNhd_and_ne_zero hf hg hfg t
    change (∮ z in C(c, R), logDeriv (fun w ↦ f w + (t.1 : ℂ) * g w) z) =
      (zeroCountInClosedBall (fun w ↦ f w + (t.1 : ℂ) * g w) c R : ℂ) *
        (2 * Real.pi * I)
    rw [circleIntegral_logDeriv_eq_divisor_sum hR ht.1 ht.2,
      intCast_zeroCountInClosedBall]
  let K : Set.Icc (0 : ℝ) 1 → AddSubgroup.zmultiples C := fun t ↦
    ⟨H t, by
      rw [hHN t]
      exact ⟨N t, by dsimp; rw [zsmul_eq_mul]⟩⟩
  have hK : Continuous K := by
    apply Continuous.subtype_mk hH
  have hconst : K (⟨1, by simp⟩ : Set.Icc (0 : ℝ) 1) =
      K (⟨0, by simp⟩ : Set.Icc (0 : ℝ) 1) :=
    PreconnectedSpace.constant (by infer_instance) hK
  have hmul : (N (⟨1, by simp⟩ : Set.Icc (0 : ℝ) 1) : ℂ) * C =
      (N (⟨0, by simp⟩ : Set.Icc (0 : ℝ) 1) : ℂ) * C := by
    rw [← hHN, ← hHN]
    exact congrArg Subtype.val hconst
  have hC : C ≠ 0 := by
    simp [C, Complex.I_ne_zero, Real.pi_ne_zero]
  have hcast : (N (⟨1, by simp⟩ : Set.Icc (0 : ℝ) 1) : ℂ) =
      (N (⟨0, by simp⟩ : Set.Icc (0 : ℝ) 1) : ℂ) :=
    mul_right_cancel₀ hC hmul
  have hN : N (⟨1, by simp⟩ : Set.Icc (0 : ℝ) 1) =
      N (⟨0, by simp⟩ : Set.Icc (0 : ℝ) 1) := by
    exact_mod_cast hcast
  simpa [N, Pi.add_apply] using hN

end ConstructionTargets.Rouche
