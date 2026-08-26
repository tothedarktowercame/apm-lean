import Mathlib

/-!
# APM a95J04 — meromorphic continuation past a circle of convergence

## Statement repairs

None.

## Encoding questions

None. The extension uses Mathlib's genuine `MeromorphicOn` predicate and its
integer-valued `meromorphicOrderAt`; a pole is an order strictly below zero
and a simple pole has order `-1`. The coefficient sequence is pinned to `f`
by the power-series sum on the unit disk. Radius exactly one is expressed by
absolute convergence at every nonnegative radius below one and failure of
absolute convergence at every radius above one.
-/

open Complex Metric Set Filter
open scoped Topology

noncomputable section

/-- A pole of `f` in the closed unit disk must lie on its boundary when `f`
is holomorphic in the open disk.  This isolates the geometric reduction used
by both parts of the theorem. -/
lemma apm_a95J04_pole_mem_sphere_of_mem_closedBall
    {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hz : z ∈ closedBall (0 : ℂ) 1)
    (hpole : meromorphicOrderAt f z < 0) :
    z ∈ sphere (0 : ℂ) 1 := by
  rw [mem_closedBall, dist_zero_right] at hz
  rw [mem_sphere, dist_zero_right]
  apply le_antisymm hz
  by_contra hnot
  have hzball : z ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball, dist_zero_right]
    exact not_le.mp hnot
  have han : AnalyticAt ℂ f z := hf.analyticAt (isOpen_ball.mem_nhds hzball)
  exact (not_lt_of_ge han.meromorphicOrderAt_nonneg) hpole

/-- Meromorphy makes the boundary-pole set finite.  Restricting the locally
finite divisor to the compact unit sphere exposes this directly through
`locallyFinsuppWithin.finiteSupport`. -/
lemma apm_a95J04_boundary_poles_finite
    {D : Set ℂ} (hDcontains : closedBall (0 : ℂ) 1 ⊆ D)
    {f : ℂ → ℂ} (hmero : MeromorphicOn f D) :
    {z : ℂ | z ∈ sphere (0 : ℂ) 1 ∧ meromorphicOrderAt f z < 0}.Finite := by
  let div := MeromorphicOn.divisor f D
  have hsD : sphere (0 : ℂ) 1 ⊆ D :=
    sphere_subset_closedBall.trans hDcontains
  let ds := div.restrict hsD
  apply (ds.finiteSupport (isCompact_sphere (0 : ℂ) 1)).subset
  intro z hz
  change ds z ≠ 0
  rw [Function.locallyFinsuppWithin.restrict_apply]
  simp only [hz.1, if_true, div, MeromorphicOn.divisor_apply hmero (hsD hz.1)]
  intro hzero
  rw [WithTop.untop₀_eq_zero] at hzero
  rcases hzero with hzero | htop
  · exact (not_lt_of_ge (by rw [hzero])) hz.2
  · exact (not_lt_of_ge (by rw [htop]; exact le_top)) hz.2

/-- Why this unblocks `apm_a95j04`: it identifies the frozen coefficient
sequence with the genuine Taylor coefficients of `f`, allowing analytic
continuation results to control the original `a n`. -/
theorem apm_a95J04_bridge_taylor_coefficients
    (f : ℂ → ℂ) (a : ℕ → ℂ)
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hseries : ∀ z ∈ ball (0 : ℂ) 1,
      HasSum (fun n ↦ a n * z ^ n) (f z)) :
    ∀ n : ℕ, a n = (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0 := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ a
  have hp : HasFPowerSeriesAt f p 0 := by
    rw [hasFPowerSeriesAt_iff]
    filter_upwards [ball_mem_nhds (0 : ℂ) zero_lt_one] with z hz
    simpa [p, FormalMultilinearSeries.coeff_ofScalars, mul_comm] using hseries z hz
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := by simp
  have ht := (hf.analyticAt (isOpen_ball.mem_nhds h0)).hasFPowerSeriesAt
  have heq := hp.eq_formalMultilinearSeries ht
  intro n
  have hn := congrArg (fun q : FormalMultilinearSeries ℂ ℂ ℂ ↦ q.coeff n) heq
  simpa [p, FormalMultilinearSeries.coeff_ofScalars, div_eq_inv_mul] using hn

/-- Why this unblocks `apm_a95j04`: once `f` is holomorphic on a disk larger
than the unit disk and `a` is its Taylor sequence, this supplies the exact
absolute-convergence contradiction to `hradius_gt`. -/
theorem apm_a95J04_bridge_absolute_convergence
    (f : ℂ → ℂ) (a : ℕ → ℂ) (R r : ℝ)
    (hf : DifferentiableOn ℂ f (ball 0 R))
    (ha : ∀ n : ℕ, a n = (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0)
    (hr0 : 0 ≤ r) (hrR : r < R) :
    Summable (fun n ↦ ‖a n‖ * r ^ n) := by
  obtain ⟨s, hrs, hsR⟩ := exists_between hrR
  have hs0 : 0 < s := lt_of_le_of_lt hr0 hrs
  lift s to NNReal using hs0.le with s₀ hs₀
  let p : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ
      (fun n ↦ iteratedDeriv n f 0 / n.factorial)
  have hzero : (0 : ℂ) ∈ ball (0 : ℂ) R := by
    simp [lt_of_le_of_lt hr0 hrR]
  obtain ⟨t, ht⟩ := (hf.analyticAt (isOpen_ball.mem_nhds hzero)).hasFPowerSeriesAt
  have hc := (hf.mono (Metric.closedBall_subset_ball hsR)).hasFPowerSeriesOnBall hs0
  have hp : HasFPowerSeriesOnBall f p 0 s₀ := by
    exact ht.exchange_radius hc
  let r₀ : NNReal := ⟨r, hr0⟩
  have hrp : (r₀ : ENNReal) < p.radius :=
    lt_of_lt_of_le (by exact_mod_cast hrs) hp.r_le
  have herenorm : ‖(r : ℂ)‖ₑ = (r₀ : ENNReal) := by
    rw [enorm_eq_nnnorm]
    congr 1
    apply NNReal.eq
    simp [r₀, abs_of_nonneg hr0]
  have hrsum := p.summable_norm_apply
    (x := (r : ℂ)) (mem_eball_zero_iff.mpr (by simpa [herenorm] using hrp))
  convert hrsum using 1 with n
  simp [p, ha, div_eq_inv_mul, abs_of_nonneg hr0, mul_comm]

/-- Normalizing the point values of a meromorphic continuation removes the
removable-singularity obstruction.  If there are no boundary poles, the
normalized continuation is analytic at every point of the closed unit disk. -/
lemma apm_a95J04_normalized_analyticAt_on_closedBall
    (D : Set ℂ) (hDcontains : closedBall (0 : ℂ) 1 ⊆ D)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (ball 0 1))
    (hmero : MeromorphicOn f D)
    (hnopole : ∀ ζ ∈ sphere (0 : ℂ) 1,
      ¬meromorphicOrderAt f ζ < 0) :
    ∀ z ∈ closedBall (0 : ℂ) 1,
      AnalyticAt ℂ (toMeromorphicNFOn f D) z := by
  intro z hz
  have hzD : z ∈ D := hDcontains hz
  have hnf : MeromorphicNFAt (toMeromorphicNFOn f D) z :=
    meromorphicNFOn_toMeromorphicNFOn f D hzD
  rw [← hnf.meromorphicOrderAt_nonneg_iff_analyticAt]
  rw [meromorphicOrderAt_toMeromorphicNFOn hmero hzD]
  rw [mem_closedBall, dist_zero_right] at hz
  rcases hz.eq_or_lt with hzsphere | hzball
  · exact not_lt.mp (hnopole z (by simpa [mem_sphere, dist_zero_right] using hzsphere))
  · have han := hf.analyticAt
      (isOpen_ball.mem_nhds (by simpa [mem_ball, dist_zero_right] using hzball))
    exact han.meromorphicOrderAt_nonneg

lemma apm_a95J04_ball_subset_thickening_closedBall
    {δ : ℝ} (hδ : 0 < δ) :
    ball (0 : ℂ) (1 + δ) ⊆ thickening δ (closedBall (0 : ℂ) 1) := by
  intro z hz
  by_cases hzin : z ∈ closedBall (0 : ℂ) 1
  · exact (Metric.ball_subset_thickening hzin δ) (by simpa using hδ)
  · rw [Metric.mem_thickening_iff]
    have hz1 : 1 < ‖z‖ := by
      simpa [mem_closedBall, dist_zero_right, not_le] using hzin
    have hz0 : ‖z‖ ≠ 0 := ne_of_gt (lt_trans zero_lt_one hz1)
    let w : ℂ := (‖z‖ : ℂ)⁻¹ * z
    refine ⟨w, ?_, ?_⟩
    · simp [w, mem_closedBall, dist_zero_right, hz0]
    · rw [mem_ball, dist_zero_right] at hz
      have hnorm : ‖z - w‖ = ‖z‖ - 1 := by
        rw [show z - w = ((1 : ℂ) - (‖z‖ : ℂ)⁻¹) * z by ring]
        rw [norm_mul]
        have hcoef : ‖(1 : ℂ) - (‖z‖ : ℂ)⁻¹‖ = 1 - ‖z‖⁻¹ := by
          have hcast : ((‖z‖⁻¹ : ℝ) : ℂ) = (‖z‖ : ℂ)⁻¹ := by norm_cast
          have heq : (1 : ℂ) - (‖z‖ : ℂ)⁻¹ = ((1 - ‖z‖⁻¹ : ℝ) : ℂ) := by
            rw [← hcast]
            norm_cast
          rw [heq, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (sub_nonneg.mpr
              ((inv_le_one₀ (lt_trans zero_lt_one hz1)).2 hz1.le))]
        rw [hcoef]
        field_simp
      rw [dist_eq, hnorm]
      exact sub_lt_iff_lt_add.mpr (by simpa [add_comm] using hz)

/-- The normalized continuation is holomorphic on a uniformly larger disk. -/
lemma apm_a95J04_normalized_holomorphic_past_circle
    (D : Set ℂ) (hDcontains : closedBall (0 : ℂ) 1 ⊆ D)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (ball 0 1))
    (hmero : MeromorphicOn f D)
    (hnopole : ∀ ζ ∈ sphere (0 : ℂ) 1,
      ¬meromorphicOrderAt f ζ < 0) :
    ∃ R : ℝ, 1 < R ∧
      DifferentiableOn ℂ (toMeromorphicNFOn f D) (ball 0 R) := by
  let U : Set ℂ := {z | AnalyticAt ℂ (toMeromorphicNFOn f D) z}
  have hUopen : IsOpen U := isOpen_analyticAt ℂ (toMeromorphicNFOn f D)
  have hsub : closedBall (0 : ℂ) 1 ⊆ U :=
    apm_a95J04_normalized_analyticAt_on_closedBall D hDcontains f hf hmero hnopole
  obtain ⟨δ, hδ, hthick⟩ :=
    (isCompact_closedBall (0 : ℂ) 1).exists_thickening_subset_open hUopen hsub
  refine ⟨1 + δ, by linarith, ?_⟩
  intro z hz
  have hzU : z ∈ U := hthick (apm_a95J04_ball_subset_thickening_closedBall hδ hz)
  exact hzU.differentiableAt.differentiableWithinAt

lemma apm_a95J04_toMeromorphicNFOn_eqOn_ball
    (D : Set ℂ) (hDcontains : closedBall (0 : ℂ) 1 ⊆ D)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (ball 0 1))
    (hmero : MeromorphicOn f D) :
    Set.EqOn (toMeromorphicNFOn f D) f (ball (0 : ℂ) 1) := by
  intro z hz
  have hzD : z ∈ D := hDcontains (ball_subset_closedBall hz)
  have han : AnalyticAt ℂ f z := hf.analyticAt (isOpen_ball.mem_nhds hz)
  simp [toMeromorphicNFOn, hmero, hzD, toMeromorphicNFAt_eq_self.2 han.meromorphicNFAt]

/-- A meromorphic germ of order `-1` is an analytic germ plus one simple
principal part.  This is the local cancellation interface needed before the
finite boundary-pole subtraction. -/
lemma apm_a95J04_simple_pole_local_decomposition
    {F : ℂ → ℂ} {ζ : ℂ} (hF : MeromorphicAt F ζ)
    (horder : meromorphicOrderAt F ζ = (-1 : ℤ)) :
    ∃ c : ℂ, ∃ H : ℂ → ℂ, AnalyticAt ℂ H ζ ∧
      F =ᶠ[𝓝[≠] ζ] fun z ↦ H z + c / (z - ζ) := by
  obtain ⟨q, hq, hq0, hFq⟩ := (meromorphicOrderAt_eq_int_iff hF).1 horder
  let q0 : ℂ → ℂ := fun t ↦ q (t - (-ζ))
  have hq0an : AnalyticAt ℂ q0 0 := by
    simpa [q0] using hq.comp_sub (-ζ)
  obtain ⟨H0, hH0, hTaylor⟩ := hq0an.exists_eq_sum_add_pow_mul 1
  let H : ℂ → ℂ := fun z ↦ H0 (z - ζ)
  have hHan : AnalyticAt ℂ H ζ := by
    simpa [H] using hH0.comp_sub ζ
  refine ⟨q ζ, H, hHan, ?_⟩
  filter_upwards [hFq, self_mem_nhdsWithin] with z hzF hz
  have hqTaylor : q z = q ζ + (z - ζ) * H z := by
    have := hTaylor (z - ζ)
    simpa [q0, H] using this
  rw [hzF, hqTaylor]
  have hne : z - ζ ≠ 0 := sub_ne_zero.mpr hz
  simp only [zpow_neg, zpow_one, smul_eq_mul, div_eq_mul_inv]
  field_simp
  ring

/-- Taylor series of a simple principal part centered at a unit-circle point. -/
lemma apm_a95J04_hasSum_simple_principal_part
    {c ζ z : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1)
    (hz : z ∈ ball (0 : ℂ) 1) :
    HasSum (fun n : ℕ ↦ (-c * (ζ ^ (n + 1))⁻¹) * z ^ n)
      (c / (z - ζ)) := by
  have hζ0 : ζ ≠ 0 := by
    intro h
    subst ζ
    rw [mem_sphere, dist_zero_right] at hζ
    norm_num at hζ
  have hzeb : z ∈ Metric.eball (0 : ℂ) ‖ζ‖ₑ := by
    rw [mem_eball_zero_iff]
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm, ENNReal.coe_lt_coe]
    exact_mod_cast (show ‖z‖ < ‖ζ‖ by
      rw [show ‖ζ‖ = 1 by simpa [mem_sphere, dist_zero_right] using hζ]
      simpa [mem_ball, dist_zero_right] using hz)
  have hs := (Complex.one_div_sub_hasFPowerSeriesOnBall_zero hζ0).hasSum hzeb
  have hscaled := hs.const_smul (-c)
  convert hscaled using 1 with n
  · simp [mul_comm, mul_left_comm]
  · simp only [zero_add, smul_eq_mul, div_eq_mul_inv]
    rw [show ζ - z = -(z - ζ) by ring, inv_neg]
    ring

lemma apm_a95J04_norm_simple_principal_part_coeff
    {c ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1) (n : ℕ) :
    ‖-c * (ζ ^ (n + 1))⁻¹‖ = ‖c‖ := by
  rw [norm_mul, norm_neg, norm_inv, norm_pow]
  have hnorm : ‖ζ‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hζ
  simp [hnorm]

lemma apm_a95J04_norm_sum_simple_principal_part_coeff
    {P : Finset ℂ} {c : ℂ → ℂ}
    (hP : ∀ ζ ∈ P, ζ ∈ sphere (0 : ℂ) 1) (n : ℕ) :
    ‖∑ ζ ∈ P, -c ζ * (ζ ^ (n + 1))⁻¹‖ ≤ ∑ ζ ∈ P, ‖c ζ‖ := by
  refine (norm_sum_le _ _).trans ?_
  gcongr with ζ hζ
  exact le_of_eq (apm_a95J04_norm_simple_principal_part_coeff (hP ζ hζ) n)

/-- Subtracting a finite family of locally correct simple principal parts
leaves a germ of nonnegative order. -/
lemma apm_a95J04_finite_principal_parts_order_nonneg
    {F : ℂ → ℂ} {K : Set ℂ} {P : Finset ℂ} {c : ℂ → ℂ}
    (hFmero : ∀ z ∈ K, MeromorphicAt F z)
    (hlocal : ∀ ζ ∈ P, ∃ H : ℂ → ℂ, AnalyticAt ℂ H ζ ∧
      F =ᶠ[𝓝[≠] ζ] fun z ↦ H z + c ζ / (z - ζ))
    (hFnonneg : ∀ z ∈ K, z ∉ P → 0 ≤ meromorphicOrderAt F z) :
    ∀ z ∈ K, 0 ≤ meromorphicOrderAt
      (fun w ↦ F w - ∑ ζ ∈ P, c ζ / (w - ζ)) z := by
  intro z hzK
  by_cases hzP : z ∈ P
  · obtain ⟨H, hHan, hlocalz⟩ := hlocal z hzP
    let T : ℂ → ℂ := fun w ↦ ∑ ζ ∈ P.erase z, c ζ / (w - ζ)
    have hTan : AnalyticAt ℂ T z := by
      apply Finset.analyticAt_fun_sum
      intro ζ hζ
      have hne : z ≠ ζ := (Finset.mem_erase.mp hζ).1.symm
      apply AnalyticAt.div analyticAt_const
        ((analyticAt_id.sub analyticAt_const))
      exact sub_ne_zero.mpr hne
    rw [meromorphicOrderAt_congr]
    · exact (hHan.sub hTan).meromorphicOrderAt_nonneg
    · filter_upwards [hlocalz, self_mem_nhdsWithin] with w hw hwne
      have hsum : (∑ ζ ∈ P, c ζ / (w - ζ)) = c z / (w - z) + T w := by
        rw [← Finset.sum_erase_add _ _ hzP]
        simp [T, add_comm]
      simp only [hsum, hw]
      change H w + c z / (w - z) - (c z / (w - z) + T w) = H w - T w
      ring
  · let S : ℂ → ℂ := fun w ↦ ∑ ζ ∈ P, c ζ / (w - ζ)
    have hSan : AnalyticAt ℂ S z := by
      apply Finset.analyticAt_fun_sum
      intro ζ hζ
      have hne : z ≠ ζ := fun h ↦ hzP (h ▸ hζ)
      apply AnalyticAt.div analyticAt_const
        ((analyticAt_id.sub analyticAt_const))
      exact sub_ne_zero.mpr hne
    have hadd := meromorphicOrderAt_add (hFmero z hzK) hSan.neg.meromorphicAt
    have hmin : 0 ≤ min (meromorphicOrderAt F z)
        (meromorphicOrderAt (-S) z) := by
      simp only [le_min_iff]
      exact ⟨hFnonneg z hzK hzP, hSan.neg.meromorphicOrderAt_nonneg⟩
    exact hmin.trans (by simpa [S, sub_eq_add_neg] using hadd)

/-- Choose all boundary simple principal parts simultaneously and cancel every
negative order on the closed disk. -/
lemma apm_a95J04_exists_finite_principal_parts_order_nonneg
    (D : Set ℂ) (hDcontains : closedBall (0 : ℂ) 1 ⊆ D)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (ball 0 1))
    (hmero : MeromorphicOn f D)
    (hsimple : ∀ ζ ∈ sphere (0 : ℂ) 1,
      meromorphicOrderAt f ζ < 0 → meromorphicOrderAt f ζ = (-1 : ℤ)) :
    ∃ (P : Finset ℂ) (c : ℂ → ℂ),
      (∀ ζ, ζ ∈ P ↔ ζ ∈ sphere (0 : ℂ) 1 ∧ meromorphicOrderAt f ζ < 0) ∧
      ∀ z ∈ closedBall (0 : ℂ) 1, 0 ≤ meromorphicOrderAt
        (fun w ↦ toMeromorphicNFOn f D w - ∑ ζ ∈ P, c ζ / (w - ζ)) z := by
  classical
  let poleSet : Set ℂ :=
    {z | z ∈ sphere (0 : ℂ) 1 ∧ meromorphicOrderAt f z < 0}
  have hpoleFinite : poleSet.Finite :=
    apm_a95J04_boundary_poles_finite hDcontains hmero
  let P : Finset ℂ := hpoleFinite.toFinset
  have hP : ∀ ζ, ζ ∈ P ↔
      ζ ∈ sphere (0 : ℂ) 1 ∧ meromorphicOrderAt f ζ < 0 := by
    intro ζ
    simp [P, poleSet]
  let F := toMeromorphicNFOn f D
  have hex : ∀ ζ : ℂ, ∃ c : ℂ, ζ ∈ P →
      ∃ H : ℂ → ℂ, AnalyticAt ℂ H ζ ∧
        F =ᶠ[𝓝[≠] ζ] fun z ↦ H z + c / (z - ζ) := by
    intro ζ
    by_cases hζP : ζ ∈ P
    · have hzD : ζ ∈ D := hDcontains (sphere_subset_closedBall (hP ζ |>.1 hζP).1)
      have hFmero : MeromorphicAt F ζ :=
        (meromorphicNFOn_toMeromorphicNFOn f D hzD).meromorphicAt
      have horder : meromorphicOrderAt F ζ = (-1 : ℤ) := by
        rw [meromorphicOrderAt_toMeromorphicNFOn hmero hzD]
        exact hsimple ζ (hP ζ |>.1 hζP).1 (hP ζ |>.1 hζP).2
      obtain ⟨c, H, hH, heq⟩ :=
        apm_a95J04_simple_pole_local_decomposition hFmero horder
      exact ⟨c, fun _ ↦ ⟨H, hH, heq⟩⟩
    · exact ⟨0, fun h ↦ (hζP h).elim⟩
  choose c hc using hex
  refine ⟨P, c, hP, ?_⟩
  apply apm_a95J04_finite_principal_parts_order_nonneg
  · intro z hz
    exact (meromorphicNFOn_toMeromorphicNFOn f D (hDcontains hz)).meromorphicAt
  · intro ζ hζ
    exact hc ζ hζ
  · intro z hz hnot
    have hzD : z ∈ D := hDcontains hz
    rw [meromorphicOrderAt_toMeromorphicNFOn hmero hzD]
    by_contra hneg
    have hlt : meromorphicOrderAt f z < 0 := lt_of_not_ge hneg
    have hzSphere := apm_a95J04_pole_mem_sphere_of_mem_closedBall hf hz hlt
    exact hnot ((hP z).2 ⟨hzSphere, hlt⟩)

lemma apm_a95J04_normalized_holomorphic_of_order_nonneg
    (D : Set ℂ) (hDcontains : closedBall (0 : ℂ) 1 ⊆ D)
    (G : ℂ → ℂ) (hGmero : MeromorphicOn G D)
    (horder : ∀ z ∈ closedBall (0 : ℂ) 1,
      0 ≤ meromorphicOrderAt G z) :
    ∃ R : ℝ, 1 < R ∧
      DifferentiableOn ℂ (toMeromorphicNFOn G D) (ball 0 R) := by
  let U : Set ℂ := {z | AnalyticAt ℂ (toMeromorphicNFOn G D) z}
  have hUopen : IsOpen U := isOpen_analyticAt ℂ (toMeromorphicNFOn G D)
  have hsub : closedBall (0 : ℂ) 1 ⊆ U := by
    intro z hz
    have hzD : z ∈ D := hDcontains hz
    have hnf : MeromorphicNFAt (toMeromorphicNFOn G D) z :=
      meromorphicNFOn_toMeromorphicNFOn G D hzD
    change AnalyticAt ℂ (toMeromorphicNFOn G D) z
    rw [← hnf.meromorphicOrderAt_nonneg_iff_analyticAt]
    simpa [meromorphicOrderAt_toMeromorphicNFOn hGmero hzD] using horder z hz
  obtain ⟨δ, hδ, hthick⟩ :=
    (isCompact_closedBall (0 : ℂ) 1).exists_thickening_subset_open hUopen hsub
  refine ⟨1 + δ, by linarith, ?_⟩
  intro z hz
  have hzU : z ∈ U := hthick (apm_a95J04_ball_subset_thickening_closedBall hδ hz)
  exact hzU.differentiableAt.differentiableWithinAt

lemma apm_a95J04_corrected_simple_pole_decomposition
    (D : Set ℂ) (hDcontains : closedBall (0 : ℂ) 1 ⊆ D)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (ball 0 1))
    (hmero : MeromorphicOn f D)
    (hsimple : ∀ ζ ∈ sphere (0 : ℂ) 1,
      meromorphicOrderAt f ζ < 0 → meromorphicOrderAt f ζ = (-1 : ℤ)) :
    ∃ (P : Finset ℂ) (c : ℂ → ℂ) (g : ℂ → ℂ) (R : ℝ),
      1 < R ∧
      (∀ ζ, ζ ∈ P ↔ ζ ∈ sphere (0 : ℂ) 1 ∧ meromorphicOrderAt f ζ < 0) ∧
      DifferentiableOn ℂ g (ball 0 R) ∧
      ∀ z ∈ ball (0 : ℂ) 1,
        f z = g z + ∑ ζ ∈ P, c ζ / (z - ζ) := by
  classical
  obtain ⟨P, c, hP, horder⟩ :=
    apm_a95J04_exists_finite_principal_parts_order_nonneg D hDcontains f hf hmero hsimple
  let F := toMeromorphicNFOn f D
  let S : ℂ → ℂ := fun w ↦ ∑ ζ ∈ P, c ζ / (w - ζ)
  let G : ℂ → ℂ := fun w ↦ F w - S w
  have hFmero : MeromorphicOn F D :=
    (meromorphicNFOn_toMeromorphicNFOn f D).meromorphicOn
  have hSmero : MeromorphicOn S D := by
    apply MeromorphicOn.fun_sum
    intro ζ z hz
    fun_prop
  have hGmero : MeromorphicOn G D := hFmero.sub hSmero
  obtain ⟨R, hR, hgR⟩ :=
    apm_a95J04_normalized_holomorphic_of_order_nonneg D hDcontains G hGmero horder
  let g := toMeromorphicNFOn G D
  refine ⟨P, c, g, R, hR, hP, hgR, ?_⟩
  intro z hz
  have hzD : z ∈ D := hDcontains (ball_subset_closedBall hz)
  have hFeq : F z = f z :=
    apm_a95J04_toMeromorphicNFOn_eqOn_ball D hDcontains f hf hmero hz
  have hSan : AnalyticAt ℂ S z := by
    apply Finset.analyticAt_fun_sum
    intro ζ hζ
    have hζsphere := (hP ζ).1 hζ |>.1
    have hne : z ≠ ζ := by
      intro heq
      subst ζ
      rw [mem_ball, dist_zero_right] at hz
      rw [mem_sphere, dist_zero_right] at hζsphere
      linarith
    apply AnalyticAt.div analyticAt_const (analyticAt_id.sub analyticAt_const)
    exact sub_ne_zero.mpr hne
  have hGan : AnalyticAt ℂ G z := by
    apply AnalyticAt.sub
    · have hfan := hf.analyticAt (isOpen_ball.mem_nhds hz)
      apply hfan.congr
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw
      exact (apm_a95J04_toMeromorphicNFOn_eqOn_ball D hDcontains f hf hmero hw).symm
    · exact hSan
  have hgeq : g z = G z := by
    simp [g, toMeromorphicNFOn, hGmero, hzD,
      toMeromorphicNFAt_eq_self.2 hGan.meromorphicNFAt]
  simp [G, S, hFeq, hgeq]

theorem apm_a95j04
    (D : Set ℂ) (hDopen : IsOpen D) (hDconn : IsConnected D)
    (hDcontains : closedBall (0 : ℂ) 1 ⊆ D)
    (f : ℂ → ℂ) (a : ℕ → ℂ)
    (hf : DifferentiableOn ℂ f (ball 0 1))
    (hseries : ∀ z ∈ ball (0 : ℂ) 1,
      HasSum (fun n ↦ a n * z ^ n) (f z))
    (hradius_lt : ∀ r : ℝ, 0 ≤ r → r < 1 →
      Summable (fun n ↦ ‖a n‖ * r ^ n))
    (hradius_gt : ∀ r : ℝ, 1 < r →
      ¬Summable (fun n ↦ ‖a n‖ * r ^ n))
    (hmero : MeromorphicOn f D) :
    (∃ ζ ∈ sphere (0 : ℂ) 1, meromorphicOrderAt f ζ < 0) ∧
    ((∀ ζ ∈ sphere (0 : ℂ) 1,
        meromorphicOrderAt f ζ < 0 → meromorphicOrderAt f ζ = (-1 : ℤ)) →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, ‖a n‖ ≤ M) := by
  constructor
  · by_contra hno
    push_neg at hno
    let g := toMeromorphicNFOn f D
    obtain ⟨R, hR1, hgR⟩ :=
      apm_a95J04_normalized_holomorphic_past_circle D hDcontains f hf hmero
        (fun ζ hζ ↦ not_lt_of_ge (hno ζ hζ))
    have heq := apm_a95J04_toMeromorphicNFOn_eqOn_ball D hDcontains f hf hmero
    have hg1 : DifferentiableOn ℂ g (ball 0 1) :=
      hgR.mono (Metric.ball_subset_ball hR1.le)
    have hgseries : ∀ z ∈ ball (0 : ℂ) 1,
        HasSum (fun n ↦ a n * z ^ n) (g z) := by
      intro z hz
      simpa [g, heq hz] using hseries z hz
    obtain ⟨r, h1r, hrR⟩ := exists_between hR1
    have ha := apm_a95J04_bridge_taylor_coefficients g a hg1 hgseries
    exact (hradius_gt r h1r)
      (apm_a95J04_bridge_absolute_convergence g a R r hgR ha
        (le_trans zero_le_one h1r.le) hrR)
  · intro hsimple
    obtain ⟨P, c, g, R, hR, hP, hgR, hdecomp⟩ :=
      apm_a95J04_corrected_simple_pole_decomposition
        D hDcontains f hf hmero hsimple
    let p : ℕ → ℂ := fun n ↦ ∑ ζ ∈ P, -c ζ * (ζ ^ (n + 1))⁻¹
    let b : ℕ → ℂ := fun n ↦ a n - p n
    have hpseries : ∀ z ∈ ball (0 : ℂ) 1,
        HasSum (fun n ↦ p n * z ^ n) (∑ ζ ∈ P, c ζ / (z - ζ)) := by
      intro z hz
      have hs : HasSum
          (fun n : ℕ ↦ ∑ ζ ∈ P, (-c ζ * (ζ ^ (n + 1))⁻¹) * z ^ n)
          (∑ ζ ∈ P, c ζ / (z - ζ)) :=
        hasSum_sum (s := P) (fun ζ hζ ↦
          apm_a95J04_hasSum_simple_principal_part
            (c := c ζ) (hP ζ |>.1 hζ).1 hz)
      convert hs using 1 with n
      simp [p, Finset.sum_mul]
    have hbseries : ∀ z ∈ ball (0 : ℂ) 1,
        HasSum (fun n ↦ b n * z ^ n) (g z) := by
      intro z hz
      have hs := (hseries z hz).sub (hpseries z hz)
      have hsum : f z - ∑ ζ ∈ P, c ζ / (z - ζ) = g z := by
        rw [hdecomp z hz]
        ring
      rw [hsum] at hs
      simpa only [b, sub_mul] using hs
    have hg1 : DifferentiableOn ℂ g (ball 0 1) :=
      hgR.mono (Metric.ball_subset_ball hR.le)
    have hbTaylor := apm_a95J04_bridge_taylor_coefficients g b hg1 hbseries
    obtain ⟨r, h1r, hrR⟩ := exists_between hR
    have hbsum := apm_a95J04_bridge_absolute_convergence g b R r hgR hbTaylor
      (le_trans zero_le_one h1r.le) hrR
    let B : ℝ := ∑' n : ℕ, ‖b n‖ * r ^ n
    let C : ℝ := ∑ ζ ∈ P, ‖c ζ‖
    refine ⟨B + C, add_nonneg (tsum_nonneg fun _ ↦ by positivity)
      (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _), ?_⟩
    intro n
    calc
      ‖a n‖ = ‖b n + p n‖ := by simp [b]
      _ ≤ ‖b n‖ + ‖p n‖ := norm_add_le _ _
      _ ≤ B + C := add_le_add ?_ ?_
    · calc
        ‖b n‖ ≤ ‖b n‖ * r ^ n := by
          exact le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ h1r.le)
        _ ≤ B := hbsum.le_tsum n (fun _ _ ↦ by positivity)
    · exact apm_a95J04_norm_sum_simple_principal_part_coeff
        (fun ζ hζ ↦ (hP ζ).1 hζ |>.1) n
  /-
  CLOSER HOP 2 (2026-08-08): the new compiled lemma
  `apm_a95J04_pole_mem_sphere_of_mem_closedBall` proves that every pole in
  the closed unit disk is necessarily a boundary pole.  It uses Mathlib's
  previously missed `AnalyticAt.meromorphicOrderAt_nonneg`, so no normal-form
  conversion is needed for this localization.

  I also inspected the repaired exact proof history, `a97J05`, `a01J04`,
  Mathlib's Taylor-series and meromorphic normal-form/order APIs, and the
  repository lemma index.  The remaining first conjunct is the global step:
  assuming no boundary pole, turn meromorphy plus the compiled localization
  into holomorphy on a uniform disk of radius `r > 1`, identify `a n` with
  the Taylor coefficients using the pointwise `HasSum` family, and contradict
  `hradius_gt` via absolute Taylor convergence.

  For the second conjunct one must additionally prove finiteness of the
  boundary pole set, subtract all simple principal parts, extend the remainder
  holomorphically across the circle, and identify its Taylor coefficients.
  `a97J05` contains the single-pole removable-singularity construction but is
  itself still open at the pointwise-`HasSum` to power-series conversion, so
  it is not a reusable closed dependency.  No unproved intermediate assertion
  was introduced and the frozen theorem statement is unchanged.

  CLOSER HOP 3 goes beyond that boundary via Mathlib's meromorphic divisor.
  `apm_a95J04_boundary_poles_finite` restricts its locally finite support to
  the compact unit sphere, proving the boundary-pole set finite. Searches of
  `CanonicalDecomposition`, `FactorizedRational`, and
  `MeromorphicOn.extract_zeros_poles` found divisor factorization, but no
  additive simple-principal-part decomposition suitable for coefficient
  bounds. The pointwise `HasSum`-to-Taylor conversion and the larger-disk
  absolute-convergence argument remain open; the frozen statement is
  unchanged.
  -/
