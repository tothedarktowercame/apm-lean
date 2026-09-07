import Mathlib

/-!
# APM m00A05: A globally attracting scalar ODE equilibrium

## Statement repairs

None.

## Encoding questions

None. Solutions are global real-function representatives whose required
regularity and equation are restricted to `[0,∞)`. Uniqueness is consequently
stated with `Set.EqOn` on that interval, so irrelevant negative-time values are
not accidentally constrained.
-/

open Set Filter
open scoped Topology

noncomputable section

def apm_m00A05_isSolution (u₀ : ℝ) (u : ℝ → ℝ) : Prop :=
  ContinuousOn u (Ici 0) ∧
  DifferentiableOn ℝ u (Ioi 0) ∧
  u 0 = u₀ ∧
  ∀ t : ℝ, 0 < t → deriv u t + u t = Real.cos (u t)

/-- The autonomous vector field in the equation is globally Lipschitz. -/
lemma apm_m00A05_lipschitz_vectorField :
    LipschitzWith 2 (fun x : ℝ => Real.cos x - x) := by
  convert Real.lipschitzWith_cos.sub LipschitzWith.id using 1 <;> norm_num

/-- A solution in the frozen weak-regularity encoding satisfies the standard
`HasDerivAt` ODE on the interior of the half-line. -/
lemma apm_m00A05_hasDerivAt_of_isSolution {u₀ : ℝ} {u : ℝ → ℝ}
    (hu : apm_m00A05_isSolution u₀ u) {t : ℝ} (ht : 0 < t) :
    HasDerivAt u (Real.cos (u t) - u t) t := by
  have hd : DifferentiableAt ℝ u t :=
    (hu.2.1 t ht).differentiableAt (Ioi_mem_nhds ht)
  convert hd.hasDerivAt using 1
  linarith [hu.2.2.2 t ht]

/-- The apparently weak endpoint regularity in `apm_m00A05_isSolution` is
enough to recover the right derivative at zero.  This is the key interface to
Mathlib's closed-interval Gronwall theorem. -/
lemma apm_m00A05_hasDerivWithinAt_zero_of_isSolution {u₀ : ℝ} {u : ℝ → ℝ}
    (hu : apm_m00A05_isSolution u₀ u) :
    HasDerivWithinAt u (Real.cos (u 0) - u 0) (Ici 0) 0 := by
  apply hasDerivWithinAt_Ici_of_tendsto_deriv
  · exact hu.2.1
  · exact (hu.1 0 (by simp)).mono (Ioi_subset_Ici le_rfl)
  · exact self_mem_nhdsWithin
  · have hcont : Tendsto (fun t : ℝ => Real.cos (u t) - u t)
        (nhdsWithin 0 (Ioi 0)) (nhds (Real.cos (u 0) - u 0)) := by
      exact ((Real.continuous_cos.tendsto _).comp
        ((hu.1 0 (by simp)).mono (Ioi_subset_Ici le_rfl))).sub
        ((hu.1 0 (by simp)).mono (Ioi_subset_Ici le_rfl))
    apply hcont.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have heq := hu.2.2.2 t ht
    linarith

/-- Endpoint-safe global uniqueness for the frozen half-line encoding. -/
lemma apm_m00A05_solution_unique {u₀ : ℝ} {u v : ℝ → ℝ}
    (hu : apm_m00A05_isSolution u₀ u)
    (hv : apm_m00A05_isSolution u₀ v) : EqOn u v (Ici 0) := by
  intro t ht
  have huniq := ODE_solution_unique (K := 2) (v := fun _ x : ℝ => Real.cos x - x)
      (a := 0) (b := t) (f := u) (g := v)
      (fun _ => apm_m00A05_lipschitz_vectorField)
      (hu.1.mono Icc_subset_Ici_self) (by
        intro s hs
        rcases eq_or_lt_of_le hs.1 with rfl | hs0
        · exact apm_m00A05_hasDerivWithinAt_zero_of_isSolution hu
        · exact (apm_m00A05_hasDerivAt_of_isSolution hu hs0).hasDerivWithinAt)
      (hv.1.mono Icc_subset_Ici_self) (by
        intro s hs
        rcases eq_or_lt_of_le hs.1 with rfl | hs0
        · exact apm_m00A05_hasDerivWithinAt_zero_of_isSolution hv
        · exact (apm_m00A05_hasDerivAt_of_isSolution hv hs0).hasDerivWithinAt)
      (hu.2.2.1.trans hv.2.2.1.symm)
  exact huniq ⟨ht, le_rfl⟩

/-- Every fixed point of cosine gives the stationary comparison trajectory. -/
lemma apm_m00A05_const_isSolution {ξ : ℝ} (hξ : Real.cos ξ = ξ) :
    apm_m00A05_isSolution ξ (fun _ => ξ) := by
  refine ⟨continuous_const.continuousOn, differentiableOn_const ξ, rfl, ?_⟩
  intro t ht
  simp [hξ]

/-- An existing half-line solution can be restarted at any nonnegative time. -/
lemma apm_m00A05_shift_isSolution {u₀ : ℝ} {u : ℝ → ℝ}
    (hu : apm_m00A05_isSolution u₀ u) {t : ℝ} (ht : 0 ≤ t) :
    apm_m00A05_isSolution (u t) (fun s => u (s + t)) := by
  have hmaps : MapsTo (fun s : ℝ => s + t) (Ici 0) (Ici 0) := by
    intro s hs
    exact add_nonneg hs ht
  refine ⟨hu.1.comp (continuous_id.add continuous_const).continuousOn hmaps, ?_, by simp, ?_⟩
  · intro s hs
    have hst : 0 < s + t := add_pos_of_pos_of_nonneg hs ht
    exact (apm_m00A05_hasDerivAt_of_isSolution hu hst).comp_add_const s t
      |>.differentiableAt.differentiableWithinAt
  · intro s hs
    have hst : 0 < s + t := add_pos_of_pos_of_nonneg hs ht
    have hd := (apm_m00A05_hasDerivAt_of_isSolution hu hst).comp_add_const s t
    rw [hd.deriv]
    ring

/-- If a trajectory reaches an equilibrium, uniqueness forces it to remain
there forever. -/
lemma apm_m00A05_eq_of_eq_equilibrium {u₀ ξ : ℝ} {u : ℝ → ℝ}
    (hu : apm_m00A05_isSolution u₀ u) (hξ : Real.cos ξ = ξ)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hut : u t = ξ) : u (s + t) = ξ := by
  have hshift := apm_m00A05_shift_isSolution hu ht
  rw [hut] at hshift
  have heq := apm_m00A05_solution_unique hshift (apm_m00A05_const_isSolution hξ)
  exact heq hs

/-- The vector field points weakly toward every cosine fixed point from the
right.  The proof uses only the global `1`-Lipschitz estimate for cosine. -/
lemma apm_m00A05_vectorField_nonpos_of_fixed_le {ξ x : ℝ}
    (hξ : Real.cos ξ = ξ) (hξx : ξ ≤ x) : Real.cos x - x ≤ 0 := by
  have h := Real.abs_cos_sub_cos_le x ξ
  have hcos : Real.cos x - Real.cos ξ ≤ x - ξ := by
    calc
      Real.cos x - Real.cos ξ ≤ |Real.cos x - Real.cos ξ| := le_abs_self _
      _ ≤ |x - ξ| := h
      _ = x - ξ := abs_of_nonneg (sub_nonneg.mpr hξx)
  linarith

/-- The symmetric inward-pointing estimate on the left of a fixed point. -/
lemma apm_m00A05_vectorField_nonneg_of_le_fixed {ξ x : ℝ}
    (hξ : Real.cos ξ = ξ) (hxξ : x ≤ ξ) : 0 ≤ Real.cos x - x := by
  have h := Real.abs_cos_sub_cos_le ξ x
  have hcos : Real.cos ξ - Real.cos x ≤ ξ - x := by
    calc
      Real.cos ξ - Real.cos x ≤ |Real.cos ξ - Real.cos x| := le_abs_self _
      _ ≤ |ξ - x| := h
      _ = ξ - x := abs_of_nonneg (sub_nonneg.mpr hxξ)
  linarith

/-- A solution starting above an equilibrium never crosses it. -/
lemma apm_m00A05_fixed_le_solution {u₀ ξ : ℝ} {u : ℝ → ℝ}
    (hu : apm_m00A05_isSolution u₀ u) (hξ : Real.cos ξ = ξ)
    (hinit : ξ ≤ u₀) {t : ℝ} (ht : 0 ≤ t) : ξ ≤ u t := by
  by_contra hnot
  have hut : u t < ξ := lt_of_not_ge hnot
  have hcont : ContinuousOn u (Icc 0 t) := hu.1.mono Icc_subset_Ici_self
  have hmem : ξ ∈ Icc (u t) (u 0) := by
    exact ⟨hut.le, hu.2.2.1.symm ▸ hinit⟩
  obtain ⟨r, hr, hur⟩ := intermediate_value_Icc' ht hcont hmem
  have hstay := apm_m00A05_eq_of_eq_equilibrium hu hξ hr.1
      (sub_nonneg.mpr hr.2) hur
  have : u t = ξ := by simpa [sub_add_cancel] using hstay
  linarith

/-- A solution starting below an equilibrium never crosses it. -/
lemma apm_m00A05_solution_le_fixed {u₀ ξ : ℝ} {u : ℝ → ℝ}
    (hu : apm_m00A05_isSolution u₀ u) (hξ : Real.cos ξ = ξ)
    (hinit : u₀ ≤ ξ) {t : ℝ} (ht : 0 ≤ t) : u t ≤ ξ := by
  by_contra hnot
  have hut : ξ < u t := lt_of_not_ge hnot
  have hcont : ContinuousOn u (Icc 0 t) := hu.1.mono Icc_subset_Ici_self
  have hmem : ξ ∈ Icc (u 0) (u t) := by
    exact ⟨hu.2.2.1.symm ▸ hinit, hut.le⟩
  obtain ⟨r, hr, hur⟩ := intermediate_value_Icc ht hcont hmem
  have hstay := apm_m00A05_eq_of_eq_equilibrium hu hξ hr.1
      (sub_nonneg.mpr hr.2) hur
  have : u t = ξ := by simpa [sub_add_cancel] using hstay
  linarith

/-- Above an equilibrium, the trapped trajectory is antitone. -/
lemma apm_m00A05_antitoneOn_of_fixed_le_initial {u₀ ξ : ℝ} {u : ℝ → ℝ}
    (hu : apm_m00A05_isSolution u₀ u) (hξ : Real.cos ξ = ξ)
    (hinit : ξ ≤ u₀) : AntitoneOn u (Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0) hu.1
  · simpa only [interior_Ici] using hu.2.1
  · intro t ht
    rw [interior_Ici] at ht
    have htrap := apm_m00A05_fixed_le_solution hu hξ hinit ht.le
    rw [show deriv u t = Real.cos (u t) - u t by
      linarith [hu.2.2.2 t ht]]
    exact apm_m00A05_vectorField_nonpos_of_fixed_le hξ htrap

/-- Below an equilibrium, the trapped trajectory is monotone. -/
lemma apm_m00A05_monotoneOn_of_initial_le_fixed {u₀ ξ : ℝ} {u : ℝ → ℝ}
    (hu : apm_m00A05_isSolution u₀ u) (hξ : Real.cos ξ = ξ)
    (hinit : u₀ ≤ ξ) : MonotoneOn u (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hu.1
  · simpa only [interior_Ici] using hu.2.1
  · intro t ht
    rw [interior_Ici] at ht
    have htrap := apm_m00A05_solution_le_fixed hu hξ hinit ht.le
    rw [show deriv u t = Real.cos (u t) - u t by
      linarith [hu.2.2.2 t ht]]
    exact apm_m00A05_vectorField_nonneg_of_le_fixed hξ htrap

/-- Trapping and monotonicity already imply convergence to some finite real
limit; identifying that limit with the equilibrium is handled separately. -/
lemma apm_m00A05_exists_limit {u₀ ξ : ℝ} {u : ℝ → ℝ}
    (hu : apm_m00A05_isSolution u₀ u) (hξ : Real.cos ξ = ξ) :
    ∃ L : ℝ, Tendsto u atTop (nhds L) := by
  by_cases hinit : u₀ ≤ ξ
  · let w : ℝ → ℝ := fun t => u (max 0 t)
    have hwmono : Monotone w := by
      intro a b hab
      exact apm_m00A05_monotoneOn_of_initial_le_fixed hu hξ hinit
        (le_max_left 0 a) (le_max_left 0 b) (max_le_max le_rfl hab)
    have hw_bdd : BddAbove (range w) := by
      refine ⟨ξ, ?_⟩
      rintro _ ⟨t, rfl⟩
      exact apm_m00A05_solution_le_fixed hu hξ hinit (le_max_left 0 t)
    refine ⟨⨆ t, w t, ?_⟩
    apply (tendsto_atTop_ciSup hwmono hw_bdd).congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    simp [w, max_eq_right ht]
  · have hinit' : ξ ≤ u₀ := le_of_not_ge hinit
    let w : ℝ → ℝ := fun t => u (max 0 t)
    have hwanti : Antitone w := by
      intro a b hab
      exact apm_m00A05_antitoneOn_of_fixed_le_initial hu hξ hinit'
        (le_max_left 0 a) (le_max_left 0 b) (max_le_max le_rfl hab)
    have hw_bdd : BddBelow (range w) := by
      refine ⟨ξ, ?_⟩
      rintro _ ⟨t, rfl⟩
      exact apm_m00A05_fixed_le_solution hu hξ hinit' (le_max_left 0 t)
    refine ⟨⨅ t, w t, ?_⟩
    apply (tendsto_atTop_ciInf hwanti hw_bdd).congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    simp [w, max_eq_right ht]

/-- A finite limiting trajectory must limit at a zero of its autonomous vector
field.  Mean-value points on `[n,n+1]` make the derivative converge both to the
vector-field value at the limit and to zero. -/
lemma apm_m00A05_limit_is_fixed {u₀ L : ℝ} {u : ℝ → ℝ}
    (hu : apm_m00A05_isSolution u₀ u) (hL : Tendsto u atTop (nhds L)) :
    Real.cos L = L := by
  have hderiv : Tendsto (deriv u) atTop (nhds (Real.cos L - L)) := by
    have hfield : Tendsto (fun t => Real.cos (u t) - u t) atTop
        (nhds (Real.cos L - L)) :=
      ((Real.continuous_cos.tendsto L).comp hL).sub hL
    apply hfield.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    linarith [hu.2.2.2 t ht]
  have hmvt : ∀ n : ℕ, ∃ c : ℝ, c ∈ Ioo (n : ℝ) ((n : ℝ) + 1) ∧
      deriv u c = u ((n : ℝ) + 1) - u (n : ℝ) := by
    intro n
    have hcont : ContinuousOn u (Icc (n : ℝ) ((n : ℝ) + 1)) :=
      hu.1.mono (by intro x hx; exact le_trans (Nat.cast_nonneg n) hx.1)
    obtain ⟨c, hc, hdc⟩ := exists_deriv_eq_slope u (by linarith)
      hcont (hu.2.1.mono <| by
        intro x hx
        exact lt_of_le_of_lt (Nat.cast_nonneg n) hx.1)
    refine ⟨c, hc, ?_⟩
    simpa using hdc
  choose c hc hdc using hmvt
  have hc_top : Tendsto c atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (Ici_mem_atTop b)] with n hn
    exact hn.trans (hc n).1.le
  have hderiv_c : Tendsto (fun n => deriv u (c n)) atTop
      (nhds (Real.cos L - L)) := hderiv.comp hc_top
  have hn : Tendsto (fun n : ℕ => u (n : ℝ)) atTop (nhds L) :=
    hL.comp tendsto_natCast_atTop_atTop
  have hn1 : Tendsto (fun n : ℕ => u ((n : ℝ) + 1)) atTop (nhds L) :=
    hL.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hzero : Tendsto (fun n : ℕ => deriv u (c n)) atTop (nhds 0) := by
    convert (hn1.sub hn).congr'
      (Filter.Eventually.of_forall fun n => (hdc n).symm) using 1 <;> simp
  have : Real.cos L - L = 0 := tendsto_nhds_unique hderiv_c hzero
  exact sub_eq_zero.mp this

/-- Cosine has at most one real fixed point. -/
lemma apm_m00A05_fixed_unique {x y : ℝ}
    (hx : Real.cos x = x) (hy : Real.cos y = y) : x = y := by
  have hxI : x ∈ Icc 0 Real.pi := by
    have hxm : -1 ≤ x := by rw [← hx]; exact Real.neg_one_le_cos x
    have hxp : x ≤ 1 := by rw [← hx]; exact Real.cos_le_one x
    have hx0 : 0 ≤ x := by
      by_contra hn
      have hxneg : x < 0 := lt_of_not_ge hn
      have hcpos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by
        nlinarith [Real.pi_gt_three], by nlinarith [Real.pi_gt_three]⟩
      linarith
    exact ⟨hx0, hxp.trans (by nlinarith [Real.pi_gt_three])⟩
  have hyI : y ∈ Icc 0 Real.pi := by
    have hym : -1 ≤ y := by rw [← hy]; exact Real.neg_one_le_cos y
    have hyp : y ≤ 1 := by rw [← hy]; exact Real.cos_le_one y
    have hy0 : 0 ≤ y := by
      by_contra hn
      have hyneg : y < 0 := lt_of_not_ge hn
      have hcpos : 0 < Real.cos y := Real.cos_pos_of_mem_Ioo ⟨by
        nlinarith [Real.pi_gt_three], by nlinarith [Real.pi_gt_three]⟩
      linarith
    exact ⟨hy0, hyp.trans (by nlinarith [Real.pi_gt_three])⟩
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · have := Real.strictAntiOn_cos hxI hyI hxy
    linarith
  · exact hxy
  · have := Real.strictAntiOn_cos hyI hxI hyx
    linarith

/-- A uniform-duration Picard step from an arbitrary state.  Although the
vector field is unbounded, a ball whose radius grows with the centre gives the
same quarter-unit lifespan at every state; this is the non-Zeno input for
global continuation. -/
lemma apm_m00A05_uniform_picard_step_at (t₀ x₀ : ℝ) :
    ∃ u : ℝ → ℝ, u t₀ = x₀ ∧
      ∀ t ∈ Icc t₀ (t₀ + 1 / 4),
        HasDerivWithinAt u (Real.cos (u t) - u t) (Icc t₀ (t₀ + 1 / 4)) t := by
  let a : NNReal := ⟨|x₀| + 2, by positivity⟩
  let L : NNReal := ⟨2 * |x₀| + 3, by positivity⟩
  have hb : ∀ x ∈ Metric.closedBall x₀ (a : ℝ), ‖Real.cos x - x‖ ≤ (L : ℝ) := by
    intro x hx
    have hdist : |x - x₀| ≤ |x₀| + 2 := by
      simpa [a, Real.dist_eq] using hx
    have hxabs : |x| ≤ 2 * |x₀| + 2 := by
      calc
        |x| ≤ |x - x₀| + |x₀| := by
          simpa [sub_add_cancel] using abs_add_le (x - x₀) x₀
        _ ≤ 2 * |x₀| + 2 := by linarith
    calc
      ‖Real.cos x - x‖ ≤ ‖Real.cos x‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ 1 + |x| := by simpa using add_le_add_right (Real.abs_cos_le_one x) |x|
      _ ≤ (L : ℝ) := by simp [L]; linarith
  have hpl : IsPicardLindelof (fun _ : ℝ => fun x : ℝ => Real.cos x - x)
      (⟨t₀, by norm_num⟩ : Icc t₀ (t₀ + 1 / 4)) x₀ a 0 L 2 := by
    apply IsPicardLindelof.of_time_independent hb
      (apm_m00A05_lipschitz_vectorField.lipschitzOnWith)
    norm_num [a, L]
    nlinarith [abs_nonneg x₀]
  exact hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

lemma apm_m00A05_uniform_picard_step (x₀ : ℝ) :
    ∃ u : ℝ → ℝ, u 0 = x₀ ∧
      ∀ t ∈ Icc (0 : ℝ) (1 / 4 : ℝ),
        HasDerivWithinAt u (Real.cos (u t) - u t) (Icc 0 (1 / 4)) t := by
  simpa using apm_m00A05_uniform_picard_step_at 0 x₀

/-- A deterministic choice of the uniform Picard segment. -/
noncomputable def apm_m00A05_picardStep (t₀ x₀ : ℝ) : ℝ → ℝ :=
  Classical.choose (apm_m00A05_uniform_picard_step_at t₀ x₀)

lemma apm_m00A05_picardStep_start (t₀ x₀ : ℝ) :
    apm_m00A05_picardStep t₀ x₀ t₀ = x₀ :=
  (Classical.choose_spec (apm_m00A05_uniform_picard_step_at t₀ x₀)).1

lemma apm_m00A05_picardStep_hasDerivWithinAt (t₀ x₀ : ℝ) {t : ℝ}
    (ht : t ∈ Icc t₀ (t₀ + 1 / 4)) :
    HasDerivWithinAt (apm_m00A05_picardStep t₀ x₀)
      (Real.cos (apm_m00A05_picardStep t₀ x₀ t) -
        apm_m00A05_picardStep t₀ x₀ t)
      (Icc t₀ (t₀ + 1 / 4)) t :=
  (Classical.choose_spec (apm_m00A05_uniform_picard_step_at t₀ x₀)).2 t ht

/-- Quarter-unit time mesh used for the non-Zeno continuation. -/
def apm_m00A05_mesh (n : ℕ) : ℝ := n / 4

@[simp] lemma apm_m00A05_mesh_zero : apm_m00A05_mesh 0 = 0 := by
  simp [apm_m00A05_mesh]

lemma apm_m00A05_mesh_succ (n : ℕ) :
    apm_m00A05_mesh (n + 1) = apm_m00A05_mesh n + 1 / 4 := by
  norm_num [apm_m00A05_mesh]
  ring

lemma apm_m00A05_mesh_strictMono_step (n : ℕ) :
    apm_m00A05_mesh n < apm_m00A05_mesh (n + 1) := by
  rw [apm_m00A05_mesh_succ]
  norm_num

/-- States obtained by recursively taking the endpoint of each chosen Picard
segment. -/
noncomputable def apm_m00A05_picardState (u₀ : ℝ) : ℕ → ℝ
  | 0 => u₀
  | n + 1 => apm_m00A05_picardStep (apm_m00A05_mesh n)
      (apm_m00A05_picardState u₀ n) (apm_m00A05_mesh (n + 1))

@[simp] lemma apm_m00A05_picardState_zero (u₀ : ℝ) :
    apm_m00A05_picardState u₀ 0 = u₀ := rfl

lemma apm_m00A05_picardState_succ (u₀ : ℝ) (n : ℕ) :
    apm_m00A05_picardState u₀ (n + 1) =
      apm_m00A05_picardStep (apm_m00A05_mesh n)
        (apm_m00A05_picardState u₀ n) (apm_m00A05_mesh (n + 1)) := rfl

/-- Adjacent chosen segments agree at their shared mesh endpoint. -/
lemma apm_m00A05_picardStep_compatible (u₀ : ℝ) (n : ℕ) :
    apm_m00A05_picardStep (apm_m00A05_mesh (n + 1))
        (apm_m00A05_picardState u₀ (n + 1)) (apm_m00A05_mesh (n + 1)) =
      apm_m00A05_picardStep (apm_m00A05_mesh n)
        (apm_m00A05_picardState u₀ n) (apm_m00A05_mesh (n + 1)) := by
  rw [apm_m00A05_picardStep_start, ← apm_m00A05_picardState_succ]

lemma apm_m00A05_picardStep_continuousOn (t₀ x₀ : ℝ) :
    ContinuousOn (apm_m00A05_picardStep t₀ x₀) (Icc t₀ (t₀ + 1 / 4)) :=
  HasDerivWithinAt.continuousOn fun _ ht =>
    apm_m00A05_picardStep_hasDerivWithinAt t₀ x₀ ht

lemma apm_m00A05_picardStep_hasDerivAt (t₀ x₀ : ℝ) {t : ℝ}
    (ht : t ∈ Ioo t₀ (t₀ + 1 / 4)) :
    HasDerivAt (apm_m00A05_picardStep t₀ x₀)
      (Real.cos (apm_m00A05_picardStep t₀ x₀ t) -
        apm_m00A05_picardStep t₀ x₀ t) t :=
  (apm_m00A05_picardStep_hasDerivWithinAt t₀ x₀ ⟨ht.1.le, ht.2.le⟩).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

lemma apm_m00A05_picardSegment_hasDerivWithinAt (u₀ : ℝ) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (apm_m00A05_mesh n) (apm_m00A05_mesh (n + 1))) :
    HasDerivWithinAt
      (apm_m00A05_picardStep (apm_m00A05_mesh n) (apm_m00A05_picardState u₀ n))
      (Real.cos (apm_m00A05_picardStep (apm_m00A05_mesh n)
          (apm_m00A05_picardState u₀ n) t) -
        apm_m00A05_picardStep (apm_m00A05_mesh n)
          (apm_m00A05_picardState u₀ n) t)
      (Icc (apm_m00A05_mesh n) (apm_m00A05_mesh (n + 1))) t := by
  rw [apm_m00A05_mesh_succ] at ht ⊢
  exact apm_m00A05_picardStep_hasDerivWithinAt _ _ ht

/-- Index of the quarter-unit mesh interval containing a nonnegative time. -/
noncomputable def apm_m00A05_meshIndex (t : ℝ) : ℕ := ⌊4 * t⌋₊

lemma apm_m00A05_meshIndex_spec {t : ℝ} (ht : 0 ≤ t) :
    t ∈ Ico (apm_m00A05_mesh (apm_m00A05_meshIndex t))
      (apm_m00A05_mesh (apm_m00A05_meshIndex t + 1)) := by
  have hlo : (apm_m00A05_meshIndex t : ℝ) ≤ 4 * t := by
    exact Nat.floor_le (mul_nonneg (by norm_num) ht)
  have hhi : 4 * t < (apm_m00A05_meshIndex t : ℝ) + 1 := by
    exact Nat.lt_floor_add_one (4 * t)
  rw [mem_Ico, apm_m00A05_mesh_succ]
  constructor <;> simp [apm_m00A05_mesh] <;> nlinarith

lemma apm_m00A05_meshIndex_eq_of_mem_Ico {t : ℝ} {n : ℕ}
    (ht : t ∈ Ico (apm_m00A05_mesh n) (apm_m00A05_mesh (n + 1))) :
    apm_m00A05_meshIndex t = n := by
  rw [apm_m00A05_mesh_succ] at ht
  apply (Nat.floor_eq_iff (show 0 ≤ 4 * t by
    have hn : 0 ≤ apm_m00A05_mesh n := by
      exact div_nonneg (Nat.cast_nonneg n) (by norm_num)
    nlinarith [ht.1])).2
  simp [apm_m00A05_mesh] at ht ⊢
  constructor <;> nlinarith

@[simp] lemma apm_m00A05_meshIndex_zero : apm_m00A05_meshIndex 0 = 0 := by
  simp [apm_m00A05_meshIndex]

/-- The meshwise candidate obtained by evaluating the chosen segment containing
the requested nonnegative time.  Negative values are irrelevant to the frozen
solution predicate. -/
noncomputable def apm_m00A05_globalCandidate (u₀ : ℝ) (t : ℝ) : ℝ :=
  if 0 ≤ t then
    apm_m00A05_picardStep (apm_m00A05_mesh (apm_m00A05_meshIndex t))
      (apm_m00A05_picardState u₀ (apm_m00A05_meshIndex t)) t
  else u₀

lemma apm_m00A05_globalCandidate_of_nonneg (u₀ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    apm_m00A05_globalCandidate u₀ t =
      apm_m00A05_picardStep (apm_m00A05_mesh (apm_m00A05_meshIndex t))
        (apm_m00A05_picardState u₀ (apm_m00A05_meshIndex t)) t := by
  simp [apm_m00A05_globalCandidate, ht]

lemma apm_m00A05_globalCandidate_eq_segment_of_mem_Ico (u₀ : ℝ) {n : ℕ} {t : ℝ}
    (ht : t ∈ Ico (apm_m00A05_mesh n) (apm_m00A05_mesh (n + 1))) :
    apm_m00A05_globalCandidate u₀ t =
      apm_m00A05_picardStep (apm_m00A05_mesh n) (apm_m00A05_picardState u₀ n) t := by
  have ht0 : 0 ≤ t := (show 0 ≤ apm_m00A05_mesh n by
    exact div_nonneg (Nat.cast_nonneg n) (by norm_num)).trans ht.1
  rw [apm_m00A05_globalCandidate_of_nonneg u₀ ht0,
    apm_m00A05_meshIndex_eq_of_mem_Ico ht]

lemma apm_m00A05_globalCandidate_eq_segment_of_mem_Icc (u₀ : ℝ) {n : ℕ} {t : ℝ}
    (ht : t ∈ Icc (apm_m00A05_mesh n) (apm_m00A05_mesh (n + 1))) :
    apm_m00A05_globalCandidate u₀ t =
      apm_m00A05_picardStep (apm_m00A05_mesh n) (apm_m00A05_picardState u₀ n) t := by
  rcases ht.2.lt_or_eq with hlt | rfl
  · exact apm_m00A05_globalCandidate_eq_segment_of_mem_Ico u₀ ⟨ht.1, hlt⟩
  · rw [apm_m00A05_globalCandidate_eq_segment_of_mem_Ico u₀
        (n := n + 1) ⟨le_rfl, apm_m00A05_mesh_strictMono_step (n + 1)⟩]
    exact apm_m00A05_picardStep_compatible u₀ n

lemma apm_m00A05_globalCandidate_eventuallyEq_segment (u₀ : ℝ) {n : ℕ} {t : ℝ}
    (ht : t ∈ Ioo (apm_m00A05_mesh n) (apm_m00A05_mesh (n + 1))) :
    Filter.Eventually (fun s => apm_m00A05_globalCandidate u₀ s =
      apm_m00A05_picardStep (apm_m00A05_mesh n) (apm_m00A05_picardState u₀ n) s)
      (nhds t) := by
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact apm_m00A05_globalCandidate_eq_segment_of_mem_Ico u₀ ⟨hs.1.le, hs.2⟩

lemma apm_m00A05_globalCandidate_hasDerivAt_of_mem_Ioo (u₀ : ℝ) {n : ℕ} {t : ℝ}
    (ht : t ∈ Ioo (apm_m00A05_mesh n) (apm_m00A05_mesh (n + 1))) :
    HasDerivAt (apm_m00A05_globalCandidate u₀)
      (Real.cos (apm_m00A05_globalCandidate u₀ t) -
        apm_m00A05_globalCandidate u₀ t) t := by
  have hseg : HasDerivAt
      (apm_m00A05_picardStep (apm_m00A05_mesh n) (apm_m00A05_picardState u₀ n))
      (Real.cos (apm_m00A05_picardStep (apm_m00A05_mesh n)
          (apm_m00A05_picardState u₀ n) t) -
        apm_m00A05_picardStep (apm_m00A05_mesh n)
          (apm_m00A05_picardState u₀ n) t) t := by
    rw [apm_m00A05_mesh_succ] at ht
    exact apm_m00A05_picardStep_hasDerivAt _ _ ht
  have heq := apm_m00A05_globalCandidate_eventuallyEq_segment u₀ ht
  convert hseg.congr_of_eventuallyEq heq using 1
  rw [heq.self_of_nhds]

lemma apm_m00A05_globalCandidate_hasDerivWithinAt_segment (u₀ : ℝ) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (apm_m00A05_mesh n) (apm_m00A05_mesh (n + 1))) :
    HasDerivWithinAt (apm_m00A05_globalCandidate u₀)
      (Real.cos (apm_m00A05_globalCandidate u₀ t) -
        apm_m00A05_globalCandidate u₀ t)
      (Icc (apm_m00A05_mesh n) (apm_m00A05_mesh (n + 1))) t := by
  have hseg := apm_m00A05_picardSegment_hasDerivWithinAt u₀ n ht
  have heq : ∀ s ∈ Icc (apm_m00A05_mesh n) (apm_m00A05_mesh (n + 1)),
      apm_m00A05_globalCandidate u₀ s =
        apm_m00A05_picardStep (apm_m00A05_mesh n) (apm_m00A05_picardState u₀ n) s :=
    fun s hs => apm_m00A05_globalCandidate_eq_segment_of_mem_Icc u₀ hs
  convert hseg.congr_of_mem heq ht using 1
  rw [heq t ht]

lemma apm_m00A05_globalCandidate_hasDerivAt_mesh (u₀ : ℝ) (n : ℕ) :
    HasDerivAt (apm_m00A05_globalCandidate u₀)
      (Real.cos (apm_m00A05_globalCandidate u₀ (apm_m00A05_mesh (n + 1))) -
        apm_m00A05_globalCandidate u₀ (apm_m00A05_mesh (n + 1)))
      (apm_m00A05_mesh (n + 1)) := by
  let m := apm_m00A05_mesh (n + 1)
  let d := Real.cos (apm_m00A05_globalCandidate u₀ m) - apm_m00A05_globalCandidate u₀ m
  have hleft : HasDerivWithinAt (apm_m00A05_globalCandidate u₀) d (Iic m) m := by
    apply (apm_m00A05_globalCandidate_hasDerivWithinAt_segment u₀ n
      (t := m) ⟨(apm_m00A05_mesh_strictMono_step n).le, le_rfl⟩).mono_of_mem_nhdsWithin
    exact Icc_mem_nhdsLE (apm_m00A05_mesh_strictMono_step n)
  have hright : HasDerivWithinAt (apm_m00A05_globalCandidate u₀) d (Ici m) m := by
    apply (apm_m00A05_globalCandidate_hasDerivWithinAt_segment u₀ (n + 1)
      (t := m) ⟨le_rfl, (apm_m00A05_mesh_strictMono_step (n + 1)).le⟩).mono_of_mem_nhdsWithin
    exact Icc_mem_nhdsGE (apm_m00A05_mesh_strictMono_step (n + 1))
  rw [← hasDerivWithinAt_univ, ← Iic_union_Ici]
  exact hleft.union hright

lemma apm_m00A05_globalCandidate_hasDerivAt (u₀ : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (apm_m00A05_globalCandidate u₀)
      (Real.cos (apm_m00A05_globalCandidate u₀ t) -
        apm_m00A05_globalCandidate u₀ t) t := by
  let n := apm_m00A05_meshIndex t
  have hs := apm_m00A05_meshIndex_spec ht.le
  by_cases heq : t = apm_m00A05_mesh n
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · rw [hn, apm_m00A05_mesh_zero] at heq
      linarith
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
      rw [hk, Nat.succ_eq_add_one] at heq
      subst t
      exact apm_m00A05_globalCandidate_hasDerivAt_mesh u₀ k
  · apply apm_m00A05_globalCandidate_hasDerivAt_of_mem_Ioo u₀
    exact ⟨lt_of_le_of_ne hs.1 (Ne.symm heq), hs.2⟩

lemma apm_m00A05_globalCandidate_continuousOn (u₀ : ℝ) :
  ContinuousOn (apm_m00A05_globalCandidate u₀) (Ici 0) := by
  intro t ht
  change 0 ≤ t at ht
  rcases eq_or_lt_of_le ht with rfl | ht
  · have hright := apm_m00A05_globalCandidate_hasDerivWithinAt_segment u₀ 0
        (t := 0) (by simp [apm_m00A05_mesh])
    exact hright.continuousWithinAt.mono_of_mem_nhdsWithin
      (by simpa only [apm_m00A05_mesh_zero] using
        Icc_mem_nhdsGE (apm_m00A05_mesh_strictMono_step 0))
  · exact (apm_m00A05_globalCandidate_hasDerivAt u₀ ht).continuousAt.continuousWithinAt

@[simp] lemma apm_m00A05_globalCandidate_zero (u₀ : ℝ) :
    apm_m00A05_globalCandidate u₀ 0 = u₀ := by
  simp [apm_m00A05_globalCandidate, apm_m00A05_picardStep_start]

/-- Why this unblocks `apm_m00a05`: this is the missing globalization of the
local Picard--Lindelöf solutions for the globally Lipschitz autonomous vector
field.  It produces a single half-line representative in exactly the frozen
solution predicate; the endpoint-safe Gronwall argument recorded below then
supplies uniqueness. -/
theorem apm_m00A05_bridge_global_exists (u₀ : ℝ) :
    ∃ u : ℝ → ℝ, apm_m00A05_isSolution u₀ u := by
  refine ⟨apm_m00A05_globalCandidate u₀,
    apm_m00A05_globalCandidate_continuousOn u₀, ?_, ?_, ?_⟩
  · intro t ht
    exact (apm_m00A05_globalCandidate_hasDerivAt u₀ ht).differentiableAt.differentiableWithinAt
  · exact apm_m00A05_globalCandidate_zero u₀
  · intro t ht
    rw [(apm_m00A05_globalCandidate_hasDerivAt u₀ ht).deriv]
    ring

theorem apm_m00a05 :
    (∀ u₀ : ℝ,
      ∃ u : ℝ → ℝ,
        apm_m00A05_isSolution u₀ u ∧
        ∀ v : ℝ → ℝ,
          apm_m00A05_isSolution u₀ v → EqOn u v (Ici 0)) ∧
    ∃ ξ : ℝ, Real.cos ξ = ξ ∧
      ∀ (u₀ : ℝ) (u : ℝ → ℝ),
        apm_m00A05_isSolution u₀ u →
        Tendsto u atTop (nhds ξ) := by
  constructor
  · intro u₀
    obtain ⟨u, hu⟩ := apm_m00A05_bridge_global_exists u₀
    exact ⟨u, hu, fun v hv => apm_m00A05_solution_unique hu hv⟩
  · let G : ℝ → ℝ := fun x => Real.cos x - x
    have hzero : 0 ∈ G '' Icc (0 : ℝ) (Real.pi / 2) := by
      apply intermediate_value_Icc' (by positivity)
        ((Real.continuous_cos.sub continuous_id).continuousOn)
      constructor
      · dsimp [G]
        rw [Real.cos_pi_div_two]
        nlinarith [Real.pi_pos]
      · norm_num [G]
    obtain ⟨ξ, hξIcc, hξ⟩ := hzero
    refine ⟨ξ, ?_, ?_⟩
    · dsimp [G] at hξ
      linarith
    · intro u₀ u hu
      have hξfixed : Real.cos ξ = ξ := by
        dsimp [G] at hξ
        linarith
      obtain ⟨L, hL⟩ := apm_m00A05_exists_limit hu hξfixed
      have hLfixed := apm_m00A05_limit_is_fixed hu hL
      rw [apm_m00A05_fixed_unique hLfixed hξfixed] at hL
      exact hL
