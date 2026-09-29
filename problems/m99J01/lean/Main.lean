import Mathlib

open scoped Manifold

/-!
# APM m99J01

## Statement repairs

None.

## Encoding questions

A solution on the half-line is represented by a `C¹` function on `ℝ`, with the
differential equation and uniqueness asserted only for nonnegative times. This avoids
mistakenly identifying arbitrary extensions to negative time as different solutions.
-/

def apm_m99j01_IsSolution (u₀ : ℝ) (u : ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 u ∧ u 0 = u₀ ∧
    ∀ t : ℝ, 0 ≤ t → deriv u t + u t = Real.cos (u t)

noncomputable def apm_m99j01_vectorField (x : ℝ) : ℝ := Real.cos x - x

/-- The autonomous vector field has the global Lipschitz bound needed by
Picard--Lindelöf and Grönwall uniqueness. -/
lemma apm_m99j01_vectorField_lipschitz :
    LipschitzWith 2 apm_m99j01_vectorField := by
  change LipschitzWith 2 (fun x : ℝ => Real.cos x - x)
  convert Real.lipschitzWith_cos.sub LipschitzWith.id using 1 <;> norm_num

/-- Every cosine fixed point gives the constant equilibrium solution in the
raw global-`C¹` encoding. -/
lemma apm_m99j01_fixed_isSolution {ξ : ℝ} (hξ : Real.cos ξ = ξ) :
    apm_m99j01_IsSolution ξ (fun _ => ξ) := by
  refine ⟨contDiff_const, rfl, ?_⟩
  intro t ht
  simpa [hξ]

lemma apm_m99j01_cos_fixed_unique {x y : ℝ}
    (hx : Real.cos x = x) (hy : Real.cos y = y) : x = y := by
  have fixed_mem (z : ℝ) (hz : Real.cos z = z) : z ∈ Set.Icc (0 : ℝ) Real.pi := by
    have hz_lower : -(1 : ℝ) ≤ z := by rw [← hz]; exact Real.neg_one_le_cos z
    have hz_upper : z ≤ 1 := by rw [← hz]; exact Real.cos_le_one z
    have hz_pos : 0 < z := by
      rw [← hz]
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> nlinarith [Real.pi_gt_three]
    exact ⟨hz_pos.le, by nlinarith [Real.pi_gt_three]⟩
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · have := Real.strictAntiOn_cos (fixed_mem x hx) (fixed_mem y hy) hxy
    rw [hx, hy] at this
    exact (not_lt_of_ge hxy.le this).elim
  · exact hxy
  · have := Real.strictAntiOn_cos (fixed_mem y hy) (fixed_mem x hx) hxy
    rw [hx, hy] at this
    exact (not_lt_of_ge hxy.le this).elim

/-- The autonomous vector field points right below its equilibrium. -/
lemma apm_m99j01_vectorField_pos_of_lt_fixed {x ξ : ℝ}
    (hξ : Real.cos ξ = ξ) (hxξ : x < ξ) :
    0 < apm_m99j01_vectorField x := by
  unfold apm_m99j01_vectorField
  have hξ_le_one : ξ ≤ 1 := by rw [← hξ]; exact Real.cos_le_one ξ
  by_cases hxneg : x < 0
  · by_cases hxsmall : x < -1
    · linarith [Real.neg_one_le_cos x]
    · have hxmem : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
        constructor <;> nlinarith [Real.pi_gt_three]
      linarith [Real.cos_pos_of_mem_Ioo hxmem]
  · have hx0 : 0 ≤ x := le_of_not_gt hxneg
    have hξ0 : 0 ≤ ξ := le_trans hx0 hxξ.le
    have hxmem : x ∈ Set.Icc (0 : ℝ) Real.pi :=
      ⟨hx0, by nlinarith [Real.pi_gt_three]⟩
    have hξmem : ξ ∈ Set.Icc (0 : ℝ) Real.pi :=
      ⟨hξ0, by nlinarith [Real.pi_gt_three]⟩
    have hcos := Real.strictAntiOn_cos hxmem hξmem hxξ
    rw [hξ] at hcos
    linarith

/-- The autonomous vector field points left above its equilibrium. -/
lemma apm_m99j01_vectorField_neg_of_fixed_lt {x ξ : ℝ}
    (hξ : Real.cos ξ = ξ) (hξx : ξ < x) :
    apm_m99j01_vectorField x < 0 := by
  unfold apm_m99j01_vectorField
  have hξ_ge_neg_one : -(1 : ℝ) ≤ ξ := by
    rw [← hξ]
    exact Real.neg_one_le_cos ξ
  have hξ_le_one : ξ ≤ 1 := by
    rw [← hξ]
    exact Real.cos_le_one ξ
  have hξ_pos : 0 < ξ := by
    rw [← hξ]
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_gt_three]
  by_cases hxlarge : 1 < x
  · linarith [Real.cos_le_one x]
  · have hx1 : x ≤ 1 := le_of_not_gt hxlarge
    have hξmem : ξ ∈ Set.Icc (0 : ℝ) Real.pi :=
      ⟨hξ_pos.le, by nlinarith [Real.pi_gt_three]⟩
    have hxmem : x ∈ Set.Icc (0 : ℝ) Real.pi :=
      ⟨le_trans hξ_pos.le hξx.le, by nlinarith [Real.pi_gt_three]⟩
    have hcos := Real.strictAntiOn_cos hξmem hxmem hξx
    rw [hξ] at hcos
    linarith

/-- Global representatives satisfying the frozen half-line predicate are
unique on the half-line. -/
lemma apm_m99j01_solution_unique {u₀ : ℝ} {u v : ℝ → ℝ}
    (hu : apm_m99j01_IsSolution u₀ u)
    (hv : apm_m99j01_IsSolution u₀ v) :
    ∀ t : ℝ, 0 ≤ t → v t = u t := by
  intro t ht
  have huniq := ODE_solution_unique (K := 2)
    (v := fun _ : ℝ => apm_m99j01_vectorField)
    (f := v) (g := u) (a := (0 : ℝ)) (b := t)
    (fun _ => apm_m99j01_vectorField_lipschitz)
    hv.1.continuous.continuousOn
    (fun s hs => by
      have hd := (hv.1.differentiable one_ne_zero s).hasDerivAt
      apply HasDerivAt.hasDerivWithinAt
      convert hd using 1
      unfold apm_m99j01_vectorField
      linarith [hv.2.2 s hs.1])
    hu.1.continuous.continuousOn
    (fun s hs => by
      have hd := (hu.1.differentiable one_ne_zero s).hasDerivAt
      apply HasDerivAt.hasDerivWithinAt
      convert hd using 1
      unfold apm_m99j01_vectorField
      linarith [hu.2.2 s hs.1])
    (by rw [hu.2.1, hv.2.1])
  exact huniq ⟨ht, le_rfl⟩

/-- A solution which reaches an equilibrium at a nonnegative time was already
equal to that equilibrium throughout the preceding interval.  This is the
backwards-time uniqueness fact used to prevent crossing the equilibrium. -/
lemma apm_m99j01_eq_fixed_on_Icc_of_eq_at
    {u₀ ξ s : ℝ} {u : ℝ → ℝ}
    (hξ : Real.cos ξ = ξ) (hu : apm_m99j01_IsSolution u₀ u)
    (hs0 : 0 ≤ s) (hus : u s = ξ) :
    ∀ r ∈ Set.Icc (0 : ℝ) s, u r = ξ := by
  let rev : ℝ → ℝ := fun r => u (s - r)
  let eqm : ℝ → ℝ := fun _ => ξ
  have huniq := ODE_solution_unique (K := 2)
    (v := fun _ : ℝ => fun x => -apm_m99j01_vectorField x)
    (f := rev) (g := eqm) (a := (0 : ℝ)) (b := s)
    (fun _ => apm_m99j01_vectorField_lipschitz.neg)
    (hu.1.continuous.comp (continuous_const.sub continuous_id)).continuousOn
    (fun r hr => by
      have hsr : 0 ≤ s - r := sub_nonneg.mpr hr.2.le
      have hd := (hu.1.differentiable one_ne_zero (s - r)).hasDerivAt
      have hd' : HasDerivAt u (apm_m99j01_vectorField (u (s - r))) (s - r) := by
        convert hd using 1
        unfold apm_m99j01_vectorField
        linarith [hu.2.2 (s - r) hsr]
      have hc : HasDerivAt (fun z : ℝ => s - z) (-1) r :=
        by convert (hasDerivAt_const r s).sub (hasDerivAt_id r) using 1 <;> norm_num
      convert (hd'.comp r hc).hasDerivWithinAt (s := Set.Ici r) using 1 <;>
        simp [rev, Function.comp_def])
    continuousOn_const
    (fun r hr => by
      have hz : apm_m99j01_vectorField ξ = 0 := by
        simp [apm_m99j01_vectorField, hξ]
      simpa [eqm, hz] using
        (hasDerivAt_const r ξ).hasDerivWithinAt (s := Set.Ici r))
    (by simp [rev, eqm, hus])
  intro r hr
  have hre := huniq ⟨sub_nonneg.mpr hr.2, by linarith [hr.1]⟩
  simpa [rev, eqm] using hre

lemma apm_m99j01_le_fixed_of_initial_le
    {u₀ ξ : ℝ} {u : ℝ → ℝ}
    (hξ : Real.cos ξ = ξ) (hu : apm_m99j01_IsSolution u₀ u)
    (hu₀ : u₀ ≤ ξ) : ∀ t : ℝ, 0 ≤ t → u t ≤ ξ := by
  intro t ht
  by_contra hnot
  have hξut : ξ < u t := lt_of_not_ge hnot
  by_cases heq : u₀ = ξ
  · have hconst := apm_m99j01_fixed_isSolution hξ
    have huξ : apm_m99j01_IsSolution ξ u := heq ▸ hu
    have he := apm_m99j01_solution_unique huξ hconst t ht
    simp only at he
    linarith
  · have hu₀ξ : u₀ < ξ := lt_of_le_of_ne hu₀ heq
    have hcont : ContinuousOn u (Set.Icc (0 : ℝ) t) :=
      hu.1.continuous.continuousOn
    have himg := intermediate_value_Icc ht hcont
      (show ξ ∈ Set.Icc (u 0) (u t) by
        rw [hu.2.1]
        exact ⟨hu₀ξ.le, hξut.le⟩)
    obtain ⟨s, hs, hus⟩ := himg
    have hback := apm_m99j01_eq_fixed_on_Icc_of_eq_at hξ hu hs.1 hus
      0 ⟨le_rfl, hs.1⟩
    rw [hu.2.1] at hback
    exact heq hback

lemma apm_m99j01_fixed_le_of_initial_ge
    {u₀ ξ : ℝ} {u : ℝ → ℝ}
    (hξ : Real.cos ξ = ξ) (hu : apm_m99j01_IsSolution u₀ u)
    (hu₀ : ξ ≤ u₀) : ∀ t : ℝ, 0 ≤ t → ξ ≤ u t := by
  intro t ht
  by_contra hnot
  have hutξ : u t < ξ := lt_of_not_ge hnot
  by_cases heq : u₀ = ξ
  · have hconst := apm_m99j01_fixed_isSolution hξ
    have huξ : apm_m99j01_IsSolution ξ u := heq ▸ hu
    have he := apm_m99j01_solution_unique huξ hconst t ht
    simp only at he
    linarith
  · have hξu₀ : ξ < u₀ := lt_of_le_of_ne hu₀ (Ne.symm heq)
    have hcont : ContinuousOn u (Set.Icc (0 : ℝ) t) :=
      hu.1.continuous.continuousOn
    have himg := intermediate_value_Icc' ht hcont
      (show ξ ∈ Set.Icc (u t) (u 0) by
        rw [hu.2.1]
        exact ⟨hutξ.le, hξu₀.le⟩)
    obtain ⟨s, hs, hus⟩ := himg
    have hback := apm_m99j01_eq_fixed_on_Icc_of_eq_at hξ hu hs.1 hus
      0 ⟨le_rfl, hs.1⟩
    rw [hu.2.1] at hback
    exact heq hback

lemma apm_m99j01_monotoneOn_of_initial_le
    {u₀ ξ : ℝ} {u : ℝ → ℝ}
    (hξ : Real.cos ξ = ξ) (hu : apm_m99j01_IsSolution u₀ u)
    (hu₀ : u₀ ≤ ξ) : MonotoneOn u (Set.Ici 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
    hu.1.continuous.continuousOn
    (hu.1.differentiable one_ne_zero).differentiableOn ?_
  intro t ht
  have ht0 : 0 ≤ t := by
    have htp : 0 < t := by simpa only [interior_Ici, Set.mem_Ioi] using ht
    exact htp.le
  have hut := apm_m99j01_le_fixed_of_initial_le hξ hu hu₀ t ht0
  have hderiv : deriv u t = apm_m99j01_vectorField (u t) := by
    unfold apm_m99j01_vectorField
    linarith [hu.2.2 t ht0]
  rw [hderiv]
  rcases hut.eq_or_lt with heq | hlt
  · simp [heq, apm_m99j01_vectorField, hξ]
  · exact (apm_m99j01_vectorField_pos_of_lt_fixed hξ hlt).le

lemma apm_m99j01_antitoneOn_of_initial_ge
    {u₀ ξ : ℝ} {u : ℝ → ℝ}
    (hξ : Real.cos ξ = ξ) (hu : apm_m99j01_IsSolution u₀ u)
    (hu₀ : ξ ≤ u₀) : AntitoneOn u (Set.Ici 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
    hu.1.continuous.continuousOn
    (hu.1.differentiable one_ne_zero).differentiableOn ?_
  intro t ht
  have ht0 : 0 ≤ t := by
    have htp : 0 < t := by simpa only [interior_Ici, Set.mem_Ioi] using ht
    exact htp.le
  have hut := apm_m99j01_fixed_le_of_initial_ge hξ hu hu₀ t ht0
  have hderiv : deriv u t = apm_m99j01_vectorField (u t) := by
    unfold apm_m99j01_vectorField
    linarith [hu.2.2 t ht0]
  rw [hderiv]
  rcases hut.eq_or_lt with heq | hlt
  · simp [← heq, apm_m99j01_vectorField, hξ]
  · exact (apm_m99j01_vectorField_neg_of_fixed_lt hξ hlt).le

/-- A real function which is monotone and bounded on the nonnegative ray has
a finite limit at `+∞`. -/
lemma apm_m99j01_exists_limit_of_monotoneOn_Ici
    {f : ℝ → ℝ} (hmono : MonotoneOn f (Set.Ici 0))
    (hlower : ∃ a, ∀ t, 0 ≤ t → a ≤ f t)
    (hupper : ∃ b, ∀ t, 0 ≤ t → f t ≤ b) :
    ∃ L, Filter.Tendsto f Filter.atTop (nhds L) := by
  have hbbelow : BddBelow (f '' Set.Ici (0 : ℝ)) := by
    obtain ⟨a, ha⟩ := hlower
    refine ⟨a, ?_⟩
    rintro y ⟨t, ht, rfl⟩
    exact ha t ht
  have hbabove : BddAbove (f '' Set.Ici (0 : ℝ)) := by
    obtain ⟨b, hb⟩ := hupper
    refine ⟨b, ?_⟩
    rintro y ⟨t, ht, rfl⟩
    exact hb t ht
  obtain ⟨g, hgmono, hfg⟩ :=
    hmono.exists_monotone_extension hbbelow hbabove
  have hgbdd : BddAbove (Set.range g) := by
    obtain ⟨b, hb⟩ := hupper
    refine ⟨b, ?_⟩
    rintro y ⟨t, rfl⟩
    by_cases ht : 0 ≤ t
    · rw [← hfg ht]
      exact hb t ht
    · have ht0 : t ≤ 0 := le_of_not_ge ht
      exact le_trans (hgmono ht0) (by
        rw [← hfg (show 0 ∈ Set.Ici (0 : ℝ) by simp)]
        exact hb 0 (le_refl 0))
  refine ⟨⨆ t, g t, (tendsto_atTop_ciSup hgmono hgbdd).congr' ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
  exact (hfg ht).symm

lemma apm_m99j01_exists_limit_of_antitoneOn_Ici
    {f : ℝ → ℝ} (hanti : AntitoneOn f (Set.Ici 0))
    (hlower : ∃ a, ∀ t, 0 ≤ t → a ≤ f t)
    (hupper : ∃ b, ∀ t, 0 ≤ t → f t ≤ b) :
    ∃ L, Filter.Tendsto f Filter.atTop (nhds L) := by
  have hbbelow : BddBelow (f '' Set.Ici (0 : ℝ)) := by
    obtain ⟨a, ha⟩ := hlower
    refine ⟨a, ?_⟩
    rintro y ⟨t, ht, rfl⟩
    exact ha t ht
  have hbabove : BddAbove (f '' Set.Ici (0 : ℝ)) := by
    obtain ⟨b, hb⟩ := hupper
    refine ⟨b, ?_⟩
    rintro y ⟨t, ht, rfl⟩
    exact hb t ht
  obtain ⟨g, hganti, hfg⟩ :=
    hanti.exists_antitone_extension hbbelow hbabove
  have hgbdd : BddBelow (Set.range g) := by
    obtain ⟨a, ha⟩ := hlower
    refine ⟨a, ?_⟩
    rintro y ⟨t, rfl⟩
    by_cases ht : 0 ≤ t
    · rw [← hfg ht]
      exact ha t ht
    · have ht0 : t ≤ 0 := le_of_not_ge ht
      exact le_trans (ha 0 (le_refl 0)) (by
        rw [hfg (show 0 ∈ Set.Ici (0 : ℝ) by simp)]
        exact hganti ht0)
  refine ⟨⨅ t, g t, (tendsto_atTop_ciInf hganti hgbdd).congr' ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
  exact (hfg ht).symm

/-- Any finite limit of a solution is an equilibrium.  The mean value theorem
on `[n,n+1]` supplies points where the derivative is the vanishing difference
of two convergent sequences. -/
lemma apm_m99j01_limit_is_fixed
    {u₀ L : ℝ} {u : ℝ → ℝ} (hu : apm_m99j01_IsSolution u₀ u)
    (hlim : Filter.Tendsto u Filter.atTop (nhds L)) : Real.cos L = L := by
  have hex (n : ℕ) : ∃ c ∈ Set.Ioo (n : ℝ) (n + 1 : ℝ),
      deriv u c = u (n + 1 : ℝ) - u (n : ℝ) := by
    obtain ⟨c, hc, hdc⟩ := exists_deriv_eq_slope u
      (a := (n : ℝ)) (b := (n + 1 : ℝ)) (by norm_num)
      hu.1.continuous.continuousOn
      (hu.1.differentiable one_ne_zero).differentiableOn
    refine ⟨c, hc, ?_⟩
    convert hdc using 1 <;> norm_num
  choose c hc hdc using hex
  have hctop : Filter.Tendsto c Filter.atTop Filter.atTop := by
    exact Filter.tendsto_atTop_mono' Filter.atTop
      (Filter.Eventually.of_forall (fun n => (hc n).1.le))
      tendsto_natCast_atTop_atTop
  have hu_c : Filter.Tendsto (fun n => u (c n)) Filter.atTop (nhds L) :=
    hlim.comp hctop
  have hvf : Filter.Tendsto
      (fun n => apm_m99j01_vectorField (u (c n))) Filter.atTop
      (nhds (apm_m99j01_vectorField L)) := by
    exact ((Real.continuous_cos.sub continuous_id).tendsto L).comp hu_c
  have hn : Filter.Tendsto (fun n : ℕ => u (n : ℝ)) Filter.atTop (nhds L) :=
    hlim.comp tendsto_natCast_atTop_atTop
  have hn1top : Filter.Tendsto (fun n : ℕ => (n + 1 : ℝ))
      Filter.atTop Filter.atTop := by
    exact Filter.tendsto_atTop_add_const_right Filter.atTop 1
      tendsto_natCast_atTop_atTop
  have hn1 : Filter.Tendsto (fun n : ℕ => u (n + 1 : ℝ))
      Filter.atTop (nhds L) := hlim.comp hn1top
  have hdiff : Filter.Tendsto (fun n : ℕ => u (n + 1 : ℝ) - u (n : ℝ))
      Filter.atTop (nhds 0) := by
    simpa using hn1.sub hn
  have heq : (fun n : ℕ => apm_m99j01_vectorField (u (c n))) =
      fun n : ℕ => u (n + 1 : ℝ) - u (n : ℝ) := by
    funext n
    have hc0 : 0 ≤ c n := le_trans (Nat.cast_nonneg n) (hc n).1.le
    rw [← hdc n]
    unfold apm_m99j01_vectorField
    linarith [hu.2.2 (c n) hc0]
  rw [heq] at hvf
  have hz : apm_m99j01_vectorField L = 0 := tendsto_nhds_unique hvf hdiff
  simpa [apm_m99j01_vectorField] using sub_eq_zero.mp hz

/-- Why this unblocks `apm_m99j01`: this is the precise global continuation
statement missing from Mathlib's local Picard--Lindelöf API, expressed in the
frozen raw-`deriv` half-line solution predicate. -/
lemma apm_m99J01_local_curve (x : ℝ) : ∃ γ : ℝ → ℝ, γ 0 = x ∧
    IsMIntegralCurveOn (I := 𝓘(ℝ)) γ
      (fun y : ℝ => apm_m99j01_vectorField y)
      (Set.Ioo (-(1 / 4 : ℝ)) (1 / 4 : ℝ)) := by
  let a : NNReal := ⟨|x| + 1, by positivity⟩
  let L : NNReal := 2 * a
  let K : NNReal := 2
  let t0 : Set.Icc (-(1 / 4 : ℝ)) (1 / 4 : ℝ) := ⟨0, by norm_num⟩
  have hb : ∀ y ∈ Metric.closedBall x (a : ℝ),
      ‖apm_m99j01_vectorField y‖ ≤ L := by
    intro y hy
    rw [Real.norm_eq_abs, show (L : ℝ) = 2 * (|x| + 1) by rfl]
    have hyx : |y - x| ≤ |x| + 1 := by
      simpa [Real.dist_eq] using hy
    have hyabs : |y| ≤ 2 * |x| + 1 := by
      calc
        |y| ≤ |y - x| + |x| := by
          simpa [sub_add_cancel] using abs_add_le (y - x) x
        _ ≤ (|x| + 1) + |x| := by gcongr
        _ = 2 * |x| + 1 := by ring
    unfold apm_m99j01_vectorField
    calc
      |Real.cos y - y| ≤ |Real.cos y| + |y| := abs_sub _ _
      _ ≤ 1 + |y| := by gcongr; exact Real.abs_cos_le_one y
      _ ≤ 2 * (|x| + 1) := by linarith
  have hl : LipschitzOnWith K apm_m99j01_vectorField
      (Metric.closedBall x (a : ℝ)) :=
    apm_m99j01_vectorField_lipschitz.lipschitzOnWith
  have hm : L * max ((1 / 4 : ℝ) - t0) (t0 - (-(1 / 4 : ℝ))) ≤ a - 0 := by
    change (2 * (|x| + 1)) *
      max ((1 / 4 : ℝ) - 0) (0 - (-(1 / 4 : ℝ))) ≤ |x| + 1 - 0
    norm_num
    linarith [abs_nonneg x]
  have hpl : IsPicardLindelof
      (fun _ : ℝ => apm_m99j01_vectorField) t0 x a 0 L K :=
    IsPicardLindelof.of_time_independent hb hl hm
  obtain ⟨γ, hγ0, hγ⟩ :=
    hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨γ, hγ0, ?_⟩
  intro t ht
  have hd := (hγ t (Set.Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)
  simpa only [ContinuousLinearMap.one_apply] using
    hd.hasFDerivAt.hasMFDerivAt.hasMFDerivWithinAt
      (s := Set.Ioo (-(1 / 4 : ℝ)) (1 / 4 : ℝ))

lemma apm_m99J01_global_curve (x : ℝ) : ∃ γ : ℝ → ℝ, γ 0 = x ∧
    IsMIntegralCurve (I := 𝓘(ℝ)) γ
      (fun y : ℝ => apm_m99j01_vectorField y) := by
  have hvf : ContDiff ℝ 1 apm_m99j01_vectorField := by
    unfold apm_m99j01_vectorField
    fun_prop
  have hv : ContMDiff 𝓘(ℝ) (𝓘(ℝ).prod 𝓘(ℝ)) 1
      (fun y : ℝ =>
        (⟨y, apm_m99j01_vectorField y⟩ : TangentBundle 𝓘(ℝ) ℝ)) := by
    exact (contMDiff_vectorSpace_iff_contDiff).2 hvf
  exact exists_isMIntegralCurve_of_isMIntegralCurveOn
    (I := 𝓘(ℝ)) hv (by norm_num : (0 : ℝ) < 1 / 4)
      apm_m99J01_local_curve x

theorem apm_m99J01_bridge_global_solution (u₀ : ℝ) :
    ∃ u : ℝ → ℝ, apm_m99j01_IsSolution u₀ u := by
  obtain ⟨u, hu0, hu⟩ := apm_m99J01_global_curve u₀
  have hd (t : ℝ) :
      HasDerivAt u (apm_m99j01_vectorField (u t)) t := by
    rw [hasDerivAt_iff_hasFDerivAt]
    simpa only [ContinuousLinearMap.one_apply] using (hu t).hasFDerivAt
  have hcont : ContDiff ℝ 1 u := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun t => (hd t).differentiableAt, ?_⟩
    have heq : deriv u = fun t => apm_m99j01_vectorField (u t) := by
      funext t
      exact (hd t).deriv
    rw [heq]
    exact (Real.continuous_cos.sub continuous_id).comp hu.continuous
  refine ⟨u, hcont, hu0, ?_⟩
  intro t ht
  rw [(hd t).deriv]
  simp [apm_m99j01_vectorField]

/-- Why this unblocks `apm_m99j01`: the phase-line signs already proved above
imply trapping and the appropriate monotonicity direction; the final clause
identifies the resulting monotone limit with the equilibrium. -/
theorem apm_m99J01_bridge_trapping_and_convergence
    {ξ u₀ : ℝ} {u : ℝ → ℝ}
    (hξ : Real.cos ξ = ξ) (hu : apm_m99j01_IsSolution u₀ u) :
    ((u₀ ≤ ξ →
        MonotoneOn u (Set.Ici 0) ∧
        ∀ t : ℝ, 0 ≤ t → u t ≤ ξ) ∧
      (ξ ≤ u₀ →
        AntitoneOn u (Set.Ici 0) ∧
        ∀ t : ℝ, 0 ≤ t → ξ ≤ u t)) ∧
      Filter.Tendsto u Filter.atTop (nhds ξ) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro hu₀
    exact ⟨apm_m99j01_monotoneOn_of_initial_le hξ hu hu₀,
      apm_m99j01_le_fixed_of_initial_le hξ hu hu₀⟩
  · intro hu₀
    exact ⟨apm_m99j01_antitoneOn_of_initial_ge hξ hu hu₀,
      apm_m99j01_fixed_le_of_initial_ge hξ hu hu₀⟩
  · rcases le_total u₀ ξ with hu₀ | hu₀
    · let hmono := apm_m99j01_monotoneOn_of_initial_le hξ hu hu₀
      let hub := apm_m99j01_le_fixed_of_initial_le hξ hu hu₀
      obtain ⟨L, hL⟩ := apm_m99j01_exists_limit_of_monotoneOn_Ici hmono
        ⟨u₀, fun t ht => by
          rw [← hu.2.1]
          exact hmono (by simp) ht ht⟩
        ⟨ξ, hub⟩
      have hLf : Real.cos L = L := apm_m99j01_limit_is_fixed hu hL
      have hLξ : L = ξ := apm_m99j01_cos_fixed_unique hLf hξ
      simpa [hLξ] using hL
    · let hanti := apm_m99j01_antitoneOn_of_initial_ge hξ hu hu₀
      let hlb := apm_m99j01_fixed_le_of_initial_ge hξ hu hu₀
      obtain ⟨L, hL⟩ := apm_m99j01_exists_limit_of_antitoneOn_Ici hanti
        ⟨ξ, hlb⟩
        ⟨u₀, fun t ht => by
          rw [← hu.2.1]
          exact hanti (by simp) ht ht⟩
      have hLf : Real.cos L = L := apm_m99j01_limit_is_fixed hu hL
      have hLξ : L = ξ := apm_m99j01_cos_fixed_unique hLf hξ
      simpa [hLξ] using hL

theorem apm_m99j01 :
    (∀ u₀ : ℝ,
      ∃ u : ℝ → ℝ,
        apm_m99j01_IsSolution u₀ u ∧
          ∀ v : ℝ → ℝ, apm_m99j01_IsSolution u₀ v →
            ∀ t : ℝ, 0 ≤ t → v t = u t) ∧
    ∃! ξ : ℝ,
      Real.cos ξ = ξ ∧
        ∀ (u₀ : ℝ) (u : ℝ → ℝ),
          apm_m99j01_IsSolution u₀ u →
            Filter.Tendsto u Filter.atTop (nhds ξ) := by
  have hexists_fixed : ∃ ξ : ℝ, Real.cos ξ = ξ := by
    let g : ℝ → ℝ := fun x ↦ Real.cos x - x
    have hg : Continuous g := Real.continuous_cos.sub continuous_id
    have hz : (0 : ℝ) ∈ Set.Icc (g 1) (g 0) := by
      refine ⟨?_, ?_⟩
      · exact sub_nonpos.mpr (Real.cos_le_one 1)
      · simp [g]
    obtain ⟨ξ, _hξ, hξ⟩ :=
      intermediate_value_Icc' (show (0 : ℝ) ≤ 1 by norm_num) hg.continuousOn hz
    exact ⟨ξ, sub_eq_zero.mp hξ⟩
  have hexists_unique_fixed : ∃! ξ : ℝ, Real.cos ξ = ξ := by
    obtain ⟨ξ, hξ⟩ := hexists_fixed
    exact ⟨ξ, hξ, fun y hy => apm_m99j01_cos_fixed_unique hy hξ⟩
  constructor
  · intro u₀
    obtain ⟨u, hu⟩ := apm_m99J01_bridge_global_solution u₀
    exact ⟨u, hu, fun v hv => apm_m99j01_solution_unique hu hv⟩
  · obtain ⟨ξ, hξ, hξuniq⟩ := hexists_unique_fixed
    refine ⟨ξ, ⟨hξ, ?_⟩, ?_⟩
    · intro u₀ u hu
      exact (apm_m99J01_bridge_trapping_and_convergence hξ hu).2
    · intro y hy
      exact apm_m99j01_cos_fixed_unique hy.1 hξ
