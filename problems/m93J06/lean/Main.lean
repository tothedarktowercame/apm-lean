import Mathlib

/-!
# APM m93J06 — existence and dependence for scalar ODEs

## Statement repairs

Part (d), read as Hölder continuity of `f` in the dependent variable with
exponent strictly below one, is false: uniqueness can already fail.  We record
that failure explicitly.  The well-posed Hölder conclusion is stated under the
Lipschitz hypothesis from part (a), which in fact gives a Lipschitz flow map.
-/

def apm_m93j06_Solves (f : ℝ → ℝ → ℝ) (y₀ : ℝ) (y : ℝ → ℝ) : Prop :=
  y 0 = y₀ ∧ ∀ t, HasDerivAt y (f t (y t)) t

def apm_m93j06_IsFlow (f : ℝ → ℝ → ℝ) (φ : ℝ → ℝ → ℝ) : Prop :=
  ∀ y₀, apm_m93j06_Solves f y₀ (fun t => φ t y₀)

lemma apm_m93j06_flow_zero {f φ : ℝ → ℝ → ℝ}
    (hφ : apm_m93j06_IsFlow f φ) (y₀ : ℝ) : φ 0 y₀ = y₀ :=
  (hφ y₀).1

lemma apm_m93j06_flow_hasDerivAt {f φ : ℝ → ℝ → ℝ}
    (hφ : apm_m93j06_IsFlow f φ) (y₀ t : ℝ) :
    HasDerivAt (fun s ↦ φ s y₀) (f t (φ t y₀)) t :=
  (hφ y₀).2 t

/-- The stability estimate is exact at the initial time. -/
lemma apm_m93j06_flow_distance_zero {f φ : ℝ → ℝ → ℝ}
    (hφ : apm_m93j06_IsFlow f φ) (L a b : ℝ) :
    |φ 0 a - φ 0 b| = Real.exp (L * |(0 : ℝ)|) * |a - b| := by
  rw [apm_m93j06_flow_zero hφ, apm_m93j06_flow_zero hφ]
  simp

/-- The signed-square curve is the nontrivial global trajectory for the
standard square-root nonuniqueness example. -/
lemma apm_m93j06_hasDerivAt_mul_abs (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ s * |s|) (2 * |t|) t := by
  by_cases ht : t = 0
  · subst t
    rw [hasDerivAt_iff_tendsto]
    have hfun :
        (fun s : ℝ => ‖s - 0‖⁻¹ *
          ‖s * |s| - 0 * |(0 : ℝ)| - (s - 0) • (2 * |(0 : ℝ)|)‖) =
          fun s : ℝ => |s| := by
      funext s
      by_cases hs : s = 0
      · simp [hs]
      · simp only [sub_zero, abs_zero, mul_zero, smul_zero,
          Real.norm_eq_abs]
        rw [abs_mul, abs_abs]
        rw [← abs_mul_abs_self]
        field_simp [abs_ne_zero.mpr hs]
        simp
    rw [hfun]
    simpa using continuous_abs.tendsto (0 : ℝ)
  · convert (hasDerivAt_id t).mul (hasDerivAt_abs ht) using 1
    rcases lt_or_gt_of_ne ht with htneg | htpos
    · simp [abs_of_neg htneg]
      ring
    · simp [abs_of_pos htpos]
      ring

/-- Along the signed-square trajectory, the square-root field evaluates to
the absolute-time derivative magnitude. -/
lemma apm_m93j06_sqrt_abs_mul_abs (t : ℝ) :
    Real.sqrt |t * abs t| = |t| := by
  rw [abs_mul, abs_abs]
  simpa [pow_two] using Real.sqrt_sq (abs_nonneg t)

/-- The zero curve solves the square-root vector field. -/
lemma apm_m93j06_zero_solves_sqrt :
    apm_m93j06_Solves (fun _ y ↦ 2 * Real.sqrt |y|) 0 (fun _ ↦ 0) := by
  constructor
  · rfl
  · intro t
    simpa using hasDerivAt_const t (0 : ℝ)

/-- The signed-square curve is a second global solution of the same initial
value problem. -/
lemma apm_m93j06_signedSquare_solves_sqrt :
    apm_m93j06_Solves (fun _ y ↦ 2 * Real.sqrt |y|) 0
      (fun t ↦ t * |t|) := by
  constructor
  · norm_num
  · intro t
    convert apm_m93j06_hasDerivAt_mul_abs t using 1
    change 2 * Real.sqrt |t * abs t| = 2 * |t|
    rw [apm_m93j06_sqrt_abs_mul_abs]

/-- The two explicit square-root trajectories are genuinely distinct. -/
lemma apm_m93j06_signedSquare_ne_zero :
    (fun t : ℝ ↦ t * |t|) ≠ fun _ ↦ 0 := by
  intro h
  have := congrFun h 1
  norm_num at this

/-- The elementary global square-root difference estimate. -/
lemma apm_m93j06_abs_sqrt_sub_sqrt_le_sqrt_abs_sub
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |Real.sqrt u - Real.sqrt v| ≤ Real.sqrt |u - v| := by
  wlog huv : v ≤ u generalizing u v
  · rw [abs_sub_comm u v, abs_sub_comm (Real.sqrt u) (Real.sqrt v)]
    exact this hv hu (le_of_not_ge huv)
  have hsu : 0 ≤ Real.sqrt u := Real.sqrt_nonneg u
  have hsv : 0 ≤ Real.sqrt v := Real.sqrt_nonneg v
  have hsvu : Real.sqrt v ≤ Real.sqrt u := Real.sqrt_le_sqrt huv
  rw [abs_of_nonneg (sub_nonneg.mpr hsvu), abs_of_nonneg (sub_nonneg.mpr huv),
    ← Real.sqrt_sq (sub_nonneg.mpr hsvu)]
  apply Real.sqrt_le_sqrt
  nlinarith [Real.sq_sqrt hu, Real.sq_sqrt hv,
    mul_nonneg hsv (sub_nonneg.mpr hsvu)]

/-- The square-root vector field used above is globally Hölder with exponent
`1/2` and constant `2`. -/
lemma apm_m93j06_sqrt_field_holder (_t a b : ℝ) :
    |2 * Real.sqrt (|a|) - 2 * Real.sqrt (|b|)| ≤
      2 * Real.rpow (|a - b|) (1 / 2 : ℝ) := by
  rw [← mul_sub, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  change 2 * |Real.sqrt (|a|) - Real.sqrt (|b|)| ≤
    2 * (|a - b|) ^ (1 / (2 : ℝ))
  rw [← Real.sqrt_eq_rpow]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    |Real.sqrt (|a|) - Real.sqrt (|b|)| ≤ Real.sqrt (abs (abs a - abs b)) :=
      apm_m93j06_abs_sqrt_sub_sqrt_le_sqrt_abs_sub (abs_nonneg a) (abs_nonneg b)
    _ ≤ Real.sqrt (|a - b|) := Real.sqrt_le_sqrt (abs_abs_sub_abs_le_abs_sub a b)

/-- Hölder continuity below exponent one does not imply uniqueness: the
square-root field and the two trajectories above refute the universal claim. -/
lemma apm_m93j06_not_holder_unique :
    ¬ ∀ α : ℝ, 0 < α → α < 1 → ∀ f : ℝ → ℝ → ℝ,
      (∃ K > 0, ∀ t a b,
        |f t a - f t b| ≤ K * Real.rpow |a - b| α) →
      ∀ y₀, ∃! y : ℝ → ℝ, apm_m93j06_Solves f y₀ y := by
  intro h
  obtain ⟨y, hy, hunique⟩ :=
    h (1 / 2 : ℝ) (by norm_num) (by norm_num)
      (fun _ y ↦ 2 * Real.sqrt |y|)
      ⟨2, by norm_num, apm_m93j06_sqrt_field_holder⟩ 0
  have hz : (fun _ : ℝ ↦ 0) = y := hunique _ apm_m93j06_zero_solves_sqrt
  have hs : (fun t : ℝ ↦ t * |t|) = y :=
    hunique _ apm_m93j06_signedSquare_solves_sqrt
  exact apm_m93j06_signedSquare_ne_zero (hs.trans hz.symm)

/-- On every compact time interval, joint continuity controls the forcing at
zero; the uniform state Lipschitz estimate then gives a linear-growth bound
for every state. -/
lemma apm_m93j06_exists_compact_linear_bound
    {f : ℝ → ℝ → ℝ} {L A B : ℝ} (hAB : A ≤ B)
    (hcont : Continuous (Function.uncurry f))
    (hLip : ∀ t a b, |f t a - f t b| ≤ L * |a - b|) :
    ∃ M ≥ 0, ∀ t ∈ Set.Icc A B, ∀ y, |f t y| ≤ M + L * |y| := by
  have hc : Continuous (fun t : ℝ ↦ |f t 0|) := by
    fun_prop
  obtain ⟨t₀, ht₀, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hAB) hc.continuousOn
  refine ⟨|f t₀ 0|, abs_nonneg _, ?_⟩
  intro t ht y
  calc
    |f t y| = |(f t y - f t 0) + f t 0| := by ring_nf
    _ ≤ |f t y - f t 0| + |f t 0| := abs_add_le _ _
    _ ≤ L * |y - 0| + |f t₀ 0| := add_le_add (hLip t y 0) (hmax ht)
    _ = |f t₀ 0| + L * |y| := by simp [add_comm]

/-- The compact linear-growth bound feeds Grönwall to give an a priori bound
on every trajectory over the interval, expressed in Mathlib's native bound. -/
lemma apm_m93j06_exists_forward_solution_bound
    {f : ℝ → ℝ → ℝ} {L A B : ℝ} (hAB : A ≤ B)
    (hcont : Continuous (Function.uncurry f))
    (hLip : ∀ t a b, |f t a - f t b| ≤ L * |a - b|) :
    ∃ M ≥ 0, ∀ (y : ℝ → ℝ),
      (∀ t, HasDerivAt y (f t (y t)) t) →
      ∀ t ∈ Set.Icc A B,
        |y t| ≤ gronwallBound |y A| L M (t - A) := by
  obtain ⟨M, hM, hbound⟩ :=
    apm_m93j06_exists_compact_linear_bound hAB hcont hLip
  refine ⟨M, hM, fun y hy ↦ ?_⟩
  apply norm_le_gronwallBound_of_norm_deriv_right_le (f' := fun t ↦ f t (y t))
    (continuous_iff_continuousAt.mpr (fun t ↦ (hy t).continuousAt)).continuousOn
    (fun t _ ↦ (hy t).hasDerivWithinAt)
    (by simp [Real.norm_eq_abs])
  intro t ht
  simpa [Real.norm_eq_abs, add_comm] using hbound t ⟨ht.1, le_of_lt ht.2⟩ (y t)

/-- Interval-native version of the forward a priori estimate. Unlike the
global variant, this consumes exactly the `HasDerivWithinAt` data produced by
Picard--Lindelöf and used by continuation. -/
lemma apm_m93j06_exists_forward_interval_solution_bound
    {f : ℝ → ℝ → ℝ} {L A B : ℝ} (hAB : A ≤ B)
    (hcont : Continuous (Function.uncurry f))
    (hLip : ∀ t a b, |f t a - f t b| ≤ L * |a - b|) :
    ∃ M ≥ 0, ∀ (y : ℝ → ℝ),
      (∀ t ∈ Set.Icc A B,
        HasDerivWithinAt y (f t (y t)) (Set.Icc A B) t) →
      ∀ t ∈ Set.Icc A B,
        |y t| ≤ gronwallBound |y A| L M (t - A) := by
  obtain ⟨M, hM, hbound⟩ :=
    apm_m93j06_exists_compact_linear_bound hAB hcont hLip
  refine ⟨M, hM, fun y hy ↦ ?_⟩
  have hy' : ∀ t ∈ Set.Ico A B,
      HasDerivWithinAt y (f t (y t)) (Set.Ici t) t := by
    intro t ht
    have htIcc : t ∈ Set.Icc A B := ⟨ht.1, le_of_lt ht.2⟩
    have hnear : Set.Icc A B ∈ nhdsWithin t (Set.Ici t) := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds ht.2)] with s hs hsB
      exact ⟨ht.1.trans hs, hsB⟩
    exact (hy t htIcc).mono_of_mem_nhdsWithin hnear
  have hb' : ∀ t ∈ Set.Ico A B, ‖f t (y t)‖ ≤ L * ‖y t‖ + M := by
    intro t ht
    simpa [Real.norm_eq_abs, add_comm] using
      hbound t ⟨ht.1, le_of_lt ht.2⟩ (y t)
  exact norm_le_gronwallBound_of_norm_deriv_right_le
    (HasDerivWithinAt.continuousOn hy) hy' (by simp [Real.norm_eq_abs]) hb'

/-- The corresponding backward-time a priori bound, proved by transporting
the forward estimate through the reversed vector field. -/
lemma apm_m93j06_exists_backward_solution_bound
    {f : ℝ → ℝ → ℝ} {L A B : ℝ} (hAB : A ≤ B)
    (hcont : Continuous (Function.uncurry f))
    (hLip : ∀ t a b, |f t a - f t b| ≤ L * |a - b|) :
    ∃ M ≥ 0, ∀ (y : ℝ → ℝ),
      (∀ t, HasDerivAt y (f t (y t)) t) →
      ∀ t ∈ Set.Icc A B,
        |y t| ≤ gronwallBound |y B| L M (B - t) := by
  let v : ℝ → ℝ → ℝ := fun s x ↦ -f (-s) x
  have hvcont : Continuous (Function.uncurry v) := by
    dsimp [v, Function.uncurry]
    fun_prop
  have hvLip : ∀ t a b, |v t a - v t b| ≤ L * |a - b| := by
    intro t a b
    change |-f (-t) a - -f (-t) b| ≤ L * |a - b|
    rw [show -f (-t) a - -f (-t) b = -(f (-t) a - f (-t) b) by ring,
      abs_neg]
    exact hLip (-t) a b
  obtain ⟨M, hM, hbound⟩ := apm_m93j06_exists_forward_solution_bound
    (f := v) (L := L) (A := -B) (B := -A) (neg_le_neg hAB) hvcont hvLip
  refine ⟨M, hM, fun y hy t ht ↦ ?_⟩
  let z : ℝ → ℝ := fun s ↦ y (-s)
  have hz : ∀ s, HasDerivAt z (v s (z s)) s := by
    intro s
    simpa [z, v] using (hy (-s)).comp s (hasDerivAt_neg s)
  have h := hbound z hz (-t) ⟨neg_le_neg ht.2, neg_le_neg ht.1⟩
  simpa [z, sub_eq_add_neg, add_comm] using h

/-- A convenient constructor for the exact Picard--Lindelöf structure used by
Mathlib, specialized to a symmetric scalar box and a fixed initial value. -/
lemma apm_m93j06_isPicardLindelof_of_box
    {f : ℝ → ℝ → ℝ} {t₀ x₀ δ a Q L : ℝ}
    (hδ : 0 < δ) (ha : 0 ≤ a) (hQ : 0 ≤ Q) (hL : 0 ≤ L)
    (hLip : ∀ t x y, |f t x - f t y| ≤ L * |x - y|)
    (hcont : Continuous (Function.uncurry f))
    (hbound : ∀ t ∈ Set.Icc (t₀ - δ) (t₀ + δ),
      ∀ x ∈ Metric.closedBall x₀ a, |f t x| ≤ Q)
    (htime : Q * δ ≤ a) :
    IsPicardLindelof f
      (⟨t₀, by constructor <;> linarith⟩ : Set.Icc (t₀ - δ) (t₀ + δ))
      x₀ ⟨a, ha⟩ 0 ⟨Q, hQ⟩ ⟨L, hL⟩ := by
  refine
    { lipschitzOnWith := ?_
      continuousOn := ?_
      norm_le := ?_
      mul_max_le := ?_ }
  · intro t _
    apply LipschitzWith.lipschitzOnWith
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simpa [Real.dist_eq] using hLip t x y
  · intro x _
    exact (hcont.comp (Continuous.prodMk_left x)).continuousOn
  · intro t ht x hx
    simpa [Real.norm_eq_abs] using hbound t ht x hx
  · simpa using htime

/-- Positive initial-radius version of the scalar Picard--Lindelöf box
constructor, used to obtain a continuous family of nearby solutions. -/
lemma apm_m93j06_isPicardLindelof_of_box_radius
    {f : ℝ → ℝ → ℝ} {t₀ x₀ δ a r Q L : ℝ}
    (hδ : 0 < δ) (ha : 0 ≤ a) (hr : 0 ≤ r) (hQ : 0 ≤ Q) (hL : 0 ≤ L)
    (hLip : ∀ t ∈ Set.Icc (t₀ - δ) (t₀ + δ),
      ∀ x ∈ Metric.closedBall x₀ a, ∀ y ∈ Metric.closedBall x₀ a,
        |f t x - f t y| ≤ L * |x - y|)
    (hcont : Continuous (Function.uncurry f))
    (hbound : ∀ t ∈ Set.Icc (t₀ - δ) (t₀ + δ),
      ∀ x ∈ Metric.closedBall x₀ a, |f t x| ≤ Q)
    (htime : Q * δ ≤ a - r) :
    IsPicardLindelof f
      (⟨t₀, by constructor <;> linarith⟩ : Set.Icc (t₀ - δ) (t₀ + δ))
      x₀ ⟨a, ha⟩ ⟨r, hr⟩ ⟨Q, hQ⟩ ⟨L, hL⟩ := by
  refine
    { lipschitzOnWith := ?_
      continuousOn := ?_
      norm_le := ?_
      mul_max_le := ?_ }
  · intro t ht
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa [Real.dist_eq] using hLip t ht x hx y hy
  · intro x _
    exact (hcont.comp (Continuous.prodMk_left x)).continuousOn
  · intro t ht x hx
    simpa [Real.norm_eq_abs] using hbound t ht x hx
  · simpa using htime

/-- A positive-radius Picard box produces a solution family jointly continuous
in the initial state and time on the whole box. -/
lemma apm_m93j06_exists_continuous_local_flow_of_box_radius
    {f : ℝ → ℝ → ℝ} {t₀ x₀ δ a r Q L : ℝ}
    (hδ : 0 < δ) (ha : 0 ≤ a) (hr : 0 ≤ r) (hQ : 0 ≤ Q) (hL : 0 ≤ L)
    (hLip : ∀ t ∈ Set.Icc (t₀ - δ) (t₀ + δ),
      ∀ x ∈ Metric.closedBall x₀ a, ∀ y ∈ Metric.closedBall x₀ a,
        |f t x - f t y| ≤ L * |x - y|)
    (hcont : Continuous (Function.uncurry f))
    (hbound : ∀ t ∈ Set.Icc (t₀ - δ) (t₀ + δ),
      ∀ x ∈ Metric.closedBall x₀ a, |f t x| ≤ Q)
    (htime : Q * δ ≤ a - r) :
    ∃ α : ℝ × ℝ → ℝ,
      (∀ x ∈ Metric.closedBall x₀ r, α (x, t₀) = x ∧
        ∀ t ∈ Set.Icc (t₀ - δ) (t₀ + δ),
          HasDerivWithinAt (fun s ↦ α (x, s)) (f t (α (x, t)))
            (Set.Icc (t₀ - δ) (t₀ + δ)) t) ∧
      ContinuousOn α
        (Metric.closedBall x₀ r ×ˢ Set.Icc (t₀ - δ) (t₀ + δ)) := by
  exact IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
    (apm_m93j06_isPicardLindelof_of_box_radius
      hδ ha hr hQ hL hLip hcont hbound htime)

/-- The box constructor immediately yields a local solution on its symmetric
closed time interval. -/
lemma apm_m93j06_exists_local_solution_of_box
    {f : ℝ → ℝ → ℝ} {t₀ x₀ δ a Q L : ℝ}
    (hδ : 0 < δ) (ha : 0 ≤ a) (hQ : 0 ≤ Q) (hL : 0 ≤ L)
    (hLip : ∀ t x y, |f t x - f t y| ≤ L * |x - y|)
    (hcont : Continuous (Function.uncurry f))
    (hbound : ∀ t ∈ Set.Icc (t₀ - δ) (t₀ + δ),
      ∀ x ∈ Metric.closedBall x₀ a, |f t x| ≤ Q)
    (htime : Q * δ ≤ a) :
    ∃ y : ℝ → ℝ, y t₀ = x₀ ∧
      ∀ t ∈ Set.Icc (t₀ - δ) (t₀ + δ),
        HasDerivWithinAt y (f t (y t))
          (Set.Icc (t₀ - δ) (t₀ + δ)) t := by
  exact IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    (apm_m93j06_isPicardLindelof_of_box hδ ha hQ hL hLip hcont hbound htime)

/-- Joint continuity and a global state-variable Lipschitz constant produce an
actual local solution around every time-state point. -/
lemma apm_m93j06_exists_local_solution
    {f : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ t x y, |f t x - f t y| ≤ L * |x - y|)
    (hcont : Continuous (Function.uncurry f)) (t₀ x₀ : ℝ) :
    ∃ δ > 0, ∃ y : ℝ → ℝ, y t₀ = x₀ ∧
      ∀ t ∈ Set.Icc (t₀ - δ) (t₀ + δ),
        HasDerivWithinAt y (f t (y t))
          (Set.Icc (t₀ - δ) (t₀ + δ)) t := by
  have hcompact : IsCompact
      (Set.Icc (t₀ - 1) (t₀ + 1) ×ˢ Metric.closedBall x₀ 1) :=
    isCompact_Icc.prod (isCompact_closedBall x₀ 1)
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hcont.continuousOn
  let Q := max C 1
  have hQone : 1 ≤ Q := le_max_right _ _
  have hQ : 0 < Q := zero_lt_one.trans_le hQone
  let δ := Q⁻¹
  have hδ : 0 < δ := inv_pos.mpr hQ
  have hδone : δ ≤ 1 := by
    exact (inv_le_one₀ hQ).mpr hQone
  have hbound : ∀ t ∈ Set.Icc (t₀ - δ) (t₀ + δ),
      ∀ x ∈ Metric.closedBall x₀ (1 : ℝ), |f t x| ≤ Q := by
    intro t ht x hx
    have ht' : t ∈ Set.Icc (t₀ - 1) (t₀ + 1) := by
      exact ⟨by linarith [ht.1, hδone], by linarith [ht.2, hδone]⟩
    have hb := hC (t, x) ⟨ht', hx⟩
    have hb' : |f t x| ≤ C := by
      simpa [Function.uncurry, Real.norm_eq_abs] using hb
    exact hb'.trans (le_max_left C 1)
  refine ⟨δ, hδ, ?_⟩
  apply apm_m93j06_exists_local_solution_of_box hδ (by norm_num) (le_of_lt hQ) hL
    hLip hcont hbound
  dsimp [δ]
  rw [mul_inv_cancel₀ hQ.ne']

/-- On a compact time interval and bounded state region, the local existence
lifespan can be chosen uniformly. -/
lemma apm_m93j06_exists_uniform_local_solution
    {f : ℝ → ℝ → ℝ} {L A B R : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ t x y, |f t x - f t y| ≤ L * |x - y|)
    (hcont : Continuous (Function.uncurry f)) :
    ∃ δ > 0, ∀ t₀ ∈ Set.Icc A B, ∀ x₀ ∈ Metric.closedBall 0 R,
      ∃ y : ℝ → ℝ, y t₀ = x₀ ∧
        ∀ t ∈ Set.Icc (t₀ - δ) (t₀ + δ),
          HasDerivWithinAt y (f t (y t))
            (Set.Icc (t₀ - δ) (t₀ + δ)) t := by
  have hcompact : IsCompact
      (Set.Icc (A - 1) (B + 1) ×ˢ Metric.closedBall (0 : ℝ) (R + 1)) :=
    isCompact_Icc.prod (isCompact_closedBall (0 : ℝ) (R + 1))
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hcont.continuousOn
  let Q := max C 1
  have hQone : 1 ≤ Q := le_max_right _ _
  have hQ : 0 < Q := zero_lt_one.trans_le hQone
  let δ := Q⁻¹
  have hδ : 0 < δ := inv_pos.mpr hQ
  have hδone : δ ≤ 1 := (inv_le_one₀ hQ).mpr hQone
  refine ⟨δ, hδ, ?_⟩
  intro t₀ ht₀ x₀ hx₀
  have hbound : ∀ t ∈ Set.Icc (t₀ - δ) (t₀ + δ),
      ∀ x ∈ Metric.closedBall x₀ (1 : ℝ), |f t x| ≤ Q := by
    intro t ht x hx
    have htt : t ∈ Set.Icc (A - 1) (B + 1) :=
      ⟨by linarith [ht.1, ht₀.1, hδone], by linarith [ht.2, ht₀.2, hδone]⟩
    have hxx : x ∈ Metric.closedBall 0 (R + 1) := by
      rw [Metric.mem_closedBall, Real.dist_eq] at hx₀ hx ⊢
      calc
        |x - 0| ≤ |x - x₀| + |x₀ - 0| := by
          rw [show x - 0 = (x - x₀) + (x₀ - 0) by ring]
          exact abs_add_le _ _
        _ ≤ 1 + R := add_le_add hx hx₀
        _ = R + 1 := add_comm _ _
    have hb := hC (t, x) ⟨htt, hxx⟩
    have hb' : |f t x| ≤ C := by
      simpa [Function.uncurry, Real.norm_eq_abs] using hb
    exact hb'.trans (le_max_left C 1)
  apply apm_m93j06_exists_local_solution_of_box hδ (by norm_num) (le_of_lt hQ) hL
    hLip hcont hbound
  dsimp [δ]
  rw [mul_inv_cancel₀ hQ.ne']

/-- A field bound along an interval solution gives a time-Lipschitz bound for
the trajectory. This supplies the Cauchy control needed at finite maximal
endpoints. -/
lemma apm_m93j06_interval_solution_lipschitzOn
    {f : ℝ → ℝ → ℝ} {A B Q : ℝ} (hQ : 0 ≤ Q) {y : ℝ → ℝ}
    (hy : ∀ t ∈ Set.Icc A B,
      HasDerivWithinAt y (f t (y t)) (Set.Icc A B) t)
    (hbound : ∀ t ∈ Set.Icc A B, |f t (y t)| ≤ Q) :
    LipschitzOnWith ⟨Q, hQ⟩ y (Set.Icc A B) := by
  apply Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (convex_Icc A B) hy
  intro t ht
  exact_mod_cast (by simpa [Real.norm_eq_abs] using hbound t ht)

/-- Explicit metric form of the preceding time-Lipschitz estimate. -/
lemma apm_m93j06_interval_solution_dist_le
    {f : ℝ → ℝ → ℝ} {A B Q : ℝ} (hQ : 0 ≤ Q) {y : ℝ → ℝ}
    (hy : ∀ t ∈ Set.Icc A B,
      HasDerivWithinAt y (f t (y t)) (Set.Icc A B) t)
    (hbound : ∀ t ∈ Set.Icc A B, |f t (y t)| ≤ Q)
    {s t : ℝ} (hs : s ∈ Set.Icc A B) (ht : t ∈ Set.Icc A B) :
    |y s - y t| ≤ Q * |s - t| := by
  simpa [Real.dist_eq] using
    (apm_m93j06_interval_solution_lipschitzOn hQ hy hbound).dist_le_mul s hs t ht

/-- Two interval solutions agreeing at an interior time agree on the whole
closed interval. This matches the within-derivative interface returned by the
Picard--Lindelöf constructor. -/
lemma apm_m93j06_interval_solution_unique
    {f : ℝ → ℝ → ℝ} {L A B τ : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ t x y, |f t x - f t y| ≤ L * |x - y|)
    (hτ : τ ∈ Set.Ioo A B) {y z : ℝ → ℝ}
    (hy : ∀ t ∈ Set.Icc A B,
      HasDerivWithinAt y (f t (y t)) (Set.Icc A B) t)
    (hz : ∀ t ∈ Set.Icc A B,
      HasDerivWithinAt z (f t (z t)) (Set.Icc A B) t)
    (heq : y τ = z τ) : Set.EqOn y z (Set.Icc A B) := by
  let K : NNReal := ⟨L, hL⟩
  have hv : ∀ t, LipschitzWith K (f t) := by
    intro t
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simpa [K, Real.dist_eq] using hLip t x y
  apply ODE_solution_unique_of_mem_Icc (s := fun _ ↦ Set.univ) (K := K)
    (fun t _ ↦ (hv t).lipschitzOnWith) hτ
    (HasDerivWithinAt.continuousOn hy)
    (fun t ht ↦ (hy t (Set.Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2))
    (fun _ _ ↦ Set.mem_univ _)
    (HasDerivWithinAt.continuousOn hz)
    (fun t ht ↦ (hz t (Set.Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2))
    (fun _ _ ↦ Set.mem_univ _) heq

/-- Compatibility on the closed overlap of two interval solutions, provided
their common anchor lies in the overlap interior. -/
lemma apm_m93j06_interval_solutions_eqOn_overlap
    {f : ℝ → ℝ → ℝ} {L A B C D τ : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ t x y, |f t x - f t y| ≤ L * |x - y|)
    (hτ : τ ∈ Set.Ioo (max A C) (min B D)) {y z : ℝ → ℝ}
    (hy : ∀ t ∈ Set.Icc A B,
      HasDerivWithinAt y (f t (y t)) (Set.Icc A B) t)
    (hz : ∀ t ∈ Set.Icc C D,
      HasDerivWithinAt z (f t (z t)) (Set.Icc C D) t)
    (heq : y τ = z τ) :
    Set.EqOn y z (Set.Icc (max A C) (min B D)) := by
  apply apm_m93j06_interval_solution_unique hL hLip hτ
  · intro t ht
    exact (hy t ⟨le_trans (le_max_left _ _) ht.1,
      ht.2.trans (min_le_left _ _)⟩).mono
      (Set.Icc_subset_Icc (le_max_left _ _) (min_le_left _ _))
  · intro t ht
    exact (hz t ⟨le_trans (le_max_right _ _) ht.1,
      ht.2.trans (min_le_right _ _)⟩).mono
      (Set.Icc_subset_Icc (le_max_right _ _) (min_le_right _ _))
  · exact heq

/-- Glue two adjacent closed-interval solutions at a common endpoint. -/
lemma apm_m93j06_exists_glued_interval_solution
    {f : ℝ → ℝ → ℝ} {A B C : ℝ} (hAB : A < B) (hBC : B < C)
    {y z : ℝ → ℝ}
    (hy : ∀ t ∈ Set.Icc A B,
      HasDerivWithinAt y (f t (y t)) (Set.Icc A B) t)
    (hz : ∀ t ∈ Set.Icc B C,
      HasDerivWithinAt z (f t (z t)) (Set.Icc B C) t)
    (heq : y B = z B) :
    ∃ w : ℝ → ℝ, Set.EqOn w y (Set.Icc A B) ∧
      Set.EqOn w z (Set.Icc B C) ∧
      ∀ t ∈ Set.Icc A C,
        HasDerivWithinAt w (f t (w t)) (Set.Icc A C) t := by
  let w : ℝ → ℝ := fun t ↦ if t ≤ B then y t else z t
  have hwy : Set.EqOn w y (Set.Icc A B) := by
    intro t ht
    simp [w, ht.2]
  have hwz : Set.EqOn w z (Set.Icc B C) := by
    intro t ht
    by_cases h : t ≤ B
    · have htB : t = B := le_antisymm h ht.1
      simp [w, htB, heq]
    · simp [w, h]
  refine ⟨w, hwy, hwz, ?_⟩
  intro t ht
  rcases lt_trichotomy t B with hlt | he | hgt
  · have htleft : t ∈ Set.Icc A B := ⟨ht.1, le_of_lt hlt⟩
    have hd := (hy t htleft).congr_of_mem hwy htleft
    have hnear : Set.Icc A B ∈ nhdsWithin t (Set.Icc A C) := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hlt)] with s hs hsB
      exact ⟨hs.1, hsB⟩
    exact (hd.mono_of_mem_nhdsWithin hnear).congr_deriv (by rw [hwy htleft])
  · subst t
    have hBleft : B ∈ Set.Icc A B := ⟨le_of_lt hAB, le_rfl⟩
    have hBright : B ∈ Set.Icc B C := ⟨le_rfl, le_of_lt hBC⟩
    have hdl := (hy B hBleft).congr_of_mem hwy hBleft
    have hdr := (hz B hBright).congr_of_mem hwz hBright
    have hdr' : HasDerivWithinAt w (f B (y B)) (Set.Icc B C) B := by
      simpa [heq] using hdr
    rw [← Set.Icc_union_Icc_eq_Icc (le_of_lt hAB) (le_of_lt hBC)]
    exact (hdl.union hdr').congr_deriv (by rw [hwy hBleft])
  · have htright : t ∈ Set.Icc B C := ⟨le_of_lt hgt, ht.2⟩
    have hd := (hz t htright).congr_of_mem hwz htright
    have hnear : Set.Icc B C ∈ nhdsWithin t (Set.Icc A C) := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds hgt)] with s hs hsB
      exact ⟨hsB, hs.2⟩
    exact (hd.mono_of_mem_nhdsWithin hnear).congr_deriv (by rw [hwz htright])

/-- Every nondegenerate interval solution admits a genuine extension to the
right, preserving the old trajectory on its whole interval. -/
lemma apm_m93j06_exists_extension_right
    {f : ℝ → ℝ → ℝ} {L A B : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ t x y, |f t x - f t y| ≤ L * |x - y|)
    (hcont : Continuous (Function.uncurry f)) (hAB : A < B) {y : ℝ → ℝ}
    (hy : ∀ t ∈ Set.Icc A B,
      HasDerivWithinAt y (f t (y t)) (Set.Icc A B) t) :
    ∃ δ > 0, ∃ w : ℝ → ℝ, Set.EqOn w y (Set.Icc A B) ∧
      ∀ t ∈ Set.Icc A (B + δ),
        HasDerivWithinAt w (f t (w t)) (Set.Icc A (B + δ)) t := by
  obtain ⟨δ, hδ, z, hzB, hz⟩ :=
    apm_m93j06_exists_local_solution hL hLip hcont B (y B)
  have hzright : ∀ t ∈ Set.Icc B (B + δ),
      HasDerivWithinAt z (f t (z t)) (Set.Icc B (B + δ)) t := by
    intro t ht
    exact (hz t ⟨by linarith [ht.1], ht.2⟩).mono
      (Set.Icc_subset_Icc (by linarith) le_rfl)
  obtain ⟨w, hwy, _, hw⟩ :=
    apm_m93j06_exists_glued_interval_solution (A := A) (B := B) (C := B + δ)
      hAB (by linarith) hy hzright hzB.symm
  exact ⟨δ, hδ, w, hwy, hw⟩

/-- Every nondegenerate interval solution admits a genuine extension to the
left, preserving the old trajectory on its whole interval. -/
lemma apm_m93j06_exists_extension_left
    {f : ℝ → ℝ → ℝ} {L A B : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ t x y, |f t x - f t y| ≤ L * |x - y|)
    (hcont : Continuous (Function.uncurry f)) (hAB : A < B) {y : ℝ → ℝ}
    (hy : ∀ t ∈ Set.Icc A B,
      HasDerivWithinAt y (f t (y t)) (Set.Icc A B) t) :
    ∃ δ > 0, ∃ w : ℝ → ℝ, Set.EqOn w y (Set.Icc A B) ∧
      ∀ t ∈ Set.Icc (A - δ) B,
        HasDerivWithinAt w (f t (w t)) (Set.Icc (A - δ) B) t := by
  obtain ⟨δ, hδ, z, hzA, hz⟩ :=
    apm_m93j06_exists_local_solution hL hLip hcont A (y A)
  have hzleft : ∀ t ∈ Set.Icc (A - δ) A,
      HasDerivWithinAt z (f t (z t)) (Set.Icc (A - δ) A) t := by
    intro t ht
    exact (hz t ⟨ht.1, by linarith [ht.2]⟩).mono
      (Set.Icc_subset_Icc le_rfl (by linarith))
  obtain ⟨w, _, hwy, hw⟩ :=
    apm_m93j06_exists_glued_interval_solution (A := A - δ) (B := A) (C := B)
      (by linarith) hAB hzleft hy hzA
  exact ⟨δ, hδ, w, hwy, hw⟩

/-- Endpoint extension can be made uniform while the endpoint stays in fixed
compact time and state regions. -/
lemma apm_m93j06_exists_uniform_extension_right
    {f : ℝ → ℝ → ℝ} {L T₀ T₁ R : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ t x y, |f t x - f t y| ≤ L * |x - y|)
    (hcont : Continuous (Function.uncurry f)) :
    ∃ δ > 0, ∀ {A B : ℝ} {y : ℝ → ℝ}, A < B →
      B ∈ Set.Icc T₀ T₁ → y B ∈ Metric.closedBall 0 R →
      (∀ t ∈ Set.Icc A B,
        HasDerivWithinAt y (f t (y t)) (Set.Icc A B) t) →
      ∃ w : ℝ → ℝ, Set.EqOn w y (Set.Icc A B) ∧
        ∀ t ∈ Set.Icc A (B + δ),
          HasDerivWithinAt w (f t (w t)) (Set.Icc A (B + δ)) t := by
  obtain ⟨δ, hδ, hlocal⟩ :=
    apm_m93j06_exists_uniform_local_solution (A := T₀) (B := T₁) (R := R)
      hL hLip hcont
  refine ⟨δ, hδ, ?_⟩
  intro A B y hAB hBT hyBR hy
  obtain ⟨z, hzB, hz⟩ := hlocal B hBT (y B) hyBR
  have hzright : ∀ t ∈ Set.Icc B (B + δ),
      HasDerivWithinAt z (f t (z t)) (Set.Icc B (B + δ)) t := by
    intro t ht
    exact (hz t ⟨by linarith [ht.1], ht.2⟩).mono
      (Set.Icc_subset_Icc (by linarith) le_rfl)
  obtain ⟨w, hwy, _, hw⟩ :=
    apm_m93j06_exists_glued_interval_solution (A := A) (B := B) (C := B + δ)
      hAB (by linarith) hy hzright hzB.symm
  exact ⟨w, hwy, hw⟩

/-- A positive time is reachable when there is an interval solution from the
prescribed initial value up to that time. -/
def apm_m93j06_Reachable (f : ℝ → ℝ → ℝ) (y₀ s : ℝ) : Prop :=
  0 < s ∧ ∃ y : ℝ → ℝ, y 0 = y₀ ∧
    ∀ t ∈ Set.Icc 0 s,
      HasDerivWithinAt y (f t (y t)) (Set.Icc 0 s) t

/-- Every positive target time bounds a nonempty set of reachable endpoints. -/
lemma apm_m93j06_exists_reachable_le
    {f : ℝ → ℝ → ℝ} {L T y₀ : ℝ} (hL : 0 ≤ L) (hT : 0 < T)
    (hLip : ∀ t x y, |f t x - f t y| ≤ L * |x - y|)
    (hcont : Continuous (Function.uncurry f)) :
    ∃ s, apm_m93j06_Reachable f y₀ s ∧ s ≤ T := by
  obtain ⟨δ, hδ, y, hy0, hy⟩ :=
    apm_m93j06_exists_local_solution hL hLip hcont 0 y₀
  let s := min (δ / 2) T
  have hs : 0 < s := lt_min (half_pos hδ) hT
  have hsT : s ≤ T := min_le_right _ _
  have hsδ : s ≤ δ := (min_le_left _ _).trans (half_le_self (le_of_lt hδ))
  refine ⟨s, ⟨hs, y, hy0, ?_⟩, hsT⟩
  intro t ht
  have hsδ' : s ≤ 0 + δ := by simpa using hsδ
  exact (hy t ⟨by linarith [ht.1, hδ], ht.2.trans hsδ'⟩).mono
    (Set.Icc_subset_Icc (by linarith) hsδ')

/-- The reachable-endpoint set used by the continuation supremum is nonempty
and bounded above by its target time. -/
lemma apm_m93j06_reachableSet_nonempty_bddAbove
    {f : ℝ → ℝ → ℝ} {L T y₀ : ℝ} (hL : 0 ≤ L) (hT : 0 < T)
    (hLip : ∀ t x y, |f t x - f t y| ≤ L * |x - y|)
    (hcont : Continuous (Function.uncurry f)) :
    Set.Nonempty {s : ℝ | apm_m93j06_Reachable f y₀ s ∧ s ≤ T} ∧
      BddAbove {s : ℝ | apm_m93j06_Reachable f y₀ s ∧ s ≤ T} := by
  obtain ⟨s, hsreach, hsT⟩ :=
    apm_m93j06_exists_reachable_le hL hT hLip hcont
  refine ⟨⟨s, hsreach, hsT⟩, ⟨T, ?_⟩⟩
  intro u hu
  exact hu.2

/-- All endpoints reachable before a fixed positive time lie in one explicit
state ball. -/
lemma apm_m93j06_exists_bound_reachable_le
    {f : ℝ → ℝ → ℝ} {L T y₀ : ℝ} (hL : 0 ≤ L) (hT : 0 < T)
    (hLip : ∀ t x y, |f t x - f t y| ≤ L * |x - y|)
    (hcont : Continuous (Function.uncurry f)) :
    ∃ R, ∀ s, apm_m93j06_Reachable f y₀ s → s ≤ T →
      ∀ y : ℝ → ℝ, y 0 = y₀ →
        (∀ t ∈ Set.Icc 0 s,
          HasDerivWithinAt y (f t (y t)) (Set.Icc 0 s) t) →
        y s ∈ Metric.closedBall 0 R := by
  obtain ⟨M, hM, hfield⟩ :=
    apm_m93j06_exists_compact_linear_bound (le_of_lt hT) hcont hLip
  let R := gronwallBound |y₀| L M T
  refine ⟨R, ?_⟩
  intro s hsreach hsT y hy0 hy
  have hs0 : 0 ≤ s := le_of_lt hsreach.1
  have hfield' : ∀ t ∈ Set.Ico 0 s, ‖f t (y t)‖ ≤ L * ‖y t‖ + M := by
    intro t ht
    simpa [Real.norm_eq_abs, add_comm] using
      hfield t ⟨ht.1, (le_of_lt ht.2).trans hsT⟩ (y t)
  have hy' : ∀ t ∈ Set.Ico 0 s,
      HasDerivWithinAt y (f t (y t)) (Set.Ici t) t := by
    intro t ht
    have htIcc : t ∈ Set.Icc 0 s := ⟨ht.1, le_of_lt ht.2⟩
    have hnear : Set.Icc 0 s ∈ nhdsWithin t (Set.Ici t) := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds ht.2)] with u hu hus
      exact ⟨ht.1.trans hu, hus⟩
    exact (hy t htIcc).mono_of_mem_nhdsWithin hnear
  have hend : |y s| ≤ gronwallBound |y₀| L M s := by
    have h := norm_le_gronwallBound_of_norm_deriv_right_le
      (δ := |y₀|) (HasDerivWithinAt.continuousOn hy) hy'
      (by simp [hy0, Real.norm_eq_abs]) hfield' s ⟨hs0, le_rfl⟩
    simpa [Real.norm_eq_abs] using h
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
  exact hend.trans (gronwallBound_mono (abs_nonneg y₀) hM hL hsT)


/-- Every positive target time is reachable.  The proof takes the supremum of
the reachable endpoints and uses a uniform Picard restart to rule out a gap
before the target. -/
lemma apm_m93j06_exists_forward_interval_solution
    {f : ℝ → ℝ → ℝ} {L T y₀ : ℝ} (hL : 0 ≤ L) (hT : 0 < T)
    (hLip : ∀ t x y, |f t x - f t y| ≤ L * |x - y|)
    (hcont : Continuous (Function.uncurry f)) :
    ∃ y : ℝ → ℝ, y 0 = y₀ ∧
      ∀ t ∈ Set.Icc 0 T,
        HasDerivWithinAt y (f t (y t)) (Set.Icc 0 T) t := by
  let S : Set ℝ := {s | apm_m93j06_Reachable f y₀ s ∧ s ≤ T}
  obtain ⟨hSne, hSbdd⟩ :=
    apm_m93j06_reachableSet_nonempty_bddAbove hL hT hLip hcont
  obtain ⟨R, hR⟩ :=
    apm_m93j06_exists_bound_reachable_le hL hT hLip hcont
  obtain ⟨δ, hδ, hext⟩ :=
    apm_m93j06_exists_uniform_extension_right
      (T₀ := 0) (T₁ := T) (R := R) hL hLip hcont
  have hsup_le : sSup S ≤ T := by
    exact csSup_le hSne fun s hs ↦ hs.2
  have hT_le_sup : T ≤ sSup S := by
    by_contra hnot
    have hsup_lt_T : sSup S < T := lt_of_not_ge hnot
    obtain ⟨s, hsS, hsclose⟩ :=
      exists_lt_of_lt_csSup hSne (sub_lt_self (sSup S) (half_pos hδ))
    rcases hsS.1 with ⟨hs0, y, hy0, hy⟩
    have hyR : y s ∈ Metric.closedBall 0 R :=
      hR s ⟨hs0, y, hy0, hy⟩ hsS.2 y hy0 hy
    obtain ⟨w, hwy, hw⟩ :=
      hext hs0 ⟨le_of_lt hs0, hsS.2⟩ hyR hy
    let u := min T (s + δ / 2)
    have hsup_lt_u : sSup S < u := by
      apply lt_min hsup_lt_T
      linarith
    have hu0 : 0 < u :=
      hs0.trans (lt_of_le_of_lt (le_csSup hSbdd hsS) hsup_lt_u)
    have huT : u ≤ T := min_le_left _ _
    have hu_ext : u ≤ s + δ := by
      exact (min_le_right _ _).trans (by linarith [hδ])
    have hw0 : w 0 = y₀ := (hwy ⟨le_rfl, le_of_lt hs0⟩).trans hy0
    have huReach : apm_m93j06_Reachable f y₀ u := by
      refine ⟨hu0, w, hw0, ?_⟩
      intro t ht
      exact (hw t ⟨ht.1, ht.2.trans hu_ext⟩).mono
        (Set.Icc_subset_Icc le_rfl hu_ext)
    have huS : u ∈ S := ⟨huReach, huT⟩
    exact (not_lt_of_ge (le_csSup hSbdd huS)) hsup_lt_u
  have hsup_eq : sSup S = T := le_antisymm hsup_le hT_le_sup
  have hnear : T - δ / 2 < sSup S := by
    rw [hsup_eq]
    exact sub_lt_self _ (half_pos hδ)
  obtain ⟨s, hsS, hsclose⟩ := exists_lt_of_lt_csSup hSne hnear
  rcases hsS.1 with ⟨hs0, y, hy0, hy⟩
  have hyR : y s ∈ Metric.closedBall 0 R :=
    hR s ⟨hs0, y, hy0, hy⟩ hsS.2 y hy0 hy
  obtain ⟨w, hwy, hw⟩ :=
    hext hs0 ⟨le_of_lt hs0, hsS.2⟩ hyR hy
  have hT_ext : T ≤ s + δ := by linarith
  have hw0 : w 0 = y₀ := (hwy ⟨le_rfl, le_of_lt hs0⟩).trans hy0
  refine ⟨w, hw0, ?_⟩
  intro t ht
  exact (hw t ⟨ht.1, ht.2.trans hT_ext⟩).mono
    (Set.Icc_subset_Icc le_rfl hT_ext)

/-- Time reversal transports finite forward existence to a solution on every
finite interval ending at the initial time. -/
lemma apm_m93j06_exists_backward_interval_solution
    {f : ℝ → ℝ → ℝ} {L T y₀ : ℝ} (hL : 0 ≤ L) (hT : 0 < T)
    (hLip : ∀ t x y, |f t x - f t y| ≤ L * |x - y|)
    (hcont : Continuous (Function.uncurry f)) :
    ∃ y : ℝ → ℝ, y 0 = y₀ ∧
      ∀ t ∈ Set.Icc (-T) 0,
        HasDerivWithinAt y (f t (y t)) (Set.Icc (-T) 0) t := by
  let g : ℝ → ℝ → ℝ := fun s x ↦ -f (-s) x
  have hgcont : Continuous (Function.uncurry g) := by
    dsimp [g, Function.uncurry]
    fun_prop
  have hgLip : ∀ t x y, |g t x - g t y| ≤ L * |x - y| := by
    intro t x y
    change |-f (-t) x - -f (-t) y| ≤ L * |x - y|
    rw [show -f (-t) x - -f (-t) y = -(f (-t) x - f (-t) y) by ring,
      abs_neg]
    exact hLip (-t) x y
  obtain ⟨z, hz0, hz⟩ :=
    apm_m93j06_exists_forward_interval_solution hL hT hgLip hgcont (y₀ := y₀)
  let y : ℝ → ℝ := fun t ↦ z (-t)
  refine ⟨y, by simpa [y] using hz0, ?_⟩
  intro t ht
  have hnt : -t ∈ Set.Icc 0 T := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hcomp := (hz (-t) hnt).comp t
    ((hasDerivAt_neg t).hasDerivWithinAt (s := Set.Icc (-T) 0))
    (fun u hu ↦ ⟨by linarith [hu.2], by linarith [hu.1]⟩)
  simpa [y, g] using hcomp

/-- Forward and backward compact solutions glue at their common initial value
to solve the ODE on any prescribed symmetric compact interval. -/
lemma apm_m93j06_exists_symmetric_interval_solution
    {f : ℝ → ℝ → ℝ} {L T y₀ : ℝ} (hL : 0 ≤ L) (hT : 0 < T)
    (hLip : ∀ t x y, |f t x - f t y| ≤ L * |x - y|)
    (hcont : Continuous (Function.uncurry f)) :
    ∃ y : ℝ → ℝ, y 0 = y₀ ∧
      ∀ t ∈ Set.Icc (-T) T,
        HasDerivWithinAt y (f t (y t)) (Set.Icc (-T) T) t := by
  obtain ⟨yneg, hyneg0, hyneg⟩ :=
    apm_m93j06_exists_backward_interval_solution hL hT hLip hcont (y₀ := y₀)
  obtain ⟨ypos, hypos0, hypos⟩ :=
    apm_m93j06_exists_forward_interval_solution hL hT hLip hcont (y₀ := y₀)
  obtain ⟨y, hyneg, hypos, hy⟩ :=
    apm_m93j06_exists_glued_interval_solution
      (A := -T) (B := 0) (C := T) (by linarith) hT
      hyneg hypos (hyneg0.trans hypos0.symm)
  refine ⟨y, ?_, hy⟩
  exact (hyneg ⟨by linarith, le_rfl⟩).trans hyneg0

/-- Compatible symmetric compact solutions globalize to a trajectory on all
of `ℝ`.  Although the chosen compact solution varies with the evaluation
time, uniqueness makes the resulting function locally equal to any one
sufficiently large chosen solution. -/
lemma apm_m93j06_exists_global_solution
    {f : ℝ → ℝ → ℝ} {L y₀ : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ t x y, |f t x - f t y| ≤ L * |x - y|)
    (hcont : Continuous (Function.uncurry f)) :
    ∃ y : ℝ → ℝ, apm_m93j06_Solves f y₀ y := by
  have hex : ∀ a : ℝ, ∃ y : ℝ → ℝ, y 0 = y₀ ∧
      ∀ t ∈ Set.Icc (-(|a| + 1)) (|a| + 1),
        HasDerivWithinAt y (f t (y t))
          (Set.Icc (-(|a| + 1)) (|a| + 1)) t := by
    intro a
    exact apm_m93j06_exists_symmetric_interval_solution hL
      (by positivity : 0 < |a| + 1) hLip hcont
  choose γ hγ0 hγ using hex
  have hcompat : ∀ a b x : ℝ,
      x ∈ Set.Icc (-(|a| + 1)) (|a| + 1) →
      x ∈ Set.Icc (-(|b| + 1)) (|b| + 1) → γ a x = γ b x := by
    intro a b x hxa hxb
    have hzero : 0 ∈ Set.Ioo
        (max (-(|a| + 1)) (-(|b| + 1)))
        (min (|a| + 1) (|b| + 1)) := by
      constructor
      · apply max_lt <;> linarith [abs_nonneg a, abs_nonneg b]
      · exact lt_min (by positivity) (by positivity)
    have heq := apm_m93j06_interval_solutions_eqOn_overlap hL hLip hzero
      (hγ a) (hγ b) ((hγ0 a).trans (hγ0 b).symm)
    apply heq
    exact ⟨max_le hxa.1 hxb.1, le_min hxa.2 hxb.2⟩
  let y : ℝ → ℝ := fun t ↦ γ t t
  refine ⟨y, ?_, ?_⟩
  · exact hγ0 0
  · intro t
    have htmem : t ∈ Set.Ioo (-(|t| + 1)) (|t| + 1) := by
      rw [Set.mem_Ioo, ← abs_lt]
      exact lt_add_one _
    have hfixed : HasDerivAt (γ t) (f t (γ t t)) t :=
      (hγ t t (Set.Ioo_subset_Icc_self htmem)).hasDerivAt
        (Icc_mem_nhds htmem.1 htmem.2)
    have hevent : y =ᶠ[nhds t] γ t := by
      filter_upwards [Ioo_mem_nhds htmem.1 htmem.2] with s hs
      apply hcompat s t s
      · constructor
        · calc
            -(|s| + 1) ≤ -|s| := by linarith
            _ ≤ s := neg_abs_le s
        · calc
            s ≤ |s| := le_abs_self s
            _ ≤ |s| + 1 := by linarith
      · exact Set.Ioo_subset_Icc_self hs
    simpa [y] using hfixed.congr_of_eventuallyEq hevent

/-- Global solutions with the same initial value are unique under a uniform
Lipschitz bound in the dependent variable. -/
lemma apm_m93j06_solution_unique
    {f : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ t a b, |f t a - f t b| ≤ L * |a - b|)
    {y₀ : ℝ} {y z : ℝ → ℝ}
    (hy : apm_m93j06_Solves f y₀ y) (hz : apm_m93j06_Solves f y₀ z) : y = z := by
  let K : NNReal := ⟨L, hL⟩
  have hv : ∀ t, LipschitzWith K (f t) := by
    intro t
    rw [lipschitzWith_iff_dist_le_mul]
    intro a b
    simpa [K, Real.dist_eq] using hLip t a b
  apply ODE_solution_unique_univ (s := fun _ ↦ Set.univ) (K := K)
      (fun t ↦ (hv t).lipschitzOnWith)
      (fun t ↦ ⟨hy.2 t, Set.mem_univ _⟩)
      (fun t ↦ ⟨hz.2 t, Set.mem_univ _⟩)
  exact hy.1.trans hz.1.symm

/-- Once global existence is available, the compiled Grönwall uniqueness
argument upgrades it to the exact `∃!` interface used by the frozen theorem. -/
lemma apm_m93j06_existsUnique_of_exists
    {f : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ t a b, |f t a - f t b| ≤ L * |a - b|)
    (hex : ∀ y₀, ∃ y : ℝ → ℝ, apm_m93j06_Solves f y₀ y) :
    ∀ y₀, ∃! y : ℝ → ℝ, apm_m93j06_Solves f y₀ y := by
  intro y₀
  obtain ⟨y, hy⟩ := hex y₀
  refine ⟨y, hy, fun z hz ↦ ?_⟩
  exact apm_m93j06_solution_unique hL hLip hz hy

/-- The compact continuation construction and global uniqueness together give
the exact first conjunct of the main theorem. -/
lemma apm_m93j06_global_existsUnique
    (f : ℝ → ℝ → ℝ) (hcont : Continuous (Function.uncurry f))
    (hLip : ∃ L > 0, ∀ t x y, |f t x - f t y| ≤ L * |x - y|) :
    ∀ y₀, ∃! y : ℝ → ℝ, apm_m93j06_Solves f y₀ y := by
  obtain ⟨L, hL, hLip⟩ := hLip
  apply apm_m93j06_existsUnique_of_exists (le_of_lt hL) hLip
  intro y₀
  exact apm_m93j06_exists_global_solution (le_of_lt hL) hLip hcont

/-- Pointwise choice packages a family of global solutions into the custom
flow predicate. -/
lemma apm_m93j06_isFlow_of_existsUnique
    {f : ℝ → ℝ → ℝ}
    (h : ∀ y₀, ∃! y : ℝ → ℝ, apm_m93j06_Solves f y₀ y) :
    ∃ φ, apm_m93j06_IsFlow f φ := by
  let φ : ℝ → ℝ → ℝ := fun t y₀ ↦ Classical.choose (h y₀).exists t
  refine ⟨φ, fun y₀ ↦ ?_⟩
  exact (Classical.choose_spec (h y₀).exists)

/-- The global existence-and-uniqueness clause immediately supplies the flow
needed by the linear-growth clause; the growth assumption is stronger than
needed at this packaging stage. -/
lemma apm_m93j06_growth_flow_of_global_existence
    (hglobal : ∀ f : ℝ → ℝ → ℝ, Continuous (Function.uncurry f) →
      (∃ L > 0, ∀ t a b, |f t a - f t b| ≤ L * |a - b|) →
      ∀ y₀, ∃! y : ℝ → ℝ, apm_m93j06_Solves f y₀ y) :
    ∀ f C, 0 ≤ C → Continuous (Function.uncurry f) →
      (∀ t y, |f t y| ≤ C * |y|) →
      (∃ L > 0, ∀ t a b, |f t a - f t b| ≤ L * |a - b|) →
      ∃ φ, apm_m93j06_IsFlow f φ := by
  intro f C _ hcont _ hLip
  exact apm_m93j06_isFlow_of_existsUnique (hglobal f hcont hLip)

/-- Global Lipschitz dependence of any global flow, obtained by applying
Grönwall forward in time and to the time-reversed ODE backward in time. -/
lemma apm_m93j06_flow_lipschitz
    {f φ : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hφ : apm_m93j06_IsFlow f φ)
    (hLip : ∀ t a b, |f t a - f t b| ≤ L * |a - b|) :
    ∀ t a b, |φ t a - φ t b| ≤ Real.exp (L * |t|) * |a - b| := by
  let K : NNReal := ⟨L, hL⟩
  have hv : ∀ t, LipschitzWith K (f t) := by
    intro t
    rw [lipschitzWith_iff_dist_le_mul]
    intro a b
    simpa [K, Real.dist_eq] using hLip t a b
  intro t a b
  by_cases ht : 0 ≤ t
  · have h := dist_le_of_trajectories_ODE (a := 0) (b := t) (K := K)
        (δ := dist a b)
        hv
        (continuous_iff_continuousAt.mpr
          (fun s ↦ (apm_m93j06_flow_hasDerivAt hφ a s).continuousAt)).continuousOn
        (fun s _ ↦ (apm_m93j06_flow_hasDerivAt hφ a s).hasDerivWithinAt)
        (continuous_iff_continuousAt.mpr
          (fun s ↦ (apm_m93j06_flow_hasDerivAt hφ b s).continuousAt)).continuousOn
        (fun s _ ↦ (apm_m93j06_flow_hasDerivAt hφ b s).hasDerivWithinAt)
        (by rw [apm_m93j06_flow_zero hφ, apm_m93j06_flow_zero hφ]) t ⟨ht, le_rfl⟩
    simpa [K, Real.dist_eq, abs_of_nonneg ht, mul_comm] using h
  · have ht' : 0 ≤ -t := neg_nonneg.mpr (le_of_not_ge ht)
    let v : ℝ → ℝ → ℝ := fun s x ↦ -f (-s) x
    let ya : ℝ → ℝ := fun s ↦ φ (-s) a
    let yb : ℝ → ℝ := fun s ↦ φ (-s) b
    have hv' : ∀ s, LipschitzWith K (v s) := by
      intro s
      rw [lipschitzWith_iff_dist_le_mul]
      intro x y
      simpa [K, v, Real.dist_eq] using hLip (-s) x y
    have hya : ∀ s, HasDerivAt ya (v s (ya s)) s := by
      intro s
      simpa [ya, v] using
        (apm_m93j06_flow_hasDerivAt hφ a (-s)).comp s (hasDerivAt_neg s)
    have hyb : ∀ s, HasDerivAt yb (v s (yb s)) s := by
      intro s
      simpa [yb, v] using
        (apm_m93j06_flow_hasDerivAt hφ b (-s)).comp s (hasDerivAt_neg s)
    have h := dist_le_of_trajectories_ODE (a := 0) (b := -t) (K := K)
        (δ := dist a b)
        hv' (continuous_iff_continuousAt.mpr (fun s ↦ (hya s).continuousAt)).continuousOn
        (fun s _ ↦ (hya s).hasDerivWithinAt)
        (continuous_iff_continuousAt.mpr (fun s ↦ (hyb s).continuousAt)).continuousOn
        (fun s _ ↦ (hyb s).hasDerivWithinAt)
        (by simp [ya, yb, apm_m93j06_flow_zero hφ]) (-t) ⟨ht', le_rfl⟩
    simpa [K, ya, yb, Real.dist_eq, abs_of_nonpos (le_of_not_ge ht), mul_comm] using h

/-- The derivative of a time-dependent scalar field in its state coordinate,
expressed directly through the Fréchet derivative of the uncurried field. -/
noncomputable def apm_m93j06_partialY (f : ℝ → ℝ → ℝ) (t y : ℝ) : ℝ :=
  fderiv ℝ (Function.uncurry f) (t, y) (0, 1)

/-- A jointly `C¹` field has a jointly continuous state derivative. -/
lemma apm_m93j06_continuous_partialY {f : ℝ → ℝ → ℝ}
    (hf : ContDiff ℝ 1 (Function.uncurry f)) :
    Continuous (Function.uncurry (apm_m93j06_partialY f)) := by
  change Continuous (fun p : ℝ × ℝ ↦
    fderiv ℝ (Function.uncurry f) p (0, 1))
  exact (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

/-- The preceding Fréchet-coordinate expression is the ordinary derivative
of each fixed-time slice. -/
lemma apm_m93j06_hasDerivAt_slice {f : ℝ → ℝ → ℝ}
    (hf : ContDiff ℝ 1 (Function.uncurry f)) (t y : ℝ) :
    HasDerivAt (f t) (apm_m93j06_partialY f t y) y := by
  have hp : HasDerivAt (fun x : ℝ ↦ (t, x)) (0, 1) y := by
    simpa using (hasDerivAt_const y t).prodMk (hasDerivAt_id y)
  have hF := (hf.differentiable (by norm_num) (t, y)).hasFDerivAt
  simpa [apm_m93j06_partialY, Function.uncurry] using hF.comp_hasDerivAt y hp

/-- The divided-difference coefficient of a `C¹` slice extends continuously
across the diagonal, with diagonal value equal to the state derivative. -/
lemma apm_m93j06_continuousAt_dslope_slice {f : ℝ → ℝ → ℝ}
    (hf : ContDiff ℝ 1 (Function.uncurry f)) (t y : ℝ) :
    ContinuousAt (dslope (f t) y) y := by
  exact continuousAt_dslope_same.mpr
    (apm_m93j06_hasDerivAt_slice hf t y).differentiableAt

/-- The difference of two trajectories is an exact scalar linear ODE whose
coefficient is the divided difference of the field.  This identity remains
valid when the trajectories meet because `dslope` uses the slice derivative
on the diagonal. -/
lemma apm_m93j06_flow_difference_hasDerivAt
    {f φ : ℝ → ℝ → ℝ} (hφ : apm_m93j06_IsFlow f φ) (a b t : ℝ) :
    HasDerivAt (fun s ↦ φ s b - φ s a)
      ((φ t b - φ t a) * dslope (f t) (φ t a) (φ t b)) t := by
  have hd := (apm_m93j06_flow_hasDerivAt hφ b t).sub
    (apm_m93j06_flow_hasDerivAt hφ a t)
  convert hd using 1
  simpa [smul_eq_mul, mul_comm] using
    (sub_smul_dslope (f t) (φ t a) (φ t b))

/-- Away from the initial-data diagonal, the normalized flow difference starts
at one and solves the same linear secant equation. -/
lemma apm_m93j06_flow_quotient_solves
    {f φ : ℝ → ℝ → ℝ} (hφ : apm_m93j06_IsFlow f φ) {a b : ℝ}
    (hab : b ≠ a) :
    let q : ℝ → ℝ := fun t ↦ (φ t b - φ t a) / (b - a)
    q 0 = 1 ∧ ∀ t, HasDerivAt q
      (q t * dslope (f t) (φ t a) (φ t b)) t := by
  let q : ℝ → ℝ := fun t ↦ (φ t b - φ t a) / (b - a)
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab
  constructor
  · simp [apm_m93j06_flow_zero hφ, hba]
  · intro t
    have hd := (apm_m93j06_flow_difference_hasDerivAt hφ a b t).div_const (b - a)
    convert hd using 1
    dsimp [q]
    field_simp [hba]


/-- Explicit fundamental solution of a continuous scalar linear ODE. -/
noncomputable def apm_m93j06_linearSolution (c : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (∫ s in (0 : ℝ)..t, c s)

lemma apm_m93j06_linearSolution_zero (c : ℝ → ℝ) :
    apm_m93j06_linearSolution c 0 = 1 := by
  simp [apm_m93j06_linearSolution]

lemma apm_m93j06_linearSolution_hasDerivAt {c : ℝ → ℝ} (hc : Continuous c)
    (t : ℝ) :
    HasDerivAt (apm_m93j06_linearSolution c)
      (apm_m93j06_linearSolution c t * c t) t := by
  have hi : HasDerivAt (fun u ↦ ∫ s in (0 : ℝ)..u, c s) (c t) t :=
    intervalIntegral.integral_hasDerivAt_right
      (hc.intervalIntegrable 0 t)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  simpa [apm_m93j06_linearSolution] using hi.exp

/-- A scalar linear ODE with continuous coefficient and initial value one has
the exponential-integral solution. -/
lemma apm_m93j06_linear_ode_eq_exp_integral {c q : ℝ → ℝ}
    (hc : Continuous c) (hq0 : q 0 = 1)
    (hq : ∀ t, HasDerivAt q (q t * c t) t) (t : ℝ) :
    q t = apm_m93j06_linearSolution c t := by
  let z := apm_m93j06_linearSolution c
  let r : ℝ → ℝ := fun s ↦ q s / z s
  have hz : ∀ s, HasDerivAt z (z s * c s) s := by
    intro s
    exact apm_m93j06_linearSolution_hasDerivAt hc s
  have hz_ne : ∀ s, z s ≠ 0 := by
    intro s
    exact Real.exp_ne_zero _
  have hr : ∀ s, HasDerivAt r 0 s := by
    intro s
    have hd := (hq s).div (hz s) (hz_ne s)
    convert hd using 1
    dsimp [r]
    field_simp
    ring
  have hrdiff : Differentiable ℝ r := fun s ↦ (hr s).differentiableAt
  have hrderiv : ∀ s, deriv r s = 0 := fun s ↦ (hr s).deriv
  have hconst := is_const_of_deriv_eq_zero hrdiff hrderiv t 0
  have hr0 : r 0 = 1 := by
    simp [r, z, hq0, apm_m93j06_linearSolution_zero]
  have hrt : r t = 1 := hconst.trans hr0
  dsimp [r] at hrt
  exact (div_eq_one_iff_eq (hz_ne t)).mp hrt

/-- Average of the state derivative along the segment from `a` to `b`. -/
noncomputable def apm_m93j06_averagePartialY
    (f : ℝ → ℝ → ℝ) (t a b : ℝ) : ℝ :=
  ∫ u in Set.Icc (0 : ℝ) 1,
    apm_m93j06_partialY f t (a + u * (b - a))

/-- The averaged state derivative is jointly continuous in time and both
segment endpoints. -/
lemma apm_m93j06_continuous_averagePartialY {f : ℝ → ℝ → ℝ}
    (hf : ContDiff ℝ 1 (Function.uncurry f)) :
    Continuous (fun p : (ℝ × ℝ × ℝ) ↦
      apm_m93j06_averagePartialY f p.1 p.2.1 p.2.2) := by
  apply continuous_parametric_integral_of_continuous
    (s := Set.Icc (0 : ℝ) 1) ?_ isCompact_Icc
  change Continuous (fun q : ((ℝ × ℝ × ℝ) × ℝ) ↦
    apm_m93j06_partialY f q.1.1
      (q.1.2.1 + q.2 * (q.1.2.2 - q.1.2.1)))
  have hm : Continuous (fun q : ((ℝ × ℝ × ℝ) × ℝ) ↦
      (q.1.1, q.1.2.1 + q.2 * (q.1.2.2 - q.1.2.1))) := by
    fun_prop
  simpa [Function.uncurry] using (apm_m93j06_continuous_partialY hf).comp hm

/-- Fundamental-theorem identity for the averaged derivative. -/
lemma apm_m93j06_averagePartialY_mul_sub {f : ℝ → ℝ → ℝ}
    (hf : ContDiff ℝ 1 (Function.uncurry f)) (t a b : ℝ) :
    apm_m93j06_averagePartialY f t a b * (b - a) = f t b - f t a := by
  let path : ℝ → ℝ := fun u ↦ a + u * (b - a)
  have hpath : ∀ u, HasDerivAt path (b - a) u := by
    intro u
    convert (hasDerivAt_const u a).add
      ((hasDerivAt_id u).mul_const (b - a)) using 1
    ring
  have hderiv : ∀ u, HasDerivAt (fun v ↦ f t (path v))
      (apm_m93j06_partialY f t (path u) * (b - a)) u := by
    intro u
    exact (apm_m93j06_hasDerivAt_slice hf t (path u)).comp u (hpath u)
  have hint : IntervalIntegrable
      (fun u ↦ apm_m93j06_partialY f t (path u) * (b - a))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    have hcpath : Continuous (fun u ↦ (t, path u)) := by
      dsimp [path]
      fun_prop
    exact ((apm_m93j06_continuous_partialY hf).comp hcpath).mul continuous_const
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun u _ ↦ hderiv u) hint
  rw [intervalIntegral.integral_mul_const] at hFTC
  simpa [apm_m93j06_averagePartialY, path, intervalIntegral.integral_of_le,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc] using hFTC

@[simp] lemma apm_m93j06_averagePartialY_same (f : ℝ → ℝ → ℝ) (t a : ℝ) :
    apm_m93j06_averagePartialY f t a a = apm_m93j06_partialY f t a := by
  simp [apm_m93j06_averagePartialY]

/-- Along two flow trajectories, the averaged coefficient is continuous in
time. -/
lemma apm_m93j06_continuous_flow_averagePartialY
    {f φ : ℝ → ℝ → ℝ} (hf : ContDiff ℝ 1 (Function.uncurry f))
    (hφ : apm_m93j06_IsFlow f φ) (a b : ℝ) :
    Continuous (fun t ↦ apm_m93j06_averagePartialY f t (φ t a) (φ t b)) := by
  have hm : Continuous (fun t ↦ (t, φ t a, φ t b)) :=
    continuous_id.prodMk
    ((continuous_iff_continuousAt.mpr
      (fun t ↦ (apm_m93j06_flow_hasDerivAt hφ a t).continuousAt)).prodMk
    (continuous_iff_continuousAt.mpr
      (fun t ↦ (apm_m93j06_flow_hasDerivAt hφ b t).continuousAt)))
  simpa only [Function.comp_apply] using
    (apm_m93j06_continuous_averagePartialY hf).comp hm

/-- Exact averaged-coefficient ODE for a flow difference. -/
lemma apm_m93j06_flow_difference_average_hasDerivAt
    {f φ : ℝ → ℝ → ℝ} (hf : ContDiff ℝ 1 (Function.uncurry f))
    (hφ : apm_m93j06_IsFlow f φ) (a b t : ℝ) :
    HasDerivAt (fun s ↦ φ s b - φ s a)
      ((φ t b - φ t a) *
        apm_m93j06_averagePartialY f t (φ t a) (φ t b)) t := by
  have hd := (apm_m93j06_flow_hasDerivAt hφ b t).sub
    (apm_m93j06_flow_hasDerivAt hφ a t)
  convert hd using 1
  simpa [mul_comm] using
    (apm_m93j06_averagePartialY_mul_sub hf t (φ t a) (φ t b))

/-- Every nontrivial flow secant has the exponential-integral formula with
the jointly continuous averaged state derivative as coefficient. -/
lemma apm_m93j06_flow_secant_eq_exp_integral
    {f φ : ℝ → ℝ → ℝ} (hf : ContDiff ℝ 1 (Function.uncurry f))
    (hφ : apm_m93j06_IsFlow f φ) {a b : ℝ} (hab : b ≠ a) (t : ℝ) :
    (φ t b - φ t a) / (b - a) =
      apm_m93j06_linearSolution
        (fun s ↦ apm_m93j06_averagePartialY f s (φ s a) (φ s b)) t := by
  let q : ℝ → ℝ := fun s ↦ (φ s b - φ s a) / (b - a)
  let c : ℝ → ℝ := fun s ↦
    apm_m93j06_averagePartialY f s (φ s a) (φ s b)
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab
  have hq0 : q 0 = 1 := by
    simp [q, apm_m93j06_flow_zero hφ, hba]
  have hq : ∀ s, HasDerivAt q (q s * c s) s := by
    intro s
    have hd := (apm_m93j06_flow_difference_average_hasDerivAt hf hφ a b s).div_const
      (b - a)
    convert hd using 1
    dsimp [q, c]
    field_simp [hba]
  exact apm_m93j06_linear_ode_eq_exp_integral
    (apm_m93j06_continuous_flow_averagePartialY hf hφ a b) hq0 hq t


/-- Integrating a jointly continuous real function over a fixed finite
interval preserves continuity in a real parameter. -/
lemma apm_m93j06_continuous_intervalIntegral_param
    {F : ℝ → ℝ → ℝ} (hF : Continuous (Function.uncurry F)) (a b : ℝ) :
    Continuous (fun x ↦ ∫ s in a..b, F x s) := by
  rcases le_total a b with hab | hba
  · have hset := continuous_parametric_integral_of_continuous
      (μ := MeasureTheory.volume)
      hF isCompact_Icc (s := Set.Icc a b)
    convert hset using 1
    funext x
    rw [intervalIntegral.integral_of_le hab,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  · have hset := continuous_parametric_integral_of_continuous
      (μ := MeasureTheory.volume)
      hF isCompact_Icc (s := Set.Icc b a)
    have hneg : Continuous (fun x ↦ -(∫ s in Set.Icc b a, F x s)) := hset.neg
    convert hneg using 1
    funext x
    rw [intervalIntegral.integral_of_ge hba,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- Under joint continuity of an already supplied global flow, the exact
secant formula gives differentiability in the initial value, with the usual
variational exponential as derivative. -/
lemma apm_m93j06_flow_hasDerivAt_initial_of_continuous
    {f φ : ℝ → ℝ → ℝ} (hf : ContDiff ℝ 1 (Function.uncurry f))
    (hφ : apm_m93j06_IsFlow f φ)
    (hφcont : Continuous (Function.uncurry φ)) (t a : ℝ) :
    HasDerivAt (φ t)
      (apm_m93j06_linearSolution
        (fun s ↦ apm_m93j06_partialY f s (φ s a)) t) a := by
  let G : ℝ → ℝ := fun b ↦ apm_m93j06_linearSolution
    (fun s ↦ apm_m93j06_averagePartialY f s (φ s a) (φ s b)) t
  have hcoef : Continuous (Function.uncurry
      (fun b s ↦ apm_m93j06_averagePartialY f s (φ s a) (φ s b))) := by
    have hm : Continuous (fun p : ℝ × ℝ ↦
        (p.2, φ p.2 a, φ p.2 p.1)) := by
      exact continuous_snd.prodMk
        (((continuous_iff_continuousAt.mpr
          (fun s ↦ (apm_m93j06_flow_hasDerivAt hφ a s).continuousAt)).comp
            continuous_snd).prodMk
          (hφcont.comp (continuous_snd.prodMk continuous_fst)))
    simpa [Function.uncurry] using
      (apm_m93j06_continuous_averagePartialY hf).comp hm
  have hG : Continuous G := by
    apply Real.continuous_exp.comp
    exact apm_m93j06_continuous_intervalIntegral_param hcoef 0 t
  rw [hasDerivAt_iff_tendsto_slope]
  have heq : slope (φ t) a =ᶠ[nhdsWithin a {a}ᶜ] G := by
    filter_upwards [self_mem_nhdsWithin] with b hb
    have hba : b ≠ a := hb
    simpa [G, slope, div_eq_inv_mul, mul_comm] using
      apm_m93j06_flow_secant_eq_exp_integral hf hφ hba t
  have hGt := hG.continuousAt.mono_left
    (inf_le_left : nhdsWithin a {a}ᶜ ≤ nhds a)
  have hslope := (Filter.Tendsto.congr' heq.symm) hGt
  simpa [G] using hslope

/-- Joint continuity of the global flow upgrades the exact secant formula to
`C¹` dependence on the initial value at every time. -/
lemma apm_m93j06_flow_contDiff_initial_of_continuous
    {f φ : ℝ → ℝ → ℝ} (hf : ContDiff ℝ 1 (Function.uncurry f))
    (hφ : apm_m93j06_IsFlow f φ)
    (hφcont : Continuous (Function.uncurry φ)) (t : ℝ) :
    ContDiff ℝ 1 (φ t) := by
  let D : ℝ → ℝ := fun a ↦ apm_m93j06_linearSolution
    (fun s ↦ apm_m93j06_partialY f s (φ s a)) t
  have hcoef : Continuous (Function.uncurry
      (fun a s ↦ apm_m93j06_partialY f s (φ s a))) := by
    have hm : Continuous (fun p : ℝ × ℝ ↦ (p.2, φ p.2 p.1)) :=
      continuous_snd.prodMk (hφcont.comp (continuous_snd.prodMk continuous_fst))
    simpa [Function.uncurry] using
      (apm_m93j06_continuous_partialY hf).comp hm
  have hD : Continuous D := by
    apply Real.continuous_exp.comp
    exact apm_m93j06_continuous_intervalIntegral_param hcoef 0 t
  rw [contDiff_one_iff_deriv]
  refine ⟨fun a ↦
    (apm_m93j06_flow_hasDerivAt_initial_of_continuous hf hφ hφcont t a).differentiableAt,
    ?_⟩
  have hderiv : deriv (φ t) = D := by
    funext a
    exact (apm_m93j06_flow_hasDerivAt_initial_of_continuous hf hφ hφcont t a).deriv
  rw [hderiv]
  exact hD

/-- Consequently, a joint continuous-dependence theorem for global flows is
the sole missing input for the second conjunct. -/
lemma apm_m93j06_smooth_dependence_of_continuous_flow
    (hflowcont : ∀ f φ : ℝ → ℝ → ℝ,
      ContDiff ℝ 1 (Function.uncurry f) → apm_m93j06_IsFlow f φ →
      Continuous (Function.uncurry φ)) :
    ∀ f φ, ContDiff ℝ 1 (Function.uncurry f) → apm_m93j06_IsFlow f φ →
      ∃ ε > 0, ∀ t, |t| < ε → ContDiff ℝ 1 (φ t) := by
  intro f φ hf hφ
  refine ⟨1, zero_lt_one, fun t _ ↦ ?_⟩
  exact apm_m93j06_flow_contDiff_initial_of_continuous hf hφ
    (hflowcont f φ hf hφ) t

/-- On every compact time-state rectangle, a `C¹` scalar field has a uniform
Lipschitz constant in its state coordinate. -/
lemma apm_m93j06_exists_compact_state_lipschitz
    {f : ℝ → ℝ → ℝ} (hf : ContDiff ℝ 1 (Function.uncurry f))
    {A B R : ℝ} (hAB : A ≤ B) (hR : 0 ≤ R) :
    ∃ K ≥ 0, ∀ t ∈ Set.Icc A B, ∀ x ∈ Set.Icc (-R) R,
      ∀ y ∈ Set.Icc (-R) R, |f t x - f t y| ≤ K * |x - y| := by
  have hcompact : IsCompact (Set.Icc A B ×ˢ Set.Icc (-R) R) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨K, hKbound⟩ := hcompact.exists_bound_of_continuousOn
    (apm_m93j06_continuous_partialY hf).continuousOn
  have hK : 0 ≤ K := by
    have h := hKbound (A, 0) ⟨⟨le_rfl, hAB⟩, by constructor <;> linarith⟩
    exact (norm_nonneg _).trans h
  refine ⟨K, hK, ?_⟩
  intro t ht
  let Knn : NNReal := ⟨K, hK⟩
  have hlip : LipschitzOnWith Knn (f t) (Set.Icc (-R) R) := by
    apply Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (convex_Icc (-R) R)
    · intro x hx
      exact (apm_m93j06_hasDerivAt_slice hf t x).hasDerivWithinAt
    · intro x hx
      exact_mod_cast (by simpa [Real.norm_eq_abs] using hKbound (t, x) ⟨ht, hx⟩)
  intro x hx y hy
  simpa [Knn, Real.dist_eq] using hlip.dist_le_mul x hx y hy

/-- Interval solutions of a jointly `C¹` scalar field are unique from an
interior meeting point. Unlike the earlier interval lemma, this needs no
global Lipschitz constant. -/
lemma apm_m93j06_interval_solution_unique_of_contDiff
    {f : ℝ → ℝ → ℝ} (hf : ContDiff ℝ 1 (Function.uncurry f))
    {A B τ : ℝ} (hτ : τ ∈ Set.Ioo A B) {y z : ℝ → ℝ}
    (hy : ∀ t ∈ Set.Icc A B,
      HasDerivWithinAt y (f t (y t)) (Set.Icc A B) t)
    (hz : ∀ t ∈ Set.Icc A B,
      HasDerivWithinAt z (f t (z t)) (Set.Icc A B) t)
    (heq : y τ = z τ) : Set.EqOn y z (Set.Icc A B) := by
  have hAB : A ≤ B := le_trans (le_of_lt hτ.1) (le_of_lt hτ.2)
  have hycont : ContinuousOn y (Set.Icc A B) :=
    HasDerivWithinAt.continuousOn hy
  have hzcont : ContinuousOn z (Set.Icc A B) :=
    HasDerivWithinAt.continuousOn hz
  obtain ⟨Ry, hRy⟩ := isCompact_Icc.exists_bound_of_continuousOn hycont.norm
  obtain ⟨Rz, hRz⟩ := isCompact_Icc.exists_bound_of_continuousOn hzcont.norm
  let R := max Ry Rz
  have hR : 0 ≤ R := by
    have h := hRy τ ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩
    exact (norm_nonneg _).trans (h.trans (le_max_left _ _))
  obtain ⟨K, hK, hLip⟩ :=
    apm_m93j06_exists_compact_state_lipschitz hf hAB hR
  have hyRange : ∀ s ∈ Set.Icc A B, y s ∈ Set.Icc (-R) R := by
    intro s hs
    apply abs_le.mp
    simpa only [Real.norm_eq_abs, abs_abs, R] using
      (hRy s hs).trans (le_max_left Ry Rz)
  have hzRange : ∀ s ∈ Set.Icc A B, z s ∈ Set.Icc (-R) R := by
    intro s hs
    apply abs_le.mp
    simpa only [Real.norm_eq_abs, abs_abs, R] using
      (hRz s hs).trans (le_max_right Ry Rz)
  let Knn : NNReal := ⟨K, hK⟩
  have hv : ∀ s ∈ Set.Icc A B,
      LipschitzOnWith Knn (f s) (Set.Icc (-R) R) := by
    intro s hs
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro a ha b hb
    simpa [Knn, Real.dist_eq] using hLip s hs a ha b hb
  apply ODE_solution_unique_of_mem_Icc
    (s := fun _ ↦ Set.Icc (-R) R) (K := Knn)
    (fun s hs ↦ hv s (Set.Ioo_subset_Icc_self hs)) hτ
    hycont
    (fun s hs ↦ (hy s (Set.Ioo_subset_Icc_self hs)).hasDerivAt
      (Icc_mem_nhds hs.1 hs.2))
    (fun s hs ↦ hyRange s (Set.Ioo_subset_Icc_self hs))
    hzcont
    (fun s hs ↦ (hz s (Set.Ioo_subset_Icc_self hs)).hasDerivAt
      (Icc_mem_nhds hs.1 hs.2))
    (fun s hs ↦ hzRange s (Set.Ioo_subset_Icc_self hs)) heq

/-- Two global trajectories of a jointly `C¹` scalar field which meet at any
time agree everywhere. -/
lemma apm_m93j06_trajectories_eq_of_contDiff_eq_at
    {f : ℝ → ℝ → ℝ} (hf : ContDiff ℝ 1 (Function.uncurry f))
    {y z : ℝ → ℝ} (hy : ∀ t, HasDerivAt y (f t (y t)) t)
    (hz : ∀ t, HasDerivAt z (f t (z t)) t) {τ : ℝ} (hτ : y τ = z τ) : y = z := by
  funext t
  let A := min τ t - 1
  let B := max τ t + 1
  have hAB : A ≤ B := by
    dsimp [A, B]
    linarith [min_le_left τ t, le_max_left τ t]
  have hAτ : A < τ := by dsimp [A]; linarith [min_le_left τ t]
  have hτB : τ < B := by dsimp [B]; linarith [le_max_left τ t]
  have htIcc : t ∈ Set.Icc A B := by
    dsimp [A, B]
    exact ⟨by linarith [min_le_right τ t], by linarith [le_max_right τ t]⟩
  have hycont : Continuous y := continuous_iff_continuousAt.mpr
    (fun s ↦ (hy s).continuousAt)
  have hzcont : Continuous z := continuous_iff_continuousAt.mpr
    (fun s ↦ (hz s).continuousAt)
  obtain ⟨Ry, hRy⟩ := isCompact_Icc.exists_bound_of_continuousOn hycont.norm.continuousOn
  obtain ⟨Rz, hRz⟩ := isCompact_Icc.exists_bound_of_continuousOn hzcont.norm.continuousOn
  let R := max Ry Rz
  have hR : 0 ≤ R := by
    have h := hRy τ ⟨le_of_lt hAτ, le_of_lt hτB⟩
    exact (norm_nonneg _).trans (h.trans (le_max_left _ _))
  obtain ⟨K, hK, hLip⟩ :=
    apm_m93j06_exists_compact_state_lipschitz hf hAB hR
  have hyRange : ∀ s ∈ Set.Icc A B, y s ∈ Set.Icc (-R) R := by
    intro s hs
    have hnorm : |y s| ≤ R := by
      simpa only [Real.norm_eq_abs, abs_abs, R] using
        (hRy s hs).trans (le_max_left Ry Rz)
    exact (abs_le.mp hnorm)
  have hzRange : ∀ s ∈ Set.Icc A B, z s ∈ Set.Icc (-R) R := by
    intro s hs
    have hnorm : |z s| ≤ R := by
      simpa only [Real.norm_eq_abs, abs_abs, R] using
        (hRz s hs).trans (le_max_right Ry Rz)
    exact (abs_le.mp hnorm)
  let Knn : NNReal := ⟨K, hK⟩
  have hv : ∀ s ∈ Set.Icc A B,
      LipschitzOnWith Knn (f s) (Set.Icc (-R) R) := by
    intro s hs
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro a ha b hb
    simpa [Knn, Real.dist_eq] using hLip s hs a ha b hb
  have heq : Set.EqOn y z (Set.Icc A B) := by
    apply ODE_solution_unique_of_mem_Icc
      (s := fun _ ↦ Set.Icc (-R) R) (K := Knn)
      (fun s hs ↦ hv s (Set.Ioo_subset_Icc_self hs)) ⟨hAτ, hτB⟩
      hycont.continuousOn (fun s _ ↦ hy s)
      (fun s hs ↦ hyRange s (Set.Ioo_subset_Icc_self hs))
      hzcont.continuousOn (fun s _ ↦ hz s)
      (fun s hs ↦ hzRange s (Set.Ioo_subset_Icc_self hs))
      hτ
  exact heq htIcc

/-- Joint `C¹` regularity therefore implies uniqueness for the global initial
value problem without a global Lipschitz constant. -/
lemma apm_m93j06_solution_unique_of_contDiff
    {f : ℝ → ℝ → ℝ} (hf : ContDiff ℝ 1 (Function.uncurry f))
    {y₀ : ℝ} {y z : ℝ → ℝ}
    (hy : apm_m93j06_Solves f y₀ y) (hz : apm_m93j06_Solves f y₀ z) : y = z := by
  exact apm_m93j06_trajectories_eq_of_contDiff_eq_at hf hy.2 hz.2
    (hy.1.trans hz.1.symm)

/-- Around every time-state point, a jointly `C¹` scalar field admits a
positive-radius Picard family which is jointly continuous in the initial
state and time. -/
lemma apm_m93j06_exists_continuous_local_flow
    {f : ℝ → ℝ → ℝ} (hf : ContDiff ℝ 1 (Function.uncurry f)) (t₀ x₀ : ℝ) :
    ∃ δ > 0, ∃ r > 0, ∃ α : ℝ × ℝ → ℝ,
      (∀ x ∈ Metric.closedBall x₀ r, α (x, t₀) = x ∧
        ∀ t ∈ Set.Icc (t₀ - δ) (t₀ + δ),
          HasDerivWithinAt (fun s ↦ α (x, s)) (f t (α (x, t)))
            (Set.Icc (t₀ - δ) (t₀ + δ)) t) ∧
      ContinuousOn α
        (Metric.closedBall x₀ r ×ˢ Set.Icc (t₀ - δ) (t₀ + δ)) := by
  have hcompact : IsCompact
      (Set.Icc (t₀ - 1) (t₀ + 1) ×ˢ Metric.closedBall x₀ 1) :=
    isCompact_Icc.prod (isCompact_closedBall x₀ 1)
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hf.continuous.continuousOn
  let Q := max C 1
  have hQone : 1 ≤ Q := le_max_right _ _
  have hQ : 0 < Q := zero_lt_one.trans_le hQone
  let δ := (2 * Q)⁻¹
  have hδ : 0 < δ := inv_pos.mpr (mul_pos (by norm_num) hQ)
  have hδone : δ ≤ 1 := by
    apply (inv_le_one₀ (mul_pos (by norm_num) hQ)).mpr
    linarith
  have hbound : ∀ t ∈ Set.Icc (t₀ - δ) (t₀ + δ),
      ∀ x ∈ Metric.closedBall x₀ (1 : ℝ), |f t x| ≤ Q := by
    intro t ht x hx
    have ht' : t ∈ Set.Icc (t₀ - 1) (t₀ + 1) :=
      ⟨by linarith [ht.1, hδone], by linarith [ht.2, hδone]⟩
    have hb := hC (t, x) ⟨ht', hx⟩
    have hb' : |f t x| ≤ C := by
      simpa [Function.uncurry, Real.norm_eq_abs] using hb
    exact hb'.trans (le_max_left C 1)
  let R := |x₀| + 1
  have hR : 0 ≤ R := by positivity
  obtain ⟨L, hL, hLip⟩ :=
    apm_m93j06_exists_compact_state_lipschitz hf
      (A := t₀ - 1) (B := t₀ + 1) (R := R) (by linarith) hR
  have hLipBall : ∀ t ∈ Set.Icc (t₀ - δ) (t₀ + δ),
      ∀ x ∈ Metric.closedBall x₀ (1 : ℝ),
      ∀ y ∈ Metric.closedBall x₀ (1 : ℝ),
        |f t x - f t y| ≤ L * |x - y| := by
    intro t ht x hx y hy
    have ht' : t ∈ Set.Icc (t₀ - 1) (t₀ + 1) :=
      ⟨by linarith [ht.1, hδone], by linarith [ht.2, hδone]⟩
    have memIcc : ∀ z ∈ Metric.closedBall x₀ (1 : ℝ), z ∈ Set.Icc (-R) R := by
      intro z hz
      rw [Metric.mem_closedBall, Real.dist_eq] at hz
      have habs : |z| ≤ R := by
        calc
          |z| = |(z - x₀) + x₀| := by ring_nf
          _ ≤ |z - x₀| + |x₀| := abs_add_le _ _
          _ ≤ 1 + |x₀| := by gcongr
          _ = R := by simp [R, add_comm]
      exact abs_le.mp habs
    exact hLip t ht' x (memIcc x hx) y (memIcc y hy)
  refine ⟨δ, hδ, (1 / 2 : ℝ), by norm_num, ?_⟩
  apply apm_m93j06_exists_continuous_local_flow_of_box_radius hδ
    (by norm_num) (by norm_num) (le_of_lt hQ) hL hLipBall hf.continuous hbound
  dsimp [δ]
  have hQne : Q ≠ 0 := hQ.ne'
  field_simp
  norm_num

/-- Along one compact piece of a supplied trajectory, the positive-radius
continuous Picard charts can be chosen with one common lifespan and radius. -/
lemma apm_m93j06_exists_uniform_continuous_local_flow_along
    {f φ : ℝ → ℝ → ℝ} (hf : ContDiff ℝ 1 (Function.uncurry f))
    (hφ : apm_m93j06_IsFlow f φ) {A B : ℝ} (hAB : A ≤ B) (a : ℝ) :
    ∃ δ > 0, ∃ r > 0, ∀ t₀ ∈ Set.Icc A B,
      ∃ α : ℝ × ℝ → ℝ,
        (∀ x ∈ Metric.closedBall (φ t₀ a) r, α (x, t₀) = x ∧
          ∀ t ∈ Set.Icc (t₀ - δ) (t₀ + δ),
            HasDerivWithinAt (fun s ↦ α (x, s)) (f t (α (x, t)))
              (Set.Icc (t₀ - δ) (t₀ + δ)) t) ∧
        ContinuousOn α
          (Metric.closedBall (φ t₀ a) r ×ˢ Set.Icc (t₀ - δ) (t₀ + δ)) := by
  have htraj : Continuous (fun t ↦ φ t a) :=
    continuous_iff_continuousAt.mpr
      (fun t ↦ (apm_m93j06_flow_hasDerivAt hφ a t).continuousAt)
  obtain ⟨R₀, hR₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    htraj.norm.continuousOn
  let R := max R₀ 0 + 1
  have hR : 0 ≤ R := by positivity
  have hcompact : IsCompact
      (Set.Icc (A - 1) (B + 1) ×ˢ Set.Icc (-R) R) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn
    hf.continuous.norm.continuousOn
  let Q := max C 1
  have hQone : 1 ≤ Q := le_max_right _ _
  have hQ : 0 < Q := zero_lt_one.trans_le hQone
  let δ := (2 * Q)⁻¹
  have hδ : 0 < δ := inv_pos.mpr (mul_pos (by norm_num) hQ)
  have hδone : δ ≤ 1 := by
    apply (inv_le_one₀ (mul_pos (by norm_num) hQ)).mpr
    linarith
  obtain ⟨L, hL, hLip⟩ :=
    apm_m93j06_exists_compact_state_lipschitz hf
      (A := A - 1) (B := B + 1) (R := R) (by linarith) hR
  refine ⟨δ, hδ, (1 / 2 : ℝ), by norm_num, ?_⟩
  intro t₀ ht₀
  have hcenter : |φ t₀ a| ≤ max R₀ 0 := by
    exact (by simpa only [Real.norm_eq_abs, abs_abs] using
      (hR₀ t₀ ht₀).trans (le_max_left R₀ 0))
  have memIcc : ∀ x ∈ Metric.closedBall (φ t₀ a) (1 : ℝ),
      x ∈ Set.Icc (-R) R := by
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq] at hx
    apply abs_le.mp
    calc
      |x| = |(x - φ t₀ a) + φ t₀ a| := by ring_nf
      _ ≤ |x - φ t₀ a| + |φ t₀ a| := abs_add_le _ _
      _ ≤ 1 + max R₀ 0 := add_le_add hx hcenter
      _ = R := by simp [R, add_comm]
  have htime : ∀ t ∈ Set.Icc (t₀ - δ) (t₀ + δ),
      t ∈ Set.Icc (A - 1) (B + 1) := by
    intro t ht
    exact ⟨by linarith [ht.1, ht₀.1, hδone],
      by linarith [ht.2, ht₀.2, hδone]⟩
  have hbound : ∀ t ∈ Set.Icc (t₀ - δ) (t₀ + δ),
      ∀ x ∈ Metric.closedBall (φ t₀ a) (1 : ℝ), |f t x| ≤ Q := by
    intro t ht x hx
    have hb := hC (t, x) ⟨htime t ht, memIcc x hx⟩
    have hb' : |f t x| ≤ C := by
      simpa [Function.uncurry, Real.norm_eq_abs] using hb
    exact hb'.trans (le_max_left C 1)
  have hLipBall : ∀ t ∈ Set.Icc (t₀ - δ) (t₀ + δ),
      ∀ x ∈ Metric.closedBall (φ t₀ a) (1 : ℝ),
      ∀ y ∈ Metric.closedBall (φ t₀ a) (1 : ℝ),
        |f t x - f t y| ≤ L * |x - y| := by
    intro t ht x hx y hy
    exact hLip t (htime t ht) x (memIcc x hx) y (memIcc y hy)
  apply apm_m93j06_exists_continuous_local_flow_of_box_radius hδ
    (by norm_num) (by norm_num) (le_of_lt hQ) hL hLipBall hf.continuous hbound
  dsimp [δ]
  have hQne : Q ≠ 0 := hQ.ne'
  field_simp
  norm_num

/-- One continuous Picard chart propagates continuity of a supplied flow's
time slice from the chart's anchor to every interior time in the chart. -/
lemma apm_m93j06_flow_timeSlice_continuousAt_of_local_flow
    {f φ : ℝ → ℝ → ℝ} (hf : ContDiff ℝ 1 (Function.uncurry f))
    (hφ : apm_m93j06_IsFlow f φ) {t₀ a δ r : ℝ}
    (hδ : 0 < δ) (hr : 0 < r) {α : ℝ × ℝ → ℝ}
    (hα : ∀ x ∈ Metric.closedBall (φ t₀ a) r, α (x, t₀) = x ∧
      ∀ t ∈ Set.Icc (t₀ - δ) (t₀ + δ),
        HasDerivWithinAt (fun u ↦ α (x, u)) (f t (α (x, t)))
          (Set.Icc (t₀ - δ) (t₀ + δ)) t)
    (hαcont : ContinuousOn α
      (Metric.closedBall (φ t₀ a) r ×ˢ Set.Icc (t₀ - δ) (t₀ + δ)))
    (hcont : ContinuousAt (φ t₀) a) {s : ℝ}
    (hs : s ∈ Set.Ioo (t₀ - δ) (t₀ + δ)) : ContinuousAt (φ s) a := by
  let g : ℝ → ℝ × ℝ := fun b ↦ (φ t₀ b, s)
  have hg : ContinuousAt g a :=
    hcont.prodMk continuousAt_const
  have hbox : Metric.closedBall (φ t₀ a) r ×ˢ
      Set.Icc (t₀ - δ) (t₀ + δ) ∈ nhds (φ t₀ a, s) := by
    exact prod_mem_nhds (Metric.closedBall_mem_nhds _ hr)
      (Icc_mem_nhds hs.1 hs.2)
  have hαat : ContinuousAt α (g a) := by
    simpa [g] using hαcont.continuousAt hbox
  have hcomp : ContinuousAt (fun b ↦ α (g b)) a := hαat.comp hg
  have heq : φ s =ᶠ[nhds a] fun b ↦ α (g b) := by
    have hstate : ∀ᶠ b in nhds a,
        φ t₀ b ∈ Metric.closedBall (φ t₀ a) r :=
      hcont (Metric.closedBall_mem_nhds _ hr)
    filter_upwards [hstate] with b hb
    have huniq : Set.EqOn (fun u ↦ α (φ t₀ b, u)) (fun u ↦ φ u b)
        (Set.Icc (t₀ - δ) (t₀ + δ)) := by
      apply apm_m93j06_interval_solution_unique_of_contDiff hf
        (τ := t₀) (by constructor <;> linarith)
      · exact (hα (φ t₀ b) hb).2
      · intro u hu
        exact (apm_m93j06_flow_hasDerivAt hφ b u).hasDerivWithinAt
      · exact (hα (φ t₀ b) hb).1
    exact (huniq (Set.Ioo_subset_Icc_self hs)).symm
  exact hcomp.congr_of_eventuallyEq heq

/-- Continuity of one time slice persists for the same initial value on a
nontrivial open time interval. -/
lemma apm_m93j06_flow_timeSlice_continuousAt_near
    {f φ : ℝ → ℝ → ℝ} (hf : ContDiff ℝ 1 (Function.uncurry f))
    (hφ : apm_m93j06_IsFlow f φ) {t₀ a : ℝ}
    (hcont : ContinuousAt (φ t₀) a) :
    ∃ δ > 0, ∀ s ∈ Set.Ioo (t₀ - δ) (t₀ + δ),
      ContinuousAt (φ s) a := by
  obtain ⟨δ, hδ, r, hr, α, hα, hαcont⟩ :=
    apm_m93j06_exists_continuous_local_flow hf t₀ (φ t₀ a)
  exact ⟨δ, hδ, fun s hs ↦
    apm_m93j06_flow_timeSlice_continuousAt_of_local_flow
      hf hφ hδ hr hα hαcont hcont hs⟩

/-- Every time slice of a supplied global flow of a jointly `C¹` scalar field
is continuous at every initial value. -/
lemma apm_m93j06_flow_timeSlice_continuousAt
    {f φ : ℝ → ℝ → ℝ} (hf : ContDiff ℝ 1 (Function.uncurry f))
    (hφ : apm_m93j06_IsFlow f φ) (t a : ℝ) : ContinuousAt (φ t) a := by
  let A := min 0 t
  let B := max 0 t
  have hAB : A ≤ B := min_le_max
  obtain ⟨δ, hδ, r, hr, hlocal⟩ :=
    apm_m93j06_exists_uniform_continuous_local_flow_along hf hφ hAB a
  obtain ⟨n, hn⟩ := exists_nat_gt (|t| / δ)
  have hnpos : 0 < n := by
    have hnonneg : 0 ≤ |t| / δ := div_nonneg (abs_nonneg _) (le_of_lt hδ)
    have hnR' : (0 : ℝ) < n := lt_of_le_of_lt hnonneg hn
    exact_mod_cast hnR'
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  let d := t / (n : ℝ)
  have hd : |d| < δ := by
    rw [abs_div, abs_of_pos hnR]
    rw [div_lt_iff₀ hnR]
    rw [div_lt_iff₀ hδ] at hn
    simpa [mul_comm] using hn
  have hnd : (n : ℝ) * d = t := by
    dsimp [d]
    field_simp
  have hgrid : ∀ k : ℕ, k ≤ n → (k : ℝ) * d ∈ Set.Icc A B := by
    intro k hk
    have hk0 : (0 : ℝ) ≤ k := by positivity
    have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk
    by_cases hdt : 0 ≤ d
    · have h0 : 0 ≤ (k : ℝ) * d := mul_nonneg hk0 hdt
      have htop : (k : ℝ) * d ≤ t := by
        rw [← hnd]
        exact mul_le_mul_of_nonneg_right hkn hdt
      exact ⟨by simp [A]; exact Or.inl h0,
        by simp [B]; exact Or.inr htop⟩
    · have hdt' : d < 0 := lt_of_not_ge hdt
      have hbot : t ≤ (k : ℝ) * d := by
        rw [← hnd]
        exact mul_le_mul_of_nonpos_right hkn (le_of_lt hdt')
      have hzero : (k : ℝ) * d ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk0 (le_of_lt hdt')
      exact ⟨by simp [A]; exact Or.inr hbot,
        by simp [B]; exact Or.inl hzero⟩
  have hind : ∀ k : ℕ, k ≤ n → ContinuousAt (φ ((k : ℝ) * d)) a := by
    intro k
    induction k with
    | zero =>
        intro _
        convert (continuousAt_id : ContinuousAt (fun x : ℝ ↦ x) a) using 1
        funext x
        simpa using apm_m93j06_flow_zero hφ x
    | succ k ih =>
        intro hsucc
        have hk : k ≤ n := Nat.le_trans (Nat.le_succ k) hsucc
        obtain ⟨α, hα, hαcont⟩ := hlocal ((k : ℝ) * d) (hgrid k hk)
        apply apm_m93j06_flow_timeSlice_continuousAt_of_local_flow
          hf hφ hδ hr hα hαcont (ih hk)
        constructor <;> dsimp only
        · have := neg_lt_of_abs_lt hd
          push_cast
          linarith
        · have := lt_of_abs_lt hd
          push_cast
          linarith
  have hfinal := hind n le_rfl
  rw [hnd] at hfinal
  exact hfinal

/-- Continuity of the time-`t₀` flow map at one initial value propagates to
joint continuity of the flow at the corresponding time-state pair. -/
lemma apm_m93j06_flow_continuousAt_of_timeSlice
    {f φ : ℝ → ℝ → ℝ} (hf : ContDiff ℝ 1 (Function.uncurry f))
    (hφ : apm_m93j06_IsFlow f φ) {t₀ a : ℝ}
    (hcont : ContinuousAt (φ t₀) a) :
    ContinuousAt (Function.uncurry φ) (t₀, a) := by
  obtain ⟨δ, hδ, r, hr, α, hα, hαcont⟩ :=
    apm_m93j06_exists_continuous_local_flow hf t₀ (φ t₀ a)
  let g : ℝ × ℝ → ℝ × ℝ := fun p ↦ (φ t₀ p.2, p.1)
  have hg : ContinuousAt g (t₀, a) := by
    exact (hcont.comp continuousAt_snd).prodMk continuousAt_fst
  have hbox : Metric.closedBall (φ t₀ a) r ×ˢ
      Set.Icc (t₀ - δ) (t₀ + δ) ∈ nhds (φ t₀ a, t₀) := by
    exact prod_mem_nhds (Metric.closedBall_mem_nhds _ hr)
      (Icc_mem_nhds (by linarith) (by linarith))
  have hαat : ContinuousAt α (g (t₀, a)) := by
    simpa [g] using hαcont.continuousAt hbox
  have hcomp : ContinuousAt (fun p ↦ α (g p)) (t₀, a) :=
    hαat.comp hg
  have heq : Function.uncurry φ =ᶠ[nhds (t₀, a)] fun p ↦ α (g p) := by
    have hstate : ∀ᶠ p : ℝ × ℝ in nhds (t₀, a),
        φ t₀ p.2 ∈ Metric.closedBall (φ t₀ a) r :=
      (hcont.comp continuousAt_snd) (Metric.closedBall_mem_nhds _ hr)
    have htime : ∀ᶠ p : ℝ × ℝ in nhds (t₀, a),
        p.1 ∈ Set.Ioo (t₀ - δ) (t₀ + δ) :=
      continuousAt_fst (Ioo_mem_nhds (by linarith) (by linarith))
    filter_upwards [hstate, htime] with p hpstate hptime
    have huniq : Set.EqOn (fun s ↦ α (φ t₀ p.2, s)) (fun s ↦ φ s p.2)
        (Set.Icc (t₀ - δ) (t₀ + δ)) := by
      apply apm_m93j06_interval_solution_unique_of_contDiff hf
        (τ := t₀) (by constructor <;> linarith)
      · exact (hα (φ t₀ p.2) hpstate).2
      · intro s hs
        exact (apm_m93j06_flow_hasDerivAt hφ p.2 s).hasDerivWithinAt
      · exact (hα (φ t₀ p.2) hpstate).1
    exact (huniq (Set.Ioo_subset_Icc_self hptime)).symm
  exact hcomp.congr_of_eventuallyEq heq

/-- A supplied global flow of a jointly `C¹` scalar field is jointly
continuous in time and initial value. -/
lemma apm_m93j06_flow_continuous
    {f φ : ℝ → ℝ → ℝ} (hf : ContDiff ℝ 1 (Function.uncurry f))
    (hφ : apm_m93j06_IsFlow f φ) : Continuous (Function.uncurry φ) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t, a⟩
  exact apm_m93j06_flow_continuousAt_of_timeSlice hf hφ
    (apm_m93j06_flow_timeSlice_continuousAt hf hφ t a)

/-- Joint continuity supplied by Picard propagation discharges the final
hypothesis of the compiled variational-equation argument. -/
lemma apm_m93j06_smooth_dependence :
    ∀ f φ, ContDiff ℝ 1 (Function.uncurry f) → apm_m93j06_IsFlow f φ →
      ∃ ε > 0, ∀ t, |t| < ε → ContDiff ℝ 1 (φ t) := by
  apply apm_m93j06_smooth_dependence_of_continuous_flow
  intro f φ hf hφ
  exact apm_m93j06_flow_continuous hf hφ

/-- End-to-end assembly of the frozen result from its two remaining analytic
producers: global existence/uniqueness and differentiable dependence. -/
lemma apm_m93j06_of_global_and_contDiff
    (hglobal : ∀ f : ℝ → ℝ → ℝ, Continuous (Function.uncurry f) →
      (∃ L > 0, ∀ t a b, |f t a - f t b| ≤ L * |a - b|) →
      ∀ y₀, ∃! y : ℝ → ℝ, apm_m93j06_Solves f y₀ y)
    (hsmooth : ∀ f φ, ContDiff ℝ 1 (Function.uncurry f) → apm_m93j06_IsFlow f φ →
      ∃ ε > 0, ∀ t, |t| < ε → ContDiff ℝ 1 (φ t)) :
    (∀ f : ℝ → ℝ → ℝ, Continuous (Function.uncurry f) →
      (∃ L > 0, ∀ t a b, |f t a - f t b| ≤ L * |a - b|) →
      ∀ y₀, ∃! y : ℝ → ℝ, apm_m93j06_Solves f y₀ y) ∧
    (∀ f φ, ContDiff ℝ 1 (Function.uncurry f) → apm_m93j06_IsFlow f φ →
      ∃ ε > 0, ∀ t, |t| < ε → ContDiff ℝ 1 (φ t)) ∧
    (∀ f C, 0 ≤ C → Continuous (Function.uncurry f) →
      (∀ t y, |f t y| ≤ C * |y|) →
      (∃ L > 0, ∀ t a b, |f t a - f t b| ≤ L * |a - b|) →
      ∃ φ, apm_m93j06_IsFlow f φ) ∧
    (¬ ∀ α : ℝ, 0 < α → α < 1 → ∀ f : ℝ → ℝ → ℝ,
      (∃ K > 0, ∀ t a b,
        |f t a - f t b| ≤ K * Real.rpow |a - b| α) →
      ∀ y₀, ∃! y : ℝ → ℝ, apm_m93j06_Solves f y₀ y) ∧
    (∀ f φ C L, 0 ≤ C → 0 ≤ L → apm_m93j06_IsFlow f φ →
      (∀ t y, |f t y| ≤ C * |y|) →
      (∀ t a b, |f t a - f t b| ≤ L * |a - b|) →
      ∀ t a b, |φ t a - φ t b| ≤ Real.exp (L * |t|) * |a - b|) := by
  refine ⟨hglobal, hsmooth, apm_m93j06_growth_flow_of_global_existence hglobal,
    apm_m93j06_not_holder_unique, ?_⟩
  intro f φ C L _ hL hφ _ hLip
  exact apm_m93j06_flow_lipschitz hL hφ hLip

theorem apm_m93j06 :
    (∀ f : ℝ → ℝ → ℝ, Continuous (Function.uncurry f) →
      (∃ L > 0, ∀ t a b, |f t a - f t b| ≤ L * |a - b|) →
      ∀ y₀, ∃! y : ℝ → ℝ, apm_m93j06_Solves f y₀ y) ∧
    (∀ f φ, ContDiff ℝ 1 (Function.uncurry f) → apm_m93j06_IsFlow f φ →
      ∃ ε > 0, ∀ t, |t| < ε → ContDiff ℝ 1 (φ t)) ∧
    (∀ f C, 0 ≤ C → Continuous (Function.uncurry f) →
      (∀ t y, |f t y| ≤ C * |y|) →
      (∃ L > 0, ∀ t a b, |f t a - f t b| ≤ L * |a - b|) →
      ∃ φ, apm_m93j06_IsFlow f φ) ∧
    (¬ ∀ α : ℝ, 0 < α → α < 1 → ∀ f : ℝ → ℝ → ℝ,
      (∃ K > 0, ∀ t a b,
        |f t a - f t b| ≤ K * Real.rpow |a - b| α) →
      ∀ y₀, ∃! y : ℝ → ℝ, apm_m93j06_Solves f y₀ y) ∧
    (∀ f φ C L, 0 ≤ C → 0 ≤ L → apm_m93j06_IsFlow f φ →
      (∀ t y, |f t y| ≤ C * |y|) →
      (∀ t a b, |f t a - f t b| ≤ L * |a - b|) →
      ∀ t a b, |φ t a - φ t b| ≤ Real.exp (L * |t|) * |a - b|) := by
  /-
  Boundary: Mathlib provides local existence through `IsPicardLindelof` and
  uniqueness/stability through `ODE_solution_unique_univ` and
  `dist_le_of_trajectories_ODE`. The first and third conjuncts here require
  constructing compatible solutions on an exhausting family of compact time
  intervals and gluing them into a single function on all of `ℝ`; the growth
  conjunct additionally needs a continuation argument.

  The second conjunct requires differentiable dependence of the resulting
  flow on initial data (not merely regularity of each trajectory). The fourth
  requires formalizing a nonunique Hölder vector field such as
  `y ↦ sqrt |y|` with two global `HasDerivAt` solutions. Finally, the last
  estimate needs separate forward- and backward-time Gronwall applications
  translated from norm/dist bounds to the exact absolute-value expression.
  I found the relevant local APIs in
  `Mathlib.Analysis.ODE.PicardLindelof` and
  `Mathlib.Analysis.ODE.Gronwall`, but no compiled sibling assembled these
  global and parameter-dependence bridges within this pass.

  Closer hop 1 extracts the structural consequences of the custom flow
  predicate as `apm_m93j06_flow_zero` and
  `apm_m93j06_flow_hasDerivAt`; the helper
  `apm_m93j06_flow_distance_zero` closes the base-time case of the final
  stability estimate. Source inspection additionally identifies
  `IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith`,
  which already builds a local flow Lipschitz in initial data, but only on one
  closed time interval and one initial-data ball. It does not supply the `C¹`
  dependence required by the second frozen conjunct.

  Searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, closed ODE artifacts,
  and git history found no globalization theorem or formalized square-root
  nonuniqueness example. The live bridges remain compatible exhaustion/gluing,
  differentiable parameter dependence, the Hölder counterexample, and the two
  time orientations of Gronwall. The frozen statement was left unchanged.

  CLOSER HOP 2 (partial). The square-root nonuniqueness example is now
  compiled through four lemmas. `apm_m93j06_hasDerivAt_mul_abs` proves
  globally, including at the nonsmooth point of `abs`, that
  `(t * |t|)' = 2 * |t|`; `apm_m93j06_sqrt_abs_mul_abs` identifies the field
  value along this curve. Consequently `apm_m93j06_zero_solves_sqrt` and
  `apm_m93j06_signedSquare_solves_sqrt` give two global solutions of
  `y' = 2 * sqrt |y|` with initial value zero, and
  `apm_m93j06_signedSquare_ne_zero` proves they are distinct. This goes beyond
  the prior hop's proposed example by closing all trajectory and
  nonuniqueness obligations.

  The fourth conjunct is now reduced solely to the global `1/2`-Hölder bound
  for `y ↦ 2 * sqrt |y|`; Mathlib's square-root continuity and derivative APIs
  do not package the required difference inequality. The other live bridges
  remain compact-interval exhaustion/gluing, differentiable dependence in
  initial data, and backward/forward Gronwall. Searches of the square-root,
  `rpow`, Picard--Lindelöf, and Gronwall sources and the partial ODE siblings
  `m00A05`, `m96A02`, and `m96J02` found no theorem completing those pieces.
  The frozen statement remains unchanged.

  CLOSER HOP 3 (partial). The fourth frozen conjunct is now fully closed by
  `apm_m93j06_not_holder_unique`. The new elementary lemma
  `apm_m93j06_abs_sqrt_sub_sqrt_le_sqrt_abs_sub` proves
  `|sqrt u - sqrt v| ≤ sqrt |u-v|` for nonnegative reals by ordering the
  square roots and comparing squares. Combining it with
  `abs_abs_sub_abs_le_abs_sub` gives the exact global exponent-`1/2` bound
  with constant `2` in `apm_m93j06_sqrt_field_holder`. The negation proof then
  instantiates the universal uniqueness claim with this field and contradicts
  uniqueness using the two compiled global trajectories from hop 2.

  The remaining first, second, third, and fifth conjuncts still require the
  same global ODE infrastructure: compatible compact-interval exhaustion,
  differentiable dependence on initial data, continuation under linear
  growth, and forward/backward Gronwall. Renewed inspection of Mathlib's
  square-root/rpow, Picard--Lindelöf, and Gronwall APIs and the cited siblings
  yielded no packaged globalization theorem. The frozen statement remains
  unchanged.

  HOP 4 (failed-with-statement). A full search of
  `Mathlib.Analysis.ODE.PicardLindelof`, including every theorem in the
  `IsPicardLindelof` namespace, confirms that all existence constructors have
  a bounded time interval in their conclusions. `ODE_solution_unique_univ`
  supplies uniqueness only after two global solutions have already been
  constructed. Neither `LEMMA-INDEX.md` nor `ConstructionTargets/` contains a
  continuation or compatible-exhaustion theorem.

  The precise missing globalization lemma is:

      theorem apm_m93j06_global_exists_unique_of_continuous_lipschitz
          (f : ℝ → ℝ → ℝ)
          (hcont : Continuous (Function.uncurry f))
          (hLip : ∃ L > 0, ∀ t a b,
            |f t a - f t b| ≤ L * |a - b|) (y₀ : ℝ) :
          ∃! y : ℝ → ℝ, apm_m93j06_Solves f y₀ y

  It is true: continuity bounds `f (·) 0` on every compact time interval and
  the global Lipschitz estimate gives the linear growth bound needed to
  continue each local solution; uniqueness makes the exhaustion compatible.
  This statement closes the first conjunct directly and supplies the global
  trajectories used to construct the flow in the third conjunct. Proving it
  here would require developing the missing continuation/gluing machinery,
  not merely connecting two existing declarations. The second and fifth
  conjuncts additionally retain their parameter-differentiability and
  two-sided Gronwall assemblies.

  HOP 5 (partial). The fifth conjunct is now isolated and fully proved by
  `apm_m93j06_flow_lipschitz`. For nonnegative time it applies Mathlib's
  `dist_le_of_trajectories_ODE` directly to the two trajectories. For negative
  time it applies the same theorem to the reversed vector field
  `v s x = -f (-s) x` and reversed trajectories `s ↦ φ (-s) a`; the
  derivative and Lipschitz transports are explicit. This closes the exact
  `exp (L * |t|) * |a-b|` estimate required by the frozen statement.

  The remaining dependency chain is: (1) global existence from continuity
  plus a uniform state-variable Lipschitz bound; (2) use (1) to construct the
  flow required by the linear-growth conjunct; and independently (3) prove
  differentiable dependence of an already supplied global flow on initial
  data. The Hölder counterexample and global stability conjuncts are compiled.
  The frozen statement remains unchanged.

  HOP 6 (partial). `apm_m93j06_solution_unique` now closes global uniqueness
  independently of existence using `ODE_solution_unique_univ` on `Set.univ`.
  `apm_m93j06_isFlow_of_existsUnique` packages pointwise unique solutions into
  `apm_m93j06_IsFlow` by choice, and
  `apm_m93j06_growth_flow_of_global_existence` proves the entire third frozen
  conjunct directly from the first. Thus linear growth needs no separate
  continuation argument once the stronger first conjunct is available.

  The exact remaining producers are now independent: (1) global existence
  under joint continuity and a uniform Lipschitz bound (uniqueness is already
  compiled), and (2) local `ContDiff ℝ 1` dependence of an already supplied
  global flow on initial data. Once those are available, the compiled
  packaging, Hölder counterexample, and stability lemmas assemble all five
  conjuncts. The frozen statement remains unchanged.

  HOP 7 (partial). `apm_m93j06_existsUnique_of_exists` factors the first
  producer further: only existence must come from continuation/gluing, since
  the compiled global uniqueness lemma supplies the `∃!` field.
  `apm_m93j06_of_global_and_contDiff` is a compiled end-to-end assembly theorem
  whose hypotheses are exactly the two independent remaining producers. It
  connects the first producer to the third conjunct through the choice-based
  flow packaging and discharges the fourth and fifth conjuncts with the
  compiled counterexample and Grönwall lemmas. A search of the installed
  Mathlib analysis and geometry trees found no theorem providing ODE solution
  dependence on initial parameters.

  Thus the residual has no unassembled bookkeeping: construct global solutions
  by compatible compact-interval continuation, and independently formalize
  `C¹` initial-value dependence. Supplying those two declarations to the
  assembly lemma closes the unchanged frozen theorem.

  HOP 8 (partial). The continuation side now has quantitative infrastructure.
  `apm_m93j06_exists_compact_linear_bound` uses the extreme-value theorem on
  `t ↦ |f t 0|` and the uniform Lipschitz estimate to produce, on every
  compact interval, `|f t y| ≤ M + L * |y|`. The forward Grönwall theorem
  turns this into `apm_m93j06_exists_forward_solution_bound`, an explicit
  a priori bound for every trajectory. The backward analogue
  `apm_m93j06_exists_backward_solution_bound` is compiled via the reversed
  vector field and reversed trajectory. Together these show that any local
  solution remains in a bounded state region on each finite time interval.

  The existence residual is consequently narrowed to using these bounds to
  iterate local Picard--Lindelöf solutions across a finite interval and glue
  the compatible interval solutions across an exhaustion. The independent
  `C¹` initial-value dependence producer remains unchanged.

  HOP 9 (partial). Local existence is now constructed at every time-state
  point. `apm_m93j06_isPicardLindelof_of_box` converts the elementary
  continuity, Lipschitz, field-bound, and time-radius inequalities into
  Mathlib's exact `IsPicardLindelof` structure, and
  `apm_m93j06_exists_local_solution_of_box` invokes its differential-form
  constructor. Finally `apm_m93j06_exists_local_solution` builds such a box
  from the frozen hypotheses: compactness bounds the field on a unit rectangle
  and the explicit lifespan `(max C 1)⁻¹` satisfies the Picard radius
  constraint.

  Global existence is therefore reduced to a continuation/gluing theorem:
  extend these local solutions while the compiled forward/backward a priori
  bounds keep their states in compact regions, obtain solutions on every
  finite interval, and glue by compiled uniqueness. The independent `C¹`
  initial-value dependence producer remains.

  HOP 10 (partial). The gluing compatibility layer is compiled in the native
  local-solution interface. `apm_m93j06_interval_solution_unique` converts
  `HasDerivWithinAt` data on a closed interval to ordinary derivatives in its
  interior and applies Mathlib's two-sided interval uniqueness theorem.
  `apm_m93j06_interval_solutions_eqOn_overlap` restricts two solutions from
  different intervals to their closed overlap and proves equality there from
  one common interior anchor. Thus local Picard pieces can be glued without
  first extending them to global derivative statements.

  The remaining existence construction must organize a chain of overlapping
  local intervals covering each finite interval, use the overlap lemma for
  compatibility, and then exhaust `ℝ`; the compiled a priori bounds prevent
  finite-time escape. The independent `C¹` dependence producer is unchanged.

  HOP 11 (partial). The finite continuation gluing operation itself is now
  compiled. `apm_m93j06_exists_glued_interval_solution` joins solutions on
  adjacent closed intervals by a piecewise function. Away from the seam it
  transports the appropriate within-derivative through a relative
  neighborhood; at the seam, matching values make the ODE derivatives equal
  and `HasDerivWithinAt.union` combines the two one-sided derivatives. The
  result agrees with both inputs and solves the ODE on the combined interval.

  The global-existence residual is the covering argument that produces a
  finite chain of local solutions up to any prescribed endpoint, induction
  using this compiled gluing operation, and exhaustion of `ℝ`. The a priori
  bounds, local constructor, compatibility theorem, and binary gluing step are
  all present. The independent `C¹` producer remains.

  HOP 12 (partial). Genuine endpoint extension is now compiled in both
  directions. `apm_m93j06_exists_extension_right` applies local existence at
  the current right endpoint, restricts the symmetric local solution to its
  right half, and uses the binary gluing theorem to extend by a positive
  amount while preserving the old interval. The left-extension theorem is
  symmetric. These results convert the local constructor and seam proof into
  the exact operation needed by a maximal-interval continuation argument.

  The remaining global-existence work is to construct a maximal compatible
  interval solution (or an equivalent finite-cover chain), use endpoint
  extension and the a priori bounds to show its endpoints are infinite, and
  package the resulting global derivative. The independent `C¹` initial-value
  dependence producer remains.

  HOP 13 (partial). The quantitative ingredients for excluding a finite
  maximal endpoint are now compiled. `apm_m93j06_exists_uniform_local_solution`
  bounds the field on one compact time--state rectangle and chooses a single
  positive Picard lifespan valid throughout prescribed compact time and
  bounded state regions. `apm_m93j06_interval_solution_lipschitzOn` applies
  the mean-value theorem to a within-derivative solution with bounded field
  values, and `apm_m93j06_interval_solution_dist_le` exposes the explicit
  `|y s-y t| ≤ Q|s-t|` estimate. Thus a trajectory approaching a finite
  endpoint is Cauchy, has a limiting state, and can restart uniformly.

  The global-existence residual is the order/topology packaging of the maximal
  compatible solution and its endpoint limit, followed by the compiled
  restart and gluing operations. The independent `C¹` producer remains.

  HOP 14 / ROUND-10 STRATEGY CHECKPOINT. The end-to-end route is revised to
  avoid both Zorn maximality and endpoint-limit packaging. For each `T > 0`,
  form the bounded set of right endpoints reachable by an interval solution
  from zero. Its supremum equals `T`: the interval-native a priori bound keeps
  every endpoint in a fixed state ball, uniform local existence supplies one
  restart radius, and a point sufficiently close to the supremum extends past
  it. Time reversal gives the negative interval. Glue at zero to obtain a
  solution on every symmetric compact interval. Finally choose one solution
  for each radius and define the global solution at `t` from radius `|t|+1`;
  overlap uniqueness makes this locally equal to any fixed sufficiently large
  radius-solution, yielding the global derivative.

  `apm_m93j06_exists_forward_interval_solution_bound` repairs the critical
  interface mismatch found at this checkpoint: unlike the older global a
  priori lemma, it consumes the exact `HasDerivWithinAt` output of the local
  Picard constructor. The remaining ordered global obligations are reachable
  endpoint nonemptiness/boundedness, the `sSup` extension contradiction,
  backward transport and gluing, and radius-choice globalization.
  Independently, `C¹` dependence requires a variational-equation proof:
  establish the exponential-integral derivative formula, control
  difference-quotient remainders uniformly on compact tubes, apply
  approximate-trajectory Grönwall, and prove continuity of the resulting
  derivative. Source audit confirmed Mathlib has only Lipschitz initial
  dependence, not this theorem.

  HOP 15 (partial). The reachable-endpoint order layer and its uniform state
  control are now compiled. `apm_m93j06_exists_reachable_le` proves that the
  endpoint set below any positive target is nonempty;
  `apm_m93j06_reachableSet_nonempty_bddAbove` packages exactly the hypotheses
  needed for `csSup`; and `apm_m93j06_exists_bound_reachable_le` applies the
  interval-native Gronwall estimate to put the endpoint of every such
  solution in one closed ball independent of the reachable endpoint.

  The next global-existence step is the `sSup` contradiction itself: choose a
  reachable endpoint uniformly close to the supremum, restart there with the
  compiled uniform extension theorem, and restrict the extension to a new
  endpoint still below the target but above the supremum. Backward transport,
  symmetric gluing, and radius-choice globalization then remain. The
  independent variational-equation proof of `C¹` dependence also remains.

  HOP 16 (partial). The supremum continuation argument and finite-interval
  existence are compiled end to end. `apm_m93j06_exists_forward_interval_solution`
  proves that the reachable-endpoint supremum is the requested positive target:
  any strict gap is crossed by a uniformly sized restart, and a second restart
  from an endpoint near the supremum reaches the target itself. The time-reversed
  field gives `apm_m93j06_exists_backward_interval_solution`; binary gluing at
  the shared initial value then gives `apm_m93j06_exists_symmetric_interval_solution`
  on every `[-T,T]`.

  Global existence is reduced to radius-choice globalization: select a
  symmetric solution at every sufficiently large radius and use interval
  uniqueness on overlaps to define one compatible global trajectory and prove
  its pointwise derivative. The independent `C¹` variational producer remains.

  HOP 17 (partial). Radius-choice globalization is compiled.
  `apm_m93j06_exists_global_solution` chooses a solution on radius `|a|+1`
  for every index `a`, defines the global curve by evaluating the `t`-indexed
  choice at `t`, and uses overlap uniqueness to show this curve is locally
  equal to the fixed `t`-indexed solution. This yields `HasDerivAt` at every
  time. `apm_m93j06_global_existsUnique` combines that construction with the
  compiled uniqueness theorem and exactly proves the first frozen conjunct;
  the compiled flow-packaging theorem consequently supplies the third.

  The sole mathematical producer still missing is local `ContDiff ℝ 1`
  dependence on the initial value for an already supplied global flow under
  joint `ContDiff ℝ 1` regularity. Once its variational-equation proof is
  compiled, `apm_m93j06_of_global_and_contDiff` closes the entire theorem.

  HOP 18 (partial). The variational-equation interface is now compiled.
  `apm_m93j06_partialY` extracts the state-coordinate Fréchet derivative of
  the uncurried field; joint `C¹` regularity makes it jointly continuous, and
  `apm_m93j06_hasDerivAt_slice` identifies it with the ordinary derivative of
  every fixed-time slice. The diagonal extension theorem for `dslope` then
  gives the correct continuous limiting coefficient. Finally,
  `apm_m93j06_flow_difference_hasDerivAt` and
  `apm_m93j06_flow_quotient_solves` prove that every nonzero initial-data
  difference quotient starts at one and solves the exact scalar linear ODE
  with coefficient `dslope (f t) (φ t a) (φ t b)`.

  The exact residual is to prove continuous dependence of these scalar linear
  equations as `b → a` on a small compact time interval, identify the limit
  with the exponential-integral solution using Grönwall, and package the
  resulting pointwise derivative and its continuity via
  `contDiff_one_iff_deriv`.

  HOP 19 (partial). The scalar linear ODE endpoint is compiled independently
  of the flow. `apm_m93j06_linearSolution` is the exponential of the interval
  integral of the coefficient, and its derivative is established directly by
  the fundamental theorem of calculus. `apm_m93j06_linear_ode_eq_exp_integral`
  proves uniqueness globally: division by the nonvanishing exponential
  solution has derivative zero, hence is the constant one.

  The remaining bridge is now coefficient-level. Replace the time-varying
  `dslope` by the integral average of `apm_m93j06_partialY` along the segment
  between the two trajectories; the fundamental theorem gives the same exact
  field difference while the averaged coefficient is jointly continuous.
  Its compact-uniform convergence to the diagonal coefficient yields the
  derivative formula and continuity needed by `contDiff_one_iff_deriv`.

  HOP 20 (partial). The continuous averaged coefficient and exact secant
  formula are compiled. `apm_m93j06_averagePartialY` integrates the jointly
  continuous state derivative along the segment between two states;
  `apm_m93j06_continuous_averagePartialY` proves joint continuity in time and
  both endpoints, while the fundamental-theorem lemma proves its product with
  `b-a` is exactly `f t b-f t a`. It reduces on the diagonal to
  `apm_m93j06_partialY`. Composition with two flow trajectories is continuous,
  so `apm_m93j06_flow_secant_eq_exp_integral` identifies every nontrivial
  initial-data secant exactly with the exponential integral of this averaged
  coefficient.

  The residual is now topological: obtain local continuity of `φ s b` in `b`
  uniformly for `s` in a small compact interval (from a compact bound on the
  averaged coefficient and Grönwall), pass the continuous coefficient through
  the compact interval integral as `b → a`, and use the exact secant formula
  to prove the derivative formula and its continuity. Then
  `contDiff_one_iff_deriv` and the assembly lemma finish.

  HOP 21 (partial). The entire secant-limit and `C¹` packaging argument is now
  compiled conditional only on joint continuity of the supplied flow.
  `apm_m93j06_continuous_intervalIntegral_param` supplies the required
  parameter-continuity of finite interval integrals. The exact secant formula
  then converges to the diagonal exponential coefficient, proving
  `apm_m93j06_flow_hasDerivAt_initial_of_continuous`. A second application of
  parameter-integral continuity shows that this derivative varies
  continuously with the initial value, and
  `apm_m93j06_flow_contDiff_initial_of_continuous` packages the result through
  `contDiff_one_iff_deriv` for every time. The final reduction lemma turns any
  joint continuous-dependence theorem directly into the second conjunct.

  Thus the sole residual is now: prove `Continuous (Function.uncurry φ)` for
  every global flow of a jointly `C¹` scalar field. It suffices to construct
  local Picard flow maps around each `(t,a)` and identify them with `φ` by
  uniqueness, then combine continuity in time and initial value locally. Once
  compiled, the existing reduction and assembly lemmas eliminate the final
  `sorry`.

  HOP 22 (partial). The local-uniqueness infrastructure needed to identify a
  supplied flow with Picard families is compiled without assuming a global
  Lipschitz constant. `apm_m93j06_exists_compact_state_lipschitz` bounds the
  continuous state derivative on any compact time-state rectangle and turns
  that bound into a uniform state Lipschitz estimate by the convex mean-value
  theorem. `apm_m93j06_trajectories_eq_of_contDiff_eq_at` bounds two arbitrary
  trajectories on a compact interval containing a meeting time and a target
  time, applies that local Lipschitz estimate, and proves equality at the
  target. Thus two global trajectories that meet at any time agree globally;
  ordinary initial-value uniqueness is an immediate corollary.

  The sole residual remains joint continuity of the supplied flow. The next
  step is to invoke Picard's continuous local-flow constructor in a positive
  initial-state ball and use arbitrary-time meeting uniqueness to identify
  every local Picard curve with the corresponding supplied global trajectory.
  This proves continuity locally around each restart point; finite restart
  chains propagate it from time zero to every `(t,a)`. The compiled C¹
  reduction and final assembly then close the theorem.

  HOP 23 (partial). Positive-radius local continuous-flow charts are now
  compiled. `apm_m93j06_isPicardLindelof_of_box_radius` exposes the exact
  nonzero initial-radius form of Mathlib's Picard box, and
  `apm_m93j06_exists_continuous_local_flow_of_box_radius` extracts its jointly
  continuous family of solutions. Finally,
  `apm_m93j06_exists_continuous_local_flow` constructs such a chart around
  every time-state point directly from joint `C¹` regularity, using compact
  bounds for the field and its state derivative and an explicit positive
  lifespan.

  The exact residual is to identify these within-interval Picard curves with
  the supplied global flow. A curve based at an arbitrary restart time must
  first be glued to the appropriate global-flow trajectory outside the local
  interval (or uniqueness must be formulated locally at the meeting time);
  the compiled arbitrary-time global uniqueness theorem can then identify the
  glued curve. These local identifications yield joint continuity of the
  supplied flow, after which the compiled C¹ reduction and final assembly
  eliminate the sole remaining `sorry`.

  HOP 24 (partial, strategy checkpoint). The identification obstruction is
  now resolved locally. `apm_m93j06_interval_solution_unique_of_contDiff`
  proves uniqueness for two within-interval solutions using compact bounds on
  their ranges, so no artificial global extension and no global Lipschitz
  hypothesis is needed. `apm_m93j06_flow_continuousAt_of_timeSlice` then
  identifies the positive-radius Picard family with the supplied flow and
  proves the restart principle: continuity of `φ t₀` at `a` implies joint
  continuity of `(t,x) ↦ φ t x` at `(t₀,a)`.

  The final topological step must retain the neighborhood information hidden
  by the pointwise restart lemma. Strengthen it to a chart statement saying
  that continuity of the time-`t₀` slice on an initial-value neighborhood
  yields joint continuity on a smaller time-state rectangle. Starting from
  `φ 0 = id`, propagate those rectangles along the compact time segment from
  zero to an arbitrary target time by a finite subcover/Lebesgue-number
  argument. This gives global joint continuity, and the already compiled
  secant-limit theorem and assembly lemma then eliminate the sole `sorry`.

  HOP 25 (partial). The compact propagation modulus is compiled.
  `apm_m93j06_exists_uniform_continuous_local_flow_along` bounds a fixed
  supplied trajectory on any compact target interval, enlarges that range to
  a compact state tube, and bounds both the field and its state derivative on
  the tube. It consequently supplies one explicit positive lifespan and one
  positive initial-state radius for Picard charts at every restart point of
  the trajectory. This removes the possible shrinking-step obstruction in
  the finite propagation argument.

  The exact residual is now to package one chart as a time-slice propagation
  lemma (continuity at `t₀` implies continuity at the same initial value for
  every time within the common lifespan), iterate it a finite number of times
  across `[min 0 t, max 0 t]`, and derive joint continuity from the compiled
  pointwise restart theorem. The compiled secant-limit and assembly then close
  the sole remaining `sorry`.

  HOP 26 (partial). The time-slice propagation rule is compiled in both its
  explicit-chart and existential forms.
  `apm_m93j06_flow_timeSlice_continuousAt_of_local_flow` composes a continuous
  Picard chart with the restart slice and uses interval `C¹` uniqueness to
  identify it with `φ`; `apm_m93j06_flow_timeSlice_continuousAt_near` packages
  the result as persistence of slice continuity on a nontrivial open time
  interval.

  The sole residual is the finite iteration of this rule using the uniform
  lifespan from HOP 25. Formalize the arithmetic grid (in both time
  orientations), induct continuity of the slice at the fixed initial value,
  and then apply the compiled pointwise restart theorem to obtain joint
  continuity everywhere. The secant-limit theorem and assembly close all five
  conjuncts after that topological step.

  HOP 27 (complete). `apm_m93j06_flow_timeSlice_continuousAt` performs the
  finite arithmetic-grid propagation in both time orientations using the
  uniform lifespan from HOP 25. Every time slice is therefore continuous at
  every initial value. The pointwise restart theorem upgrades this to joint
  continuity of the supplied flow; the compiled exponential-integral secant
  argument gives `C¹` dependence, and the assembly theorem closes all five
  frozen conjuncts without `sorry`.
  -/
  exact apm_m93j06_of_global_and_contDiff
    apm_m93j06_global_existsUnique apm_m93j06_smooth_dependence
