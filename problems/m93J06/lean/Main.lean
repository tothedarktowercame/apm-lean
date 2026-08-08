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
      · simp only [sub_zero, zero_mul, abs_zero, mul_zero, smul_zero,
          Real.norm_eq_abs]
        rw [abs_mul, abs_abs]
        rw [← abs_mul_abs_self]
        field_simp [abs_ne_zero.mpr hs]
        simp
    rw [hfun]
    simpa using continuous_abs.tendsto (0 : ℝ)
  · convert (hasDerivAt_id t).mul (hasDerivAt_abs ht) using 1
    rcases lt_or_gt_of_ne ht with htneg | htpos
    · simp [Real.sign_of_neg htneg, abs_of_neg htneg]
      ring
    · simp [Real.sign_of_pos htpos, abs_of_pos htpos]
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
lemma apm_m93j06_sqrt_field_holder (t a b : ℝ) :
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
  -/
  sorry
