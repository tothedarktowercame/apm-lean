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
  -/
  sorry
