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
  -/
  sorry
