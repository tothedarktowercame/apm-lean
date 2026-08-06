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
  · /-
    Boundary for global well-posedness: Mathlib's
    `Analysis/ODE/PicardLindelof.lean` provides local existence through
    `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt` and local-flow
    variants. The frozen theorem, however, asks for a single representative on
    `[0,∞)`, continuity at zero, an interior `deriv` equation, and uniqueness
    as `EqOn` on the whole half-line. Searches found no packaged globalization
    theorem for a globally Lipschitz autonomous vector field. Completing this
    conjunct requires proving the vector field `cos x - x` globally Lipschitz,
    iterating local solutions with compatible overlap uniqueness, and converting
    `HasDerivWithinAt` data into the exact `apm_m00A05_isSolution` predicate.
    The nearby `m96A02` artifact has the same intended Picard route but remains
    unproved, so it was discarded as a dependency.
    -/
    sorry
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
    · /-
      Boundary for global attraction: existence of an equilibrium `ξ ∈ [0,π/2]`
      is compiled above by the intermediate value theorem. The remaining proof
      depends on the half-line uniqueness conjunct: show trajectories cannot
      cross the constant solution, derive monotonicity from the sign of
      `cos x - x`, obtain a monotone limit, and rule out any limit other than
      `ξ` by integrating a uniform derivative bound. Searches covered
      `Real.strictAntiOn_cos`, monotone convergence at `atTop`, and derivative
      comparison/integration lemmas, but no API packages this phase-line chain
      for the statement's weak regularity (`ContinuousOn` plus
      `DifferentiableOn` only on `Ioi 0`).
      -/
      sorry
