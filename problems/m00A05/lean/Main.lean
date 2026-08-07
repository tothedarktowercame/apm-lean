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
    Boundary after closer hop 1 for global well-posedness: Mathlib's
    `Analysis/ODE/PicardLindelof.lean` provides local existence through
    `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt` and local-flow
    variants. The frozen theorem, however, asks for a single representative on
    `[0,∞)`, continuity at zero, an interior `deriv` equation, and uniqueness
    as `EqOn` on the whole half-line. Searches found no packaged globalization
    theorem for a globally Lipschitz autonomous vector field. Completing this
    conjunct requires iterating local solutions with compatible overlap uniqueness, and converting
    `HasDerivWithinAt` data into the exact `apm_m00A05_isSolution` predicate.
    The nearby `m96A02` artifact has the same intended Picard route but remains
    unproved, so it was discarded as a dependency.

    New progress: `apm_m00A05_lipschitz_vectorField` proves the formerly open
    analytic prerequisite globally, with constant `2`, by combining
    `Real.lipschitzWith_cos` and `LipschitzWith.id` through
    `LipschitzWith.sub`. `Gronwall.lean` also provides
    `ODE_solution_unique_univ`, so global uniqueness need not be obtained by
    manually chaining local overlap uniqueness once the solutions are expressed
    in its `HasDerivAt` format. The remaining hard bridge is global existence
    and conversion between Picard's interval solution and the frozen half-line
    regularity predicate.

    Closer hop 2 searched the full Picard--Lindelöf source, including
    `IsPicardLindelof.of_time_independent`, all local-flow constructors, and
    `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt`.
    Every existence result remains confined to one bounded interval; there is
    no maximal-solution or globally-Lipschitz continuation declaration.
    The new helper `apm_m00A05_hasDerivAt_of_isSolution` does close the reverse
    conversion: a frozen solution gives the standard `HasDerivAt` ODE at every
    positive time. Thus global uniqueness can now use Gronwall after extending
    or translating the half-line solutions, while existence still requires a
    compatible countable gluing of local Picard solutions.

    Closer hop 3 inspected the exact hypotheses of
    `ODE_solution_unique_univ` and `ODE_solution_unique`.  The former requires
    `HasDerivAt` at every real time, while the latter requires a right
    derivative at the left endpoint.  Neither can start at zero because the
    frozen predicate deliberately assumes only continuity there.  The viable
    endpoint route is now explicit: apply
    `dist_le_of_trajectories_ODE` on every `[δ,t]` with `0 < δ`, obtaining
    `dist (u t) (v t) ≤ dist (u δ) (v δ) * exp (2 * (t-δ))`, and send
    `δ ↓ 0` using continuity and the common initial value.  This would close
    uniqueness without changing the predicate, but does not supply the still
    missing global Picard gluing needed for the existential witness.
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
      Boundary after closer hop 1 for global attraction: existence of an equilibrium `ξ ∈ [0,π/2]`
      is compiled above by the intermediate value theorem. The remaining proof
      depends on the half-line uniqueness conjunct: show trajectories cannot
      cross the constant solution, derive monotonicity from the sign of
      `cos x - x`, obtain a monotone limit, and rule out any limit other than
      `ξ` by integrating a uniform derivative bound. Searches covered
      `Real.strictAntiOn_cos`, monotone convergence at `atTop`, and derivative
      comparison/integration lemmas, but no API packages this phase-line chain
      for the statement's weak regularity (`ContinuousOn` plus
      `DifferentiableOn` only on `Ioi 0`).

      The new global Lipschitz lemma also supplies the uniqueness hypothesis
      needed for the no-crossing argument. The remaining phase-line proof still
      requires converting the frozen `deriv` equality to `HasDerivAt` on the
      interior, applying time-translation uniqueness, and assembling the
      monotone-limit contradiction.

      Closer hop 2 closes the first item with
      `apm_m00A05_hasDerivAt_of_isSolution`. Searches of the closed corpus,
      `ConstructionTargets/`, and `YoungL2.lean` found no phase-line or scalar
      ODE convergence theorem. The remaining attraction boundary is therefore
      the time-translation/no-crossing argument and the monotone-limit
      contradiction, rather than derivative-format conversion.

      Closer hop 3 also checked whether the global Gronwall declaration could
      directly provide no-crossing.  Its all-time derivative hypothesis again
      fails at the frozen endpoint.  After the preceding `[δ,t]` limiting
      uniqueness lemma is formalized, no-crossing can be recovered by applying
      it to time translates at a hypothetical first contact; the subsequent
      monotone trapping and limit identification remain a separate scalar
      phase-line development.
      -/
      sorry
