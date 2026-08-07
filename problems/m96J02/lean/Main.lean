import Mathlib

open MeasureTheory

/-!
# APM m96J02

## Statement repairs

The printed theorem is false for a merely continuous `g`; for example
`g(t,x)=sqrt |x|` has nonunique solutions at zero. The standard missing
hypothesis, local Lipschitz continuity in the second variable, is added. The
integration variable `dz` in the source is corrected to `ds`, matching the
displayed integrand and the supplied solution.

## Encoding questions

None.
-/

def apm_m96j02_LocallyLipschitzInSecond (g : ℝ → ℝ → ℝ) : Prop :=
  ∀ R : ℝ, 0 < R →
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ t u v : ℝ,
        |t| ≤ R → |u| ≤ R → |v| ≤ R →
          |g t u - g t v| ≤ L * |u - v|

/-- A continuous trajectory remains a continuous trajectory after applying
the continuous nonlinearity along its graph. -/
lemma apm_m96j02_continuousOn_comp_graph
    (g : ℝ → ℝ → ℝ) (hg : Continuous fun p : ℝ × ℝ => g p.1 p.2)
    {T : ℝ} {y : ℝ → ℝ} (hy : ContinuousOn y (Set.Icc 0 T)) :
    ContinuousOn (fun t => g t (y t)) (Set.Icc 0 T) := by
  exact hg.comp_continuousOn (continuousOn_id.prodMk hy)

/-- Consequently, the nonlinear forcing along a continuous trajectory is
interval-integrable on a nonnegative time interval. -/
lemma apm_m96j02_intervalIntegrable_comp_graph
    (g : ℝ → ℝ → ℝ) (hg : Continuous fun p : ℝ × ℝ => g p.1 p.2)
    {T : ℝ} (hT : 0 ≤ T) {y : ℝ → ℝ} (hy : ContinuousOn y (Set.Icc 0 T)) :
    IntervalIntegrable (fun t => g t (y t)) volume 0 T := by
  have hc := apm_m96j02_continuousOn_comp_graph g hg hy
  rw [← Set.uIcc_of_le hT] at hc
  exact hc.intervalIntegrable

theorem apm_m96j02
    (g : ℝ → ℝ → ℝ) (hg : Continuous fun p : ℝ × ℝ => g p.1 p.2)
    (hLip : apm_m96j02_LocallyLipschitzInSecond g)
    (α β : ℝ) :
    ∃ T : ℝ, 0 < T ∧
      ∀ (x y : ℝ → ℝ),
        ContDiffOn ℝ 2 x (Set.Icc 0 T) →
        x 0 = α → deriv x 0 = β →
        (∀ t ∈ Set.Icc (0 : ℝ) T, deriv (deriv x) t = g t (x t)) →
        ContinuousOn y (Set.Icc 0 T) →
        (∀ t ∈ Set.Icc (0 : ℝ) T,
          y t = (∫ s in (0 : ℝ)..t, (t - s) * g s (y s)) + α + β * t) →
        ∀ t ∈ Set.Icc (0 : ℝ) T, x t = y t := by
  /-
  PARTIAL boundary (second-order IVP/Volterra uniqueness).  The two helpers
  above formally close the continuity and interval-integrability prerequisite
  for applying FTC to `g t (y t)`.

  Desk research found the forward calculus APIs
  `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`,
  `intervalIntegral.integral_deriv_eq_sub`, and the integration-by-parts
  theorems in `MeasureTheory.Integral.IntervalIntegral.IntegrationByParts`.
  They support proving the Taylor remainder identity
    `x t = x 0 + deriv x 0 * t + ∫ s in 0..t, (t-s) * deriv (deriv x) s`,
  but assembling it from `ContDiffOn` requires converting within-derivatives
  at both endpoints to the hypotheses of those interval-FTC lemmas.

  For uniqueness, Mathlib's `Analysis.ODE.PicardLindelof` and
  `Analysis.ODE.Gronwall` are available, but their packaged assumptions are
  for a first-order vector field on a fixed ball.  The remaining route is to
  bundle `(position, velocity) ↦ (velocity, g t position)`, derive its local
  Lipschitz-on-ball bound from `hLip`, choose a common short-time box using
  compact boundedness of `hg`, and convert the scalar `ContDiffOn` solution
  and the Volterra solution into first-order integral curves.  The direct
  alternative needs the same box bound plus the supremum estimate with factor
  `L*T^2/2`.

  PASS-1 statement-review blocker (codex).  The frozen statement is false
  because `ContDiffOn` supplies only one-sided smoothness relative to `Icc 0 T`,
  while the initial data and ODE use Mathlib's global `deriv` at the endpoint
  `0`.  Take `g := fun _ _ => 0`, `α = β = 0`, `x := fun t => |t|`, and
  `y := fun _ => 0`.  On every `Icc 0 T`, `x` agrees with the identity and is
  therefore `ContDiffOn ℝ 2`; nevertheless `deriv x 0 = 0` because `abs` is
  not two-sided differentiable there.  Mathlib's `deriv_abs` identifies
  `deriv x` with the sign function, whose derivative is again `0` at the
  nondifferentiability point by the definition of `deriv`; away from zero its
  derivative is also zero.  Hence all encoded IVP hypotheses hold.  The zero
  function satisfies the Volterra equation, but `x t = t ≠ 0 = y t` for every
  positive `t`, so no positive `T` can satisfy the conclusion.

  Searches of 172 closed artifacts, all `ConstructionTargets/`,
  `YoungL2.lean`, `LEMMA-INDEX.md`, partial boundary comments, Mathlib's
  Taylor/FTC sources, and `Analysis.ODE.Gronwall` found no way around this
  semantic endpoint mismatch.  A valid encoding would need neighborhood
  `ContDiff`/two-sided differentiability, or consistently use within-derivatives
  at the endpoint; the frozen statement cannot be repaired in this pass.
  -/
  sorry
