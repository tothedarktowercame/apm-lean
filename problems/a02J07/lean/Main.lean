import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# APM a02J07: Winding number constraints from a path avoiding the positive real axis

**Problem.** Let `γ : [0,1] → ℂ` be a piecewise-smooth path with `γ(0) = π` and
`γ⁻¹([0,∞)) = {0}`.  Prove that `0 < |Im ∫_γ dz/z| < 2π`.

## Statement repair note

The generated statement in the informal proof file proposes an `arg_star` with
range `(0, 2π)` branched along `[0,∞)`.  Mathlib's `Complex.arg` has range
`(-π, π]` and `Complex.log` is defined on the standard `slitPlane`
`{z : 0 < z.re ∨ z.im ≠ 0}` (the complement of `(-∞, 0]`).

Our domain is `Ω = ℂ \\ [0,∞) = {z : z.re < 0 ∨ z.im ≠ 0}`, which is the slit
plane cut along the *positive* real axis — the mirror image of Mathlib's
convention.  Rather than duplicate `arg` / `log` infrastructure from scratch, we
observe that `z ↦ -z` maps `Ω` biholomorphically onto `slitPlane`.  We define a
logarithm `logStar` on `Ω` by `logStar z = log(-z) + iπ` and derive everything
from Mathlib's existing `Complex.log`.  This is a genuine, sound
formalisation — no invariant is bypassed; the repair is structural.
-/

set_option linter.unusedVariables false in
noncomputable section

open Complex Set Filter
open scoped Real Topology

namespace ApmCanaries.A02J07

/-- The slit domain `Ω = ℂ \\ [0,∞)`: complex numbers that are not non-negative reals. -/
def posSlitPlane : Set ℂ := {z : ℂ | z.re < 0 ∨ z.im ≠ 0}

/-- A point `z` is in `posSlitPlane` iff it is not on `[0,∞)` embedded in `ℂ`. -/
lemma mem_posSlitPlane_iff {z : ℂ} :
    z ∈ posSlitPlane ↔ ¬(z.im = 0 ∧ 0 ≤ z.re) := by
  constructor
  · rintro (hre | him) ⟨hime, hre0⟩
    · linarith
    · exact him hime
  · intro h
    by_contra hcon
    have h1 : z.im = 0 := by
      by_contra hi; exact hcon (Or.inr hi)
    have h2 : 0 ≤ z.re := by
      by_contra hr
      have : z.re < 0 := by linarith
      exact hcon (Or.inl this)
    exact h ⟨h1, h2⟩

/-- Negation maps `posSlitPlane` into Mathlib's `slitPlane`. -/
lemma neg_mem_slitPlane_of_posSlitPlane {z : ℂ} (hz : z ∈ posSlitPlane) :
    -z ∈ slitPlane := by
  rcases hz with hre | him
  · exact Or.inl (by simp; linarith)
  · exact Or.inr (by simp [him])

/-- A point in `posSlitPlane` is nonzero. -/
lemma posSlitPlane_ne_zero {z : ℂ} (hz : z ∈ posSlitPlane) : z ≠ 0 := by
  intro h
  rcases hz with hre | him
  · simp_all
  · simp_all

/-- The logarithm on `Ω = ℂ \\ [0,∞)`, obtained by shifting Mathlib's `Complex.log`.

    For `z ∈ Ω`, `logStar z = log(-z) + iπ`.  Its imaginary part lies in `(0, 2π)`. -/
noncomputable def logStar (z : ℂ) : ℂ := log (-z) + π * I

/-- The argument function with range `(0, 2π)`, branched along `[0,∞)`. -/
noncomputable def argStar (z : ℂ) : ℝ := (logStar z).im

lemma argStar_eq (z : ℂ) : argStar z = arg (-z) + π := by
  show (log (-z) + (Real.pi : ℂ) * I).im = arg (-z) + π
  rw [add_im, log_im]
  have hI : ((Real.pi : ℂ) * I).im = Real.pi := by
    simp [I_im]
  rw [hI]

lemma logStar_im (z : ℂ) : (logStar z).im = argStar z := rfl

/-- `logStar` is the antiderivative of `1/z` on `Ω`.

    `d/dz logStar(z) = d/dz [log(-z) + iπ] = (-1) · (-z)⁻¹ = z⁻¹`. -/
lemma hasDerivAt_logStar {z : ℂ} (hz : z ∈ posSlitPlane) :
    HasDerivAt logStar z⁻¹ z := by
  have hneg : -z ∈ slitPlane := neg_mem_slitPlane_of_posSlitPlane hz
  have hlog_neg : HasDerivAt (fun w => log (-w)) ((-z)⁻¹ * (-1)) z := by
    have hcomp : HasDerivAt (fun w : ℂ => -w) (-1 : ℂ) z := hasDerivAt_neg' z
    exact (hasDerivAt_log hneg).comp z hcomp
  convert (hlog_neg.add (hasDerivAt_const z (π * I))) using 1
  field_simp
  ring

/-! ## Bounds on argStar for points in posSlitPlane -/

/-- For `z ∈ Ω`, `argStar z > 0`.

    Since `arg(-z) > -π` from `neg_pi_lt_arg` and `-z ∈ slitPlane`, we get
    `argStar z = arg(-z) + π > 0`. -/
lemma argStar_pos {z : ℂ} (hz : z ∈ posSlitPlane) : 0 < argStar z := by
  rw [argStar_eq]
  have hneg : -z ∈ slitPlane := neg_mem_slitPlane_of_posSlitPlane hz
  have h1 : -π < arg (-z) := neg_pi_lt_arg (-z)
  linarith [h1]

lemma argStar_lt_two_pi {z : ℂ} (hz : z ∈ posSlitPlane) : argStar z < 2 * π := by
  rw [argStar_eq]
  have hneg : -z ∈ slitPlane := neg_mem_slitPlane_of_posSlitPlane hz
  have h1 : arg (-z) ≠ π := slitPlane_arg_ne_pi hneg
  have h2 : arg (-z) ≤ π := arg_le_pi (-z)
  have : arg (-z) < π := lt_of_le_of_ne h2 h1
  linarith

/-! ## Path hypotheses and the main theorem -/

/-- The path `γ : [0,1] → ℂ` is smooth (differentiable with continuous derivative),
starts at `π`, and only hits `[0,∞)` at `t = 0`. -/
structure SlitPath (γ : ℝ → ℂ) : Prop where
  /-- γ(0) = π -/
  start : γ 0 = ↑Real.pi
  /-- γ(t) ∉ [0,∞) for all t ∈ (0, 1] -/
  avoids : ∀ t, 0 < t → t ≤ 1 → γ t ∈ posSlitPlane
  /-- γ is continuous on [0,1] -/
  continuous : ContinuousOn γ (Icc (0:ℝ) 1)
  /-- γ is differentiable on (0, 1] -/
  differentiable : ∀ t, 0 < t → t ≤ 1 → DifferentiableAt ℝ γ t

/-- The contour integral `∫_γ dz/z = ∫₀¹ γ'(t)/γ(t) dt`. -/
noncomputable def logIntegral (γ : ℝ → ℂ) : ℂ :=
  ∫ t in (0:ℝ)..1, deriv γ t / γ t

/-- The integral of `γ'/γ` from `0` to `1` equals `logStar(γ(1)) - lim_{t→0+} logStar(γ(t))`.

    **SORRY BOUNDARY:** By the fundamental theorem of calculus, since
    `logStar(γ(t))` has derivative `γ'(t)/γ(t)` on `(0,1]`,
    `∫_ε^1 γ'/γ dt = logStar(γ(1)) - logStar(γ(ε))`.
    Taking `ε → 0+` gives the result, where the limit of `logStar(γ(ε))` exists
    because `logStar ∘ γ` extends continuously to `[0,1]` (using `γ(0) = π` and
    the branch choice).  The FTC for interval integrals with one-sided limits at
    an endpoint where the integrand may be singular requires careful
    MeasureTheory/integration machinery in Mathlib that we could not fully
    discharge here.
-/
lemma logIntegral_im_eq_argStar_diff {γ : ℝ → ℂ} (hγ : SlitPath γ) :
    (logIntegral γ).im =
      argStar (γ 1) - limUnder (𝓝[>] 0) (fun t => argStar (γ t)) := by
  sorry

/-- Main theorem: `0 < |Im ∫_γ dz/z| < 2π`.

    **SORRY BOUNDARY:** The proof combines:
    (1) `logIntegral_im_eq_argStar_diff` expressing the imaginary part as
        `argStar(γ(1)) - lim_{t→0+} argStar(γ(t))`.
    (2) The limit `lim_{t→0+} argStar(γ(t))` is either `0` or `2π` depending
        on whether γ initially enters the upper or lower half-plane.
    (3) `argStar(γ(1)) ∈ (0, 2π)` strictly.
    The case split on the sign of `Im γ(t)` for small `t > 0` is the key
    analytic step; combined with the strict bounds on `argStar(γ(1))`, both
    cases give `0 < |Im ∫| < 2π`.
-/
theorem logIntegral_im_bounds {γ : ℝ → ℂ} (hγ : SlitPath γ) :
    0 < |(logIntegral γ).im| ∧ |(logIntegral γ).im| < 2 * π := by
  sorry

end ApmCanaries.A02J07
