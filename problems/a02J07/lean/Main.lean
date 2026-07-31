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
-- STATEMENT REPAIR 2026-07-31 (Joe-authorised): require interval integrability
-- of `γ'/γ`, so `logIntegral` cannot collapse to zero via `integral_undef`.
structure SlitPath (γ : ℝ → ℂ) : Prop where
  /-- γ(0) = π -/
  start : γ 0 = ↑Real.pi
  /-- γ(t) ∉ [0,∞) for all t ∈ (0, 1] -/
  avoids : ∀ t, 0 < t → t ≤ 1 → γ t ∈ posSlitPlane
  /-- γ is continuous on [0,1] -/
  continuous : ContinuousOn γ (Icc (0:ℝ) 1)
  /-- γ is differentiable on (0, 1] -/
  differentiable : ∀ t, 0 < t → t ≤ 1 → DifferentiableAt ℝ γ t
  /-- The logarithmic derivative is genuinely integrable along the path. -/
  integrable_logDeriv :
    IntervalIntegrable (fun t => deriv γ t / γ t) volume 0 1

/-- The contour integral `∫_γ dz/z = ∫₀¹ γ'(t)/γ(t) dt`. -/
noncomputable def logIntegral (γ : ℝ → ℂ) : ℂ :=
  ∫ t in (0:ℝ)..1, deriv γ t / γ t

/-- The path tends to its prescribed initial value from the right. -/
lemma tendsto_gamma_nhdsGT_zero {γ : ℝ → ℂ} (hγ : SlitPath γ) :
    Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝 (Real.pi : ℂ)) := by
  rw [← hγ.start]
  exact (hγ.continuous.continuousWithinAt
    (show (0 : ℝ) ∈ Icc 0 1 by norm_num)).mono_left
      (nhdsWithin_le_iff.mpr (Icc_mem_nhdsGT zero_lt_one))

/-- Near its initial point on the positive real axis, the path stays entirely
in one of the two half-planes.  Consequently `argStar ∘ γ` tends to the
corresponding edge value of the branch. -/
lemma tendsto_argStar_nhdsGT_zero_or_two_pi {γ : ℝ → ℂ} (hγ : SlitPath γ) :
    Tendsto (fun t => argStar (γ t)) (𝓝[>] (0 : ℝ)) (𝓝 0) ∨
      Tendsto (fun t => argStar (γ t)) (𝓝[>] (0 : ℝ)) (𝓝 (2 * π)) := by
  have hγ0 := tendsto_gamma_nhdsGT_zero hγ
  have hre_event : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < (γ t).re := by
    have hre_lim :
        Tendsto (fun t => (γ t).re) (𝓝[>] (0 : ℝ)) (𝓝 Real.pi) :=
      (continuous_re.tendsto _).comp hγ0
    exact hre_lim.eventually (lt_mem_nhds Real.pi_pos)
  obtain ⟨d, hd, hre⟩ :=
    mem_nhdsGT_iff_exists_Ioc_subset.mp hre_event
  let e : ℝ := min d 1
  have he_pos : 0 < e := by
    exact lt_min hd (by norm_num)
  have he_one : e ≤ 1 := min_le_right _ _
  have hS_re : ∀ t ∈ Ioc (0 : ℝ) e, 0 < (γ t).re := by
    intro t ht
    exact hre ⟨ht.1, ht.2.trans (min_le_left _ _)⟩
  have hS_ne : ∀ t ∈ Ioc (0 : ℝ) e, (γ t).im ≠ 0 := by
    intro t ht him
    rcases hγ.avoids t ht.1 (ht.2.trans he_one) with hleft | hnonreal
    · linarith [hS_re t ht]
    · exact hnonreal him
  have hS_cont : ContinuousOn (fun t => (γ t).im) (Ioc (0 : ℝ) e) :=
    (continuous_im.comp_continuousOn
      (hγ.continuous.mono fun t ht => ⟨ht.1.le, ht.2.trans he_one⟩))
  have hsign :=
    isPreconnected_Ioc.mapsTo_Ioi_or_Iio hS_cont hS_ne
  have hnegγ0 :
      Tendsto (fun t => -γ t) (𝓝[>] (0 : ℝ)) (𝓝 (-(Real.pi : ℂ))) :=
    hγ0.neg
  rcases hsign with hupper | hlower
  · left
    have him_event : ∀ᶠ t in 𝓝[>] (0 : ℝ), (-γ t).im < 0 := by
      filter_upwards [Ioc_mem_nhdsGT he_pos] with t ht
      have hu : 0 < (γ t).im := hupper ht
      simpa using neg_lt_zero.mpr hu
    have hneg_within :
        Tendsto (fun t => -γ t) (𝓝[>] (0 : ℝ))
          (𝓝[{z : ℂ | z.im < 0}] (-(Real.pi : ℂ))) :=
      tendsto_nhdsWithin_iff.mpr ⟨hnegγ0, him_event⟩
    have harg :
        Tendsto (fun t => arg (-γ t)) (𝓝[>] (0 : ℝ)) (𝓝 (-π)) := by
      exact (tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero
        (z := -(Real.pi : ℂ)) (by simp [Real.pi_pos]) (by simp)).comp hneg_within
    simpa [argStar_eq]
      using harg.add_const π
  · right
    have him_event : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ (-γ t).im := by
      filter_upwards [Ioc_mem_nhdsGT he_pos] with t ht
      have hl : (γ t).im < 0 := hlower ht
      exact neg_nonneg.mpr hl.le
    have hneg_within :
        Tendsto (fun t => -γ t) (𝓝[>] (0 : ℝ))
          (𝓝[{z : ℂ | 0 ≤ z.im}] (-(Real.pi : ℂ))) :=
      tendsto_nhdsWithin_iff.mpr ⟨hnegγ0, him_event⟩
    have harg :
        Tendsto (fun t => arg (-γ t)) (𝓝[>] (0 : ℝ)) (𝓝 π) := by
      exact (tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
        (z := -(Real.pi : ℂ)) (by simp [Real.pi_pos]) (by simp)).comp hneg_within
    simpa [argStar_eq, two_mul] using harg.add_const π

/-- Chain rule for the positive-slit logarithm along the path interior. -/
lemma hasDerivAt_logStar_comp {γ : ℝ → ℂ} (hγ : SlitPath γ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s => logStar (γ s)) (deriv γ t / γ t) t := by
  have hγt : HasDerivAt γ (deriv γ t) t :=
    (hγ.differentiable t ht.1 ht.2.le).hasDerivAt
  have hlog :
      HasDerivAt (fun s => log (-γ s)) ((-deriv γ t) / (-γ t)) t :=
    hγt.neg.clog_real
      (neg_mem_slitPlane_of_posSlitPlane (hγ.avoids t ht.1 ht.2.le))
  simpa [logStar] using hlog.add_const (π * I)

/-- The argument at the terminal endpoint is the left limit along the path. -/
lemma tendsto_argStar_nhdsLT_one {γ : ℝ → ℂ} (hγ : SlitPath γ) :
    Tendsto (fun t => argStar (γ t)) (𝓝[<] (1 : ℝ))
      (𝓝 (argStar (γ 1))) := by
  have hγ1 :
      Tendsto γ (𝓝[<] (1 : ℝ)) (𝓝 (γ 1)) :=
    (hγ.continuous.continuousWithinAt
      (show (1 : ℝ) ∈ Icc 0 1 by norm_num)).mono_left
        (nhdsWithin_le_iff.mpr (Icc_mem_nhdsLT zero_lt_one))
  have harg_cont : ContinuousAt argStar (γ 1) := by
    have hlog_cont :
        ContinuousAt logStar (γ 1) :=
      (hasDerivAt_logStar (hγ.avoids 1 zero_lt_one le_rfl)).continuousAt
    exact continuous_im.continuousAt.comp hlog_cont
  exact harg_cont.tendsto.comp hγ1

/-- The derivative of the argument along the path is the imaginary part of the
logarithmic derivative. -/
lemma hasDerivAt_argStar_comp {γ : ℝ → ℂ} (hγ : SlitPath γ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s => argStar (γ s)) (deriv γ t / γ t).im t := by
  have h :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_logStar_comp hγ ht)
  simpa [Function.comp_def, logStar_im, Complex.imCLM_apply] using h

/-- The integral of `γ'/γ` from `0` to `1` equals `logStar(γ(1)) - lim_{t→0+} logStar(γ(t))`.

    The endpoint-limit form of the fundamental theorem of calculus applies to
    `argStar ∘ γ`: its derivative is the imaginary part of `γ'/γ`, its terminal
    left limit is ordinary continuity, and its initial right limit is fixed by
    the side of the slit on which the path starts.
-/
lemma logIntegral_im_eq_argStar_diff {γ : ℝ → ℂ} (hγ : SlitPath γ) :
    (logIntegral γ).im =
      argStar (γ 1) - limUnder (𝓝[>] 0) (fun t => argStar (γ t)) := by
  have him_int :
      IntervalIntegrable (fun t => (deriv γ t / γ t).im)
        MeasureTheory.volume 0 1 :=
    ⟨Complex.imCLM.integrable_comp hγ.integrable_logDeriv.1,
      Complex.imCLM.integrable_comp hγ.integrable_logDeriv.2⟩
  have him_integral :
      (∫ t in (0 : ℝ)..1, (deriv γ t / γ t).im) =
        (logIntegral γ).im := by
    simpa [logIntegral, Complex.imCLM_apply] using
      Complex.imCLM.intervalIntegral_comp_comm hγ.integrable_logDeriv
  rcases tendsto_argStar_nhdsGT_zero_or_two_pi hγ with hzero | htwo
  · rw [hzero.limUnder_eq]
    rw [← him_integral]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
      zero_lt_one (fun t ht => hasDerivAt_argStar_comp hγ ht) him_int hzero
        (tendsto_argStar_nhdsLT_one hγ)
  · rw [htwo.limUnder_eq]
    rw [← him_integral]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
      zero_lt_one (fun t ht => hasDerivAt_argStar_comp hγ ht) him_int htwo
        (tendsto_argStar_nhdsLT_one hγ)

/-- Main theorem: `0 < |Im ∫_γ dz/z| < 2π`.

    The proof combines:
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
  have hEq := logIntegral_im_eq_argStar_diff hγ
  have hpos := argStar_pos (hγ.avoids 1 zero_lt_one le_rfl)
  have hlt := argStar_lt_two_pi (hγ.avoids 1 zero_lt_one le_rfl)
  rcases tendsto_argStar_nhdsGT_zero_or_two_pi hγ with hzero | htwo
  · rw [hzero.limUnder_eq] at hEq
    have him : (logIntegral γ).im = argStar (γ 1) := by
      simpa using hEq
    rw [him, abs_of_pos hpos]
    exact ⟨hpos, hlt⟩
  · rw [htwo.limUnder_eq] at hEq
    have him_neg : (logIntegral γ).im < 0 := by
      rw [hEq]
      linarith
    rw [abs_of_neg him_neg, hEq]
    constructor <;> linarith

end ApmCanaries.A02J07
