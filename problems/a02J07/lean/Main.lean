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
    IntervalIntegrable (fun t => deriv γ t / γ t) MeasureTheory.volume 0 1

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

/-! ## Piecewise-smooth slit paths (statement repair, 2026-11)

The original problem only asks for a *piecewise smooth* path.  The structure
below encodes exactly that: continuity on `[0,1]`, the prescribed start and the
avoidance condition word for word as in `SlitPath`, a strictly increasing
partition of `[0,1]`, and on each closed piece agreement with a globally `C¹`
function.  No differentiability at the corners and no integrability hypothesis
is assumed; both are derived. -/

/-- A piecewise-smooth path `γ : [0,1] → ℂ` with `γ(0) = π` avoiding `[0,∞)`
except at `t = 0`. -/
structure PiecewiseSmoothSlitPath (γ : ℝ → ℂ) where
  /-- γ(0) = π -/
  start : γ 0 = ↑Real.pi
  /-- γ(t) ∉ [0,∞) for all t ∈ (0, 1] -/
  avoids : ∀ t, 0 < t → t ≤ 1 → γ t ∈ posSlitPlane
  /-- γ is continuous on [0,1] -/
  continuous : ContinuousOn γ (Icc (0:ℝ) 1)
  /-- the number of smooth pieces -/
  npieces : ℕ
  /-- the partition points of `[0,1]` -/
  cut : ℕ → ℝ
  /-- the partition is strictly increasing up to `npieces` -/
  cut_mono : StrictMonoOn cut (Set.Iic npieces)
  cut_zero : cut 0 = 0
  cut_last : cut npieces = 1
  /-- the smooth model of each piece -/
  piece : ℕ → ℝ → ℂ
  piece_contDiff : ∀ i < npieces, ContDiff ℝ 1 (piece i)
  piece_eq : ∀ i < npieces, ∀ t ∈ Icc (cut i) (cut (i+1)), γ t = piece i t

namespace PiecewiseSmoothSlitPath

variable {γ : ℝ → ℂ} (hγ : PiecewiseSmoothSlitPath γ)

include hγ

lemma npieces_pos : 0 < hγ.npieces := by
  by_contra h
  push_neg at h
  have hz : hγ.npieces = 0 := Nat.eq_zero_of_le_zero h
  have h1 := hγ.cut_last
  rw [hz, hγ.cut_zero] at h1
  norm_num at h1

lemma cut_lt_succ (i : ℕ) (hi : i < hγ.npieces) : hγ.cut i < hγ.cut (i+1) :=
  hγ.cut_mono (Set.mem_Iic.mpr hi.le) (Set.mem_Iic.mpr hi) (Nat.lt_succ_self i)

lemma cut_mem_Icc (i : ℕ) (hi : i ≤ hγ.npieces) : hγ.cut i ∈ Icc (0:ℝ) 1 := by
  have h0 : hγ.cut 0 ≤ hγ.cut i := by
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact le_rfl
    · exact (hγ.cut_mono (Set.mem_Iic.mpr (Nat.zero_le _)) (Set.mem_Iic.mpr hi) hpos).le
  have h1 : hγ.cut i ≤ hγ.cut hγ.npieces := by
    rcases eq_or_lt_of_le hi with rfl | hi'
    · exact le_rfl
    · exact (hγ.cut_mono (Set.mem_Iic.mpr hi'.le) (Set.mem_Iic.mpr le_rfl) hi').le
  rw [hγ.cut_zero] at h0
  rw [hγ.cut_last] at h1
  exact ⟨h0, h1⟩

/-- Every point of `[0,1]` lies in some closed piece. -/
lemma exists_piece {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ i < hγ.npieces, t ∈ Icc (hγ.cut i) (hγ.cut (i+1)) := by
  have hex : ∃ k, t ≤ hγ.cut k := ⟨hγ.npieces, hγ.cut_last ▸ ht1⟩
  generalize hk_def : Nat.find hex = k
  have hk : t ≤ hγ.cut k := hk_def ▸ Nat.find_spec hex
  have hkn : k ≤ hγ.npieces := hk_def ▸ Nat.find_min' hex (hγ.cut_last ▸ ht1)
  have hmin : ∀ j, j < k → hγ.cut j < t := by
    intro j hj
    have hj' : j < Nat.find hex := by rwa [hk_def]
    exact not_le.mp (Nat.find_min hex hj')
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · refine ⟨0, hγ.npieces_pos, ?_, ?_⟩
    · rw [hγ.cut_zero]; exact ht0
    · rw [hγ.cut_zero] at hk
      have h01 : (0:ℝ) < hγ.cut 1 := by
        have h := hγ.cut_lt_succ 0 hγ.npieces_pos
        rwa [hγ.cut_zero] at h
      linarith
  · refine ⟨k - 1, by omega, ?_⟩
    have hprev : hγ.cut (k - 1) < t := hmin (k - 1) (by omega)
    exact ⟨hprev.le, by rw [Nat.sub_add_cancel hkpos]; exact hk⟩

/-- The finite set of corner points. -/
def cornerSet : Set ℝ := (fun i => hγ.cut i) '' Set.Iic hγ.npieces

lemma cornerSet_finite : hγ.cornerSet.Finite :=
  (Set.finite_Iic _).image (fun i => hγ.cut i)

lemma cornerSet_countable : hγ.cornerSet.Countable :=
  hγ.cornerSet_finite.countable

/-- A non-corner point of `(0,1)` lies in the interior of some piece. -/
lemma exists_piece_Ioo {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hc : t ∉ hγ.cornerSet) :
    ∃ i < hγ.npieces, t ∈ Ioo (hγ.cut i) (hγ.cut (i+1)) := by
  obtain ⟨i, hi, hti⟩ := hγ.exists_piece ht0.le ht1.le
  refine ⟨i, hi, ?_, ?_⟩
  · rcases lt_or_eq_of_le hti.1 with h | h
    · exact h
    · exact absurd ⟨i, Set.mem_Iic.mpr hi.le, (show hγ.cut i = t from h)⟩ hc
  · rcases lt_or_eq_of_le hti.2 with h | h
    · exact h
    · exact absurd ⟨i+1, Set.mem_Iic.mpr hi, (show hγ.cut (i+1) = t from h.symm)⟩ hc

/-- On the interior of a piece, `γ` agrees with the piece model in a whole
neighbourhood, hence has the same derivative. -/
lemma eventuallyEq_piece {i : ℕ} (hi : i < hγ.npieces) {t : ℝ}
    (ht : t ∈ Ioo (hγ.cut i) (hγ.cut (i+1))) :
    γ =ᶠ[𝓝 t] hγ.piece i := by
  filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
  exact hγ.piece_eq i hi s hs

lemma deriv_eq_piece {i : ℕ} (hi : i < hγ.npieces) {t : ℝ}
    (ht : t ∈ Ioo (hγ.cut i) (hγ.cut (i+1))) :
    deriv γ t = deriv (hγ.piece i) t :=
  (hγ.eventuallyEq_piece hi ht).deriv_eq

lemma hasDerivAt_ps {i : ℕ} (hi : i < hγ.npieces) {t : ℝ}
    (ht : t ∈ Ioo (hγ.cut i) (hγ.cut (i+1))) :
    HasDerivAt γ (deriv γ t) t := by
  rw [hγ.deriv_eq_piece hi ht]
  exact (hγ.piece_contDiff i hi).differentiable_one.differentiableAt.hasDerivAt
    |>.congr_of_eventuallyEq (hγ.eventuallyEq_piece hi ht)

/-- Chain rule for the positive-slit logarithm, off the corners. -/
lemma hasDerivAt_logStar_comp_ps {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hc : t ∉ hγ.cornerSet) :
    HasDerivAt (fun s => logStar (γ s)) (deriv γ t / γ t) t := by
  obtain ⟨i, hi, hti⟩ := hγ.exists_piece_Ioo ht0 ht1 hc
  have hd : HasDerivAt γ (deriv γ t) t := hγ.hasDerivAt_ps hi hti
  have hlog : HasDerivAt (fun s => log (-γ s)) ((-deriv γ t) / (-γ t)) t :=
    hd.neg.clog_real (neg_mem_slitPlane_of_posSlitPlane (hγ.avoids t ht0 ht1.le))
  simpa [logStar] using hlog.add_const (π * I)

/-- The derivative of the argument along the path, off the corners. -/
lemma hasDerivAt_argStar_comp_ps {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hc : t ∉ hγ.cornerSet) :
    HasDerivAt (fun s => argStar (γ s)) (deriv γ t / γ t).im t := by
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t
    (hγ.hasDerivAt_logStar_comp_ps ht0 ht1 hc)
  simpa [Function.comp_def, logStar_im, Complex.imCLM_apply] using h

/-- Uniform bound on `‖deriv γ‖` off the corners, from compactness of each
closed piece. -/
lemma exists_deriv_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Ioo (0:ℝ) 1, t ∉ hγ.cornerSet → ‖deriv γ t‖ ≤ M := by
  have hb : ∀ i, ∃ B : ℝ, i < hγ.npieces →
      ∀ t ∈ Icc (hγ.cut i) (hγ.cut (i+1)), ‖deriv (hγ.piece i) t‖ ≤ B := by
    intro i
    by_cases hi : i < hγ.npieces
    · have hcont : ContinuousOn (fun t => ‖deriv (hγ.piece i) t‖)
          (Icc (hγ.cut i) (hγ.cut (i+1))) :=
        (hγ.piece_contDiff i hi).continuous_deriv_one.continuousOn.norm
      have hne : (Icc (hγ.cut i) (hγ.cut (i+1))).Nonempty :=
        ⟨hγ.cut i, left_mem_Icc.mpr (hγ.cut_lt_succ i hi).le⟩
      obtain ⟨b, -, hbmax⟩ := isCompact_Icc.exists_isMaxOn hne hcont
      exact ⟨‖deriv (hγ.piece i) b‖, fun _ t ht => hbmax ht⟩
    · exact ⟨0, fun h => (hi h).elim⟩
  choose B hB using hb
  refine ⟨∑ i ∈ Finset.range hγ.npieces, |B i|,
    Finset.sum_nonneg fun j _ => abs_nonneg _, fun t ht hc => ?_⟩
  obtain ⟨i, hi, hti⟩ := hγ.exists_piece_Ioo ht.1 ht.2 hc
  rw [hγ.deriv_eq_piece hi hti]
  refine (hB i hi t ⟨hti.1.le, hti.2.le⟩).trans ?_
  refine (le_abs_self _).trans ?_
  exact Finset.single_le_sum (fun j _ => abs_nonneg (B j)) (Finset.mem_range.mpr hi)

/-- `‖γ‖` is bounded below on `[0,1]` by compactness and nonvanishing. -/
lemma exists_norm_lower :
    ∃ m : ℝ, 0 < m ∧ ∀ t ∈ Icc (0:ℝ) 1, m ≤ ‖γ t‖ := by
  have hne : ∀ t ∈ Icc (0:ℝ) 1, γ t ≠ 0 := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with rfl | h0
    · rw [hγ.start]; simp [Real.pi_ne_zero]
    · exact posSlitPlane_ne_zero (hγ.avoids t h0 ht.2)
  have hcont : ContinuousOn (fun t => ‖γ t‖) (Icc (0:ℝ) 1) := hγ.continuous.norm
  have hnem : (Icc (0:ℝ) 1).Nonempty := ⟨0, left_mem_Icc.mpr zero_le_one⟩
  obtain ⟨b, hbmem, hbmin⟩ := isCompact_Icc.exists_isMinOn hnem hcont
  exact ⟨‖γ b‖, norm_pos_iff.mpr (hne b hbmem), fun t ht => hbmin ht⟩

/-- On each piece with positive left endpoint, `logStar ∘ γ` is continuous. -/
lemma continuousOn_logStar_comp_piece {a b : ℝ} (ha : 0 < a) (hb : b ≤ 1) :
    ContinuousOn (fun s => logStar (γ s)) (Icc a b) := by
  have hg : ContinuousOn logStar posSlitPlane :=
    fun z hz => (hasDerivAt_logStar hz).continuousAt.continuousWithinAt
  have hmaps : MapsTo γ (Icc a b) posSlitPlane :=
    fun t ht => hγ.avoids t (ha.trans_le ht.1) (ht.2.trans hb)
  exact hg.comp (hγ.continuous.mono (Icc_subset_Icc ha.le hb)) hmaps

/-- The logarithmic derivative is integrable along the path: it is measurable
and a.e. bounded on the finite interval. -/
lemma integrable_logDeriv_ps :
    IntervalIntegrable (fun t => deriv γ t / γ t) MeasureTheory.volume 0 1 := by
  obtain ⟨M, hM0, hM⟩ := hγ.exists_deriv_bound
  obtain ⟨m, hm0, hm⟩ := hγ.exists_norm_lower
  have hne : ∀ t ∈ Ioc (0:ℝ) 1, γ t ≠ 0 := by
    intro t ht hz
    have hle := hm t (Ioc_subset_Icc_self ht)
    rw [hz, norm_zero] at hle
    exact absurd hle (not_le.mpr hm0)
  have hcont_inv : ContinuousOn (fun t => (γ t)⁻¹) (Ioc (0:ℝ) 1) :=
    continuousOn_inv₀.comp (hγ.continuous.mono Ioc_subset_Icc_self)
      (fun t ht => Set.mem_compl_singleton_iff.mpr (hne t ht))
  have hinv : MeasureTheory.AEStronglyMeasurable (fun t => (γ t)⁻¹)
      (MeasureTheory.volume.restrict (Ioc (0:ℝ) 1)) :=
    hcont_inv.aestronglyMeasurable measurableSet_Ioc
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun t => deriv γ t / γ t)
      (MeasureTheory.volume.restrict (Ioc (0:ℝ) 1)) :=
    ((measurable_deriv γ).aestronglyMeasurable.mul hinv).congr
      (Filter.Eventually.of_forall fun t => (div_eq_mul_inv _ _).symm)
  have hbd : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Ioc (0:ℝ) 1)),
      ‖deriv γ t / γ t‖ ≤ M / m := by
    filter_upwards [MeasureTheory.ae_restrict_of_ae
        (hγ.cornerSet_countable.ae_notMem MeasureTheory.volume),
      MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with t htc htI
    have ht1 : t < 1 := by
      rcases lt_or_eq_of_le htI.2 with h | h
      · exact h
      · exact absurd ⟨hγ.npieces, Set.mem_Iic.mpr le_rfl, hγ.cut_last.trans h.symm⟩ htc
    rw [norm_div]
    exact div_le_div₀ hM0 (hM t ⟨htI.1, ht1⟩ htc) hm0 (hm t ⟨htI.1.le, htI.2⟩)
  have hint : MeasureTheory.IntegrableOn (fun t => deriv γ t / γ t) (Ioc (0:ℝ) 1) :=
    (MeasureTheory.Integrable.of_bound hmeas (M / m) hbd)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr hint

/-- No partition point lies strictly inside a piece. -/
lemma cut_not_mem_Ioo {i j : ℕ} (hi : i < hγ.npieces) (hj : j ≤ hγ.npieces) :
    hγ.cut j ∉ Ioo (hγ.cut i) (hγ.cut (i+1)) := by
  rintro ⟨h1, h2⟩
  rcases lt_trichotomy j i with hji | rfl | hji
  · have h := hγ.cut_mono (Set.mem_Iic.mpr (hji.le.trans hi.le)) (Set.mem_Iic.mpr hi.le) hji
    linarith
  · exact lt_irrefl _ h1
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hji) with rfl | hji'
    · exact lt_irrefl _ h2
    · have h := hγ.cut_mono (Set.mem_Iic.mpr hi) (Set.mem_Iic.mpr hj) hji'
      linarith

/-- `logStar ∘ γ` is continuous on any piece whose left endpoint is positive. -/
lemma continuousOn_logStar_piece {i : ℕ} (hi : i < hγ.npieces) (h0 : 0 < hγ.cut i) :
    ContinuousOn (fun s => logStar (γ s)) (Icc (hγ.cut i) (hγ.cut (i+1))) :=
  hγ.continuousOn_logStar_comp_piece h0 (hγ.cut_mem_Icc (i+1) hi).2

/-- The imaginary-part integrand is integrable on every piece. -/
lemma pieceIntegrable (k : ℕ) (hk : k < hγ.npieces) :
    IntervalIntegrable (fun t => (deriv γ t / γ t).im)
      MeasureTheory.volume (hγ.cut k) (hγ.cut (k+1)) := by
  have hsub : uIcc (hγ.cut k) (hγ.cut (k+1)) ⊆ uIcc (0:ℝ) 1 :=
    Set.uIcc_subset_uIcc
      (mem_uIcc_of_le (hγ.cut_mem_Icc k hk.le).1 (hγ.cut_mem_Icc k hk.le).2)
      (mem_uIcc_of_le (hγ.cut_mem_Icc (k+1) hk).1 (hγ.cut_mem_Icc (k+1) hk).2)
  have hg := hγ.integrable_logDeriv_ps.mono_set hsub
  exact ⟨Complex.imCLM.integrable_comp hg.1, Complex.imCLM.integrable_comp hg.2⟩

/-- The imaginary-part integral on one interior piece: FTC gives the
telescoping difference of `argStar ∘ γ`. -/
lemma pieceIntegral {i : ℕ} (hi : i < hγ.npieces) (h0 : 0 < hγ.cut i) :
    ∫ t in hγ.cut i..hγ.cut (i+1), (deriv γ t / γ t).im =
      argStar (γ (hγ.cut (i+1))) - argStar (γ (hγ.cut i)) := by
  have hab : hγ.cut i < hγ.cut (i+1) := hγ.cut_lt_succ i hi
  have hcont : ContinuousOn (fun s => argStar (γ s)) (Icc (hγ.cut i) (hγ.cut (i+1))) :=
    continuous_im.comp_continuousOn (hγ.continuousOn_logStar_piece hi h0)
  have hderiv : ∀ t ∈ Ioo (hγ.cut i) (hγ.cut (i+1)),
      HasDerivAt (fun s => argStar (γ s)) (deriv γ t / γ t).im t := by
    intro t ht
    have ht0 : 0 < t := h0.trans_le ht.1.le
    have ht1 : t < 1 := ht.2.trans_le (hγ.cut_mem_Icc (i+1) hi).2
    have hc : t ∉ hγ.cornerSet := by
      rintro ⟨j, hj, rfl⟩
      exact hγ.cut_not_mem_Ioo hi hj ht
    exact hγ.hasDerivAt_argStar_comp_ps ht0 ht1 hc
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le hcont hderiv
    (hγ.pieceIntegrable i hi)

/-- The path tends to its prescribed initial value from the right. -/
lemma tendsto_gamma_nhdsGT_zero_ps :
    Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝 (Real.pi : ℂ)) := by
  rw [← hγ.start]
  exact (hγ.continuous.continuousWithinAt
    (show (0 : ℝ) ∈ Icc 0 1 by norm_num)).mono_left
      (nhdsWithin_le_iff.mpr (Icc_mem_nhdsGT zero_lt_one))

/-- Near its initial point, the piecewise-smooth path stays entirely in one of
the two half-planes, so `argStar ∘ γ` tends to the corresponding edge value.
(Analogue of `tendsto_argStar_nhdsGT_zero_or_two_pi` for `SlitPath`.) -/
lemma tendsto_argStar_nhdsGT_zero_or_two_pi_ps :
    Tendsto (fun t => argStar (γ t)) (𝓝[>] (0 : ℝ)) (𝓝 0) ∨
      Tendsto (fun t => argStar (γ t)) (𝓝[>] (0 : ℝ)) (𝓝 (2 * π)) := by
  have hγ0 := hγ.tendsto_gamma_nhdsGT_zero_ps
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

/-- The imaginary-part integral on the first piece: the right-hand limit at
`0` of `argStar ∘ γ` replaces the endpoint value. -/
lemma pieceZeroIntegral {L : ℝ}
    (hlim : Tendsto (fun t => argStar (γ t)) (𝓝[>] (0:ℝ)) (𝓝 L)) :
    ∫ t in hγ.cut 0..hγ.cut 1, (deriv γ t / γ t).im =
      argStar (γ (hγ.cut 1)) - L := by
  have h1pos : (0:ℝ) < hγ.cut 1 := by
    have h := hγ.cut_lt_succ 0 hγ.npieces_pos
    rwa [hγ.cut_zero] at h
  have h1mem : hγ.cut 1 ∈ Icc (0:ℝ) 1 := hγ.cut_mem_Icc 1 hγ.npieces_pos
  have hcont1 : ContinuousAt logStar (γ (hγ.cut 1)) :=
    (hasDerivAt_logStar (hγ.avoids _ h1pos h1mem.2)).continuousAt
  have hγ1 : Tendsto γ (𝓝[<] hγ.cut 1) (𝓝 (γ (hγ.cut 1))) :=
    ((hγ.continuous.mono (Icc_subset_Icc_right h1mem.2)).continuousWithinAt
      (right_mem_Icc.mpr h1pos.le)).mono_left
      (nhdsWithin_le_iff.mpr (Icc_mem_nhdsLT h1pos))
  have hb : Tendsto (fun s => argStar (γ s)) (𝓝[<] hγ.cut 1)
      (𝓝 (argStar (γ (hγ.cut 1)))) :=
    (continuous_im.continuousAt.comp hcont1).tendsto.comp hγ1
  have hderiv : ∀ t ∈ Ioo (hγ.cut 0) (hγ.cut 1),
      HasDerivAt (fun s => argStar (γ s)) (deriv γ t / γ t).im t := by
    intro t ht
    rw [hγ.cut_zero] at ht
    have ht1 : t < 1 := ht.2.trans_le h1mem.2
    have hc : t ∉ hγ.cornerSet := by
      rintro ⟨j, hj, rfl⟩
      rw [← hγ.cut_zero] at ht
      exact hγ.cut_not_mem_Ioo hγ.npieces_pos hj ht
    exact hγ.hasDerivAt_argStar_comp_ps ht.1 ht1 hc
  rw [hγ.cut_zero] at hderiv ⊢
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    h1pos hderiv (by rw [← hγ.cut_zero]; exact hγ.pieceIntegrable 0 hγ.npieces_pos) hlim hb

/-- The full imaginary-part integral is `argStar(γ 1)` minus the initial
one-sided limit of `argStar ∘ γ`. -/
lemma intervalIntegral_im_eq_ps {L : ℝ}
    (hlim : Tendsto (fun t => argStar (γ t)) (𝓝[>] (0:ℝ)) (𝓝 L)) :
    ∫ t in (0:ℝ)..1, (deriv γ t / γ t).im = argStar (γ 1) - L := by
  obtain ⟨m, hm⟩ : ∃ m, hγ.npieces = m + 1 :=
    ⟨hγ.npieces - 1, (Nat.succ_pred_eq_of_pos hγ.npieces_pos).symm⟩
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (μ := MeasureTheory.volume) (f := fun t => (deriv γ t / γ t).im)
    (a := hγ.cut) (n := hγ.npieces) (fun k hk => hγ.pieceIntegrable k hk)
  rw [hγ.cut_zero, hγ.cut_last] at hsum
  rw [← hsum, hm, Finset.sum_range_succ', hγ.pieceZeroIntegral hlim]
  have hrest : ∑ k ∈ Finset.range m,
      (∫ t in hγ.cut (k+1)..hγ.cut (k+1+1), (deriv γ t / γ t).im) =
        argStar (γ (hγ.cut (m+1))) - argStar (γ (hγ.cut 1)) := by
    have hcongr : ∀ k ∈ Finset.range m,
        (∫ t in hγ.cut (k+1)..hγ.cut (k+1+1), (deriv γ t / γ t).im) =
          (fun j => argStar (γ (hγ.cut (j+1)))) (k+1) -
            (fun j => argStar (γ (hγ.cut (j+1)))) k := by
      intro k hk
      have hkm := Finset.mem_range.mp hk
      have hk1 : k + 1 < hγ.npieces := by omega
      have h0k : 0 < hγ.cut (k+1) := by
        have h := hγ.cut_mono (Set.mem_Iic.mpr (Nat.zero_le _))
          (Set.mem_Iic.mpr hk1.le) (Nat.succ_pos k)
        rwa [hγ.cut_zero] at h
      simpa using hγ.pieceIntegral hk1 h0k
    rw [Finset.sum_congr rfl hcongr]
    exact Finset.sum_range_sub (fun j => argStar (γ (hγ.cut (j+1)))) m
  rw [hrest]
  have hfin : hγ.cut (m+1) = 1 := by rw [← hm]; exact hγ.cut_last
  rw [hfin]
  ring

/-- The piecewise-smooth analogue of `logIntegral_im_eq_argStar_diff`. -/
lemma logIntegral_im_eq_argStar_diff_ps :
    (∫ t in (0:ℝ)..1, deriv γ t / γ t).im =
      argStar (γ 1) - limUnder (𝓝[>] 0) (fun t => argStar (γ t)) := by
  have him : (∫ t in (0:ℝ)..1, (deriv γ t / γ t).im) =
      (∫ t in (0:ℝ)..1, deriv γ t / γ t).im := by
    simpa [Complex.imCLM_apply] using
      Complex.imCLM.intervalIntegral_comp_comm hγ.integrable_logDeriv_ps
  rcases hγ.tendsto_argStar_nhdsGT_zero_or_two_pi_ps with hzero | htwo
  · rw [hzero.limUnder_eq, ← him]
    exact hγ.intervalIntegral_im_eq_ps hzero
  · rw [htwo.limUnder_eq, ← him]
    exact hγ.intervalIntegral_im_eq_ps htwo

end PiecewiseSmoothSlitPath

/-- Main theorem for piecewise-smooth paths, phrased with the new structure. -/
lemma logIntegral_im_bounds_ps {γ : ℝ → ℂ} (hγ : PiecewiseSmoothSlitPath γ) :
    0 < |(∫ t in (0:ℝ)..1, deriv γ t / γ t).im| ∧
      |(∫ t in (0:ℝ)..1, deriv γ t / γ t).im| < 2 * π := by
  have hEq := hγ.logIntegral_im_eq_argStar_diff_ps
  have hpos := argStar_pos (hγ.avoids 1 zero_lt_one le_rfl)
  have hlt := argStar_lt_two_pi (hγ.avoids 1 zero_lt_one le_rfl)
  rcases hγ.tendsto_argStar_nhdsGT_zero_or_two_pi_ps with hzero | htwo
  · rw [hzero.limUnder_eq] at hEq
    have him : (∫ t in (0:ℝ)..1, deriv γ t / γ t).im = argStar (γ 1) := by
      simpa using hEq
    rw [him, abs_of_pos hpos]
    exact ⟨hpos, hlt⟩
  · rw [htwo.limUnder_eq] at hEq
    have him_neg : (∫ t in (0:ℝ)..1, deriv γ t / γ t).im < 0 := by
      rw [hEq]
      linarith
    rw [abs_of_neg him_neg, hEq]
    constructor <;> linarith

end ApmCanaries.A02J07

open ApmCanaries.A02J07 in
/-- **APM a02J07 (original statement).** Let `γ : [0,1] → ℂ` be a piecewise
smooth path with `γ(0) = π` and `γ⁻¹([0,∞)) = {0}`.  Then
`0 < |Im ∫_γ dz/z| < 2π`, where the contour integral is the genuine interval
integral of the logarithmic derivative (proved integrable along the way). -/
theorem apm_a02j07 {γ : ℝ → ℂ} (hγ : ApmCanaries.A02J07.PiecewiseSmoothSlitPath γ) :
    0 < |(∫ t in (0:ℝ)..1, deriv γ t / γ t).im| ∧
      |(∫ t in (0:ℝ)..1, deriv γ t / γ t).im| < 2 * π :=
  ApmCanaries.A02J07.logIntegral_im_bounds_ps hγ
