/-
! # APM a97J03: Convolution of L^p and L^q functions lies in C₀

Let 1 < p, q < ∞ with 1/p + 1/q = 1, f ∈ L^p(ℝ), g ∈ L^q(ℝ).
Define h(y) = ∫ f(y-x)g(x)dm(x). Prove h is continuous and
lim_{y→±∞} h(y) = 0.

## Strategy (from informal-solution.md)

1. Hölder's inequality gives |h(y)| ≤ ‖f‖_p · ‖g‖_q (uniform bound).
2. Continuity: |h(y) - h(y')| ≤ ‖τ_{y-y'}f̌ - f̌‖_p · ‖g‖_q → 0 by L^p continuity of translation.
3. Vanishing at infinity: approximate f, g by C_c functions; their convolution has compact support;
   the Hölder bound controls the approximation error uniformly.

## Phase-A hints used
-- (Memory: e-codexpilot-prove-Holder-convolution-vanishes-at-infinity-by-compact-support-density)
--    Prior attempt at same problem; strategy name confirms: Hölder bound + C_c density.
-- (Memory: math-informal/monotone-approximation) C_c density in L^p underlies the approximation.

## Completed route

The analytic bridges are discharged by reusing the compiled neighboring proof
from `problems/a03J03/lean/Main.lean`:

1. **Continuity**: package translations as `Lp.compMeasurePreserving` and pair
   them with g through `ContinuousLinearMap.lpPairing`.
   -- (Memory: e-codexpilot-prove-Holder-convolution-vanishes-at-infinity-by-compact-support-density)
   --    confirms this is the first step.

2. **Vanishing**: approximate both Lp representatives by continuous compactly
   supported functions, use compact support of their convolution, and control
   both approximation errors uniformly with `lpPairing`.
   -- (Memory: e-j02-translation-symmdiff-preimage-api) provides symmetric-difference API for this.

3. The resulting cocompact limit restricts to both `atTop` and `atBot` via
   `atTop_le_cocompact` and `atBot_le_cocompact`.

This uses Mathlib's convolution only for the compact-support core and retains
the problem's frozen pointwise integral definition.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique

open MeasureTheory Filter Set Topology
open scoped ENNReal Convolution

noncomputable section

namespace APMa97J03

/-- The convolution h(y) = ∫ f(y-x)g(x)dm(x).
    This matches the problem statement's definition. -/
def conv (f : ℝ → ℝ) (g : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ x, f (y - x) * g x ∂volume

-- Reused from the compiled neighboring bundle `problems/a03J03/lean/Main.lean`.
-- It packages translation continuity through `Lp.compMeasurePreserving`.
theorem convolution_continuous {p q : ℝ} (hpq : p.HolderConjugate q)
    {f : ℝ → ℝ} {g : ℝ → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) volume)
    (hg : MemLp g (ENNReal.ofReal q) volume) :
    Continuous (fun x => ∫ y, f (x - y) * g y) := by
  let P := ENNReal.ofReal p
  let Q := ENNReal.ofReal q
  letI : P.HolderConjugate Q := hpq.ennrealOfReal
  letI : Fact (1 ≤ P) := ⟨ENNReal.HolderConjugate.one_le P Q⟩
  letI : Fact (1 ≤ Q) := ⟨ENNReal.HolderConjugate.one_le Q P⟩
  have hPtop : P ≠ ⊤ := by simp [P]
  let τ : ℝ → C(ℝ, ℝ) :=
    fun x => ⟨fun y => x - y, continuous_const.sub continuous_id⟩
  have hτ : Continuous τ := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : ℝ × ℝ => z.1 - z.2)
    fun_prop
  have hτmp : ∀ x, MeasurePreserving (τ x) volume volume :=
    fun x => (volume : Measure ℝ).measurePreserving_sub_left x
  let F : Lp ℝ P (volume : Measure ℝ) := hf.toLp f
  let G : Lp ℝ Q (volume : Measure ℝ) := hg.toLp g
  have htrans : Continuous (fun x => Lp.compMeasurePreserving (τ x) (hτmp x) F) :=
    continuous_const.compMeasurePreservingLp hτ hτmp hPtop
  let pairing : Lp ℝ P (volume : Measure ℝ) →L[ℝ]
      Lp ℝ Q (volume : Measure ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.mul ℝ ℝ).lpPairing (volume : Measure ℝ) P Q
  have hpair :
      Continuous (fun x => pairing (Lp.compMeasurePreserving (τ x) (hτmp x) F) G) := by
    fun_prop
  apply hpair.congr
  intro x
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_compMeasurePreserving F (hτmp x),
    (hτmp x).quasiMeasurePreserving.ae_eq_comp (MemLp.coeFn_toLp hf),
    MemLp.coeFn_toLp hg] with y hτy hfy hgy
  simp only [τ, ContinuousMap.coe_mk, Function.comp_apply] at hτy hfy
  simp only [τ, ContinuousMap.coe_mk] at ⊢
  rw [hτy, hfy, hgy]
  rfl

-- Part 2: f*g vanishes at infinity
-- Approximate f by φ ∈ C_c, then φ*g is localized, g ∈ Lq means sliding window → 0
theorem convolution_tendsto_zero {p q : ℝ} (hpq : p.HolderConjugate q)
    {f : ℝ → ℝ} {g : ℝ → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) volume)
    (hg : MemLp g (ENNReal.ofReal q) volume) :
    Tendsto (fun x => ∫ y, f (x - y) * g y) (cocompact ℝ) (nhds 0) := by
  let P := ENNReal.ofReal p
  let Q := ENNReal.ofReal q
  letI : P.HolderConjugate Q := hpq.ennrealOfReal
  letI : Fact (1 ≤ P) := ⟨ENNReal.HolderConjugate.one_le P Q⟩
  letI : Fact (1 ≤ Q) := ⟨ENNReal.HolderConjugate.one_le Q P⟩
  have hPtop : P ≠ ⊤ := by simp [P]
  have hQtop : Q ≠ ⊤ := by simp [Q]
  let τ : ℝ → C(ℝ, ℝ) :=
    fun x => ⟨fun y => x - y, continuous_const.sub continuous_id⟩
  have hτmp : ∀ x, MeasurePreserving (τ x) volume volume :=
    fun x => (volume : Measure ℝ).measurePreserving_sub_left x
  let pairing : Lp ℝ P (volume : Measure ℝ) →L[ℝ]
      Lp ℝ Q (volume : Measure ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.mul ℝ ℝ).lpPairing (volume : Measure ℝ) P Q
  let F : Lp ℝ P (volume : Measure ℝ) := hf.toLp f
  let G : Lp ℝ Q (volume : Measure ℝ) := hg.toLp g
  have pair_translate_eq {a b : ℝ → ℝ}
      (ha : MemLp a P volume) (hb : MemLp b Q volume) (x : ℝ) :
      pairing (Lp.compMeasurePreserving (τ x) (hτmp x) (ha.toLp a)) (hb.toLp b) =
        ∫ y, a (x - y) * b y := by
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_compMeasurePreserving (ha.toLp a) (hτmp x),
      (hτmp x).quasiMeasurePreserving.ae_eq_comp (MemLp.coeFn_toLp ha),
      MemLp.coeFn_toLp hb] with y hτy hay hby
    simp only [τ, ContinuousMap.coe_mk, Function.comp_apply] at hτy hay
    simp only [τ, ContinuousMap.coe_mk] at ⊢
    rw [hτy, hay, hby]
    rfl
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δf := ε / (4 * (‖pairing‖ + 1) * (‖G‖ + 1))
  have hδf : 0 < δf := by
    dsimp [δf]
    positivity
  obtain ⟨φ, hφc, hφerr, hφcont, hφmem⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le hPtop
      (ENNReal.ofReal_ne_zero_iff.mpr hδf)
  let Φ : Lp ℝ P (volume : Measure ℝ) := hφmem.toLp φ
  have hFΦ : ‖F - Φ‖ ≤ δf := by
    change ‖hf.toLp f - hφmem.toLp φ‖ ≤ δf
    rw [← hf.toLp_sub hφmem, Lp.norm_toLp]
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hφerr
    simpa [ENNReal.toReal_ofReal hδf.le] using h
  let δg := ε / (4 * (‖pairing‖ + 1) * (‖Φ‖ + 1))
  have hδg : 0 < δg := by
    dsimp [δg]
    positivity
  obtain ⟨ψ, hψc, hψerr, hψcont, hψmem⟩ :=
    hg.exists_hasCompactSupport_eLpNorm_sub_le hQtop
      (ENNReal.ofReal_ne_zero_iff.mpr hδg)
  let Ψ : Lp ℝ Q (volume : Measure ℝ) := hψmem.toLp ψ
  have hGΨ : ‖G - Ψ‖ ≤ δg := by
    change ‖hg.toLp g - hψmem.toLp ψ‖ ≤ δg
    rw [← hg.toLp_sub hψmem, Lp.norm_toLp]
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hψerr
    simpa [ENNReal.toReal_ofReal hδg.le] using h
  let core : ℝ → ℝ :=
    fun x => pairing (Lp.compMeasurePreserving (τ x) (hτmp x) Φ) Ψ
  have hcore_eq :
      core = convolution φ ψ (ContinuousLinearMap.mul ℝ ℝ) (volume : Measure ℝ) := by
    funext x
    rw [convolution_eq_swap]
    exact pair_translate_eq hφmem hψmem x
  have hcorec : HasCompactSupport core := by
    rw [hcore_eq]
    exact hφc.convolution (ContinuousLinearMap.mul ℝ ℝ) hψc
  have hcorezero : core =ᶠ[cocompact ℝ] 0 := by
    rw [← Filter.coclosedCompact_eq_cocompact,
      ← hasCompactSupport_iff_eventuallyEq]
    exact hcorec
  filter_upwards [hcorezero] with x hx
  have hx' : core x = 0 := by simpa using hx
  rw [dist_zero_right]
  rw [← pair_translate_eq hf hg x]
  have hid :
      pairing (Lp.compMeasurePreserving (τ x) (hτmp x) F) G - core x =
        pairing (Lp.compMeasurePreserving (τ x) (hτmp x) (F - Φ)) G +
          pairing (Lp.compMeasurePreserving (τ x) (hτmp x) Φ) (G - Ψ) := by
    simp [core, map_sub]
  calc
    ‖pairing (Lp.compMeasurePreserving (τ x) (hτmp x) F) G‖ =
        ‖pairing (Lp.compMeasurePreserving (τ x) (hτmp x) F) G - core x‖ := by
      rw [hx', sub_zero]
    _ = ‖pairing (Lp.compMeasurePreserving (τ x) (hτmp x) (F - Φ)) G +
          pairing (Lp.compMeasurePreserving (τ x) (hτmp x) Φ) (G - Ψ)‖ := by
      rw [hid]
    _ ≤ ‖pairing (Lp.compMeasurePreserving (τ x) (hτmp x) (F - Φ)) G‖ +
          ‖pairing (Lp.compMeasurePreserving (τ x) (hτmp x) Φ) (G - Ψ)‖ :=
      norm_add_le _ _
    _ ≤ ‖pairing‖ * ‖F - Φ‖ * ‖G‖ + ‖pairing‖ * ‖Φ‖ * ‖G - Ψ‖ := by
      apply add_le_add
      · simpa only [Lp.norm_compMeasurePreserving] using
          ContinuousLinearMap.le_opNorm₂ pairing
            (Lp.compMeasurePreserving (τ x) (hτmp x) (F - Φ)) G
      · simpa only [Lp.norm_compMeasurePreserving] using
          ContinuousLinearMap.le_opNorm₂ pairing
            (Lp.compMeasurePreserving (τ x) (hτmp x) Φ) (G - Ψ)
    _ ≤ ‖pairing‖ * δf * ‖G‖ + ‖pairing‖ * ‖Φ‖ * δg := by
      gcongr
    _ < ε := by
      dsimp [δf, δg]
      have hp0 : 0 ≤ ‖pairing‖ := norm_nonneg pairing
      have hG0 : 0 ≤ ‖G‖ := norm_nonneg G
      have hΦ0 : 0 ≤ ‖Φ‖ := norm_nonneg Φ
      have hden1 : 0 < 4 * (‖pairing‖ + 1) * (‖G‖ + 1) := by positivity
      have hden2 : 0 < 4 * (‖pairing‖ + 1) * (‖Φ‖ + 1) := by positivity
      have hterm1 :
          ‖pairing‖ * (ε / (4 * (‖pairing‖ + 1) * (‖G‖ + 1))) * ‖G‖ ≤
            ε / 4 := by
        field_simp
        nlinarith
      have hterm2 :
          ‖pairing‖ * ‖Φ‖ *
              (ε / (4 * (‖pairing‖ + 1) * (‖Φ‖ + 1))) ≤ ε / 4 := by
        field_simp
        nlinarith
      calc
        ‖pairing‖ * (ε / (4 * (‖pairing‖ + 1) * (‖G‖ + 1))) * ‖G‖ +
            ‖pairing‖ * ‖Φ‖ *
              (ε / (4 * (‖pairing‖ + 1) * (‖Φ‖ + 1))) ≤ ε / 2 := by
          linarith
        _ < ε := by linarith

/-- Main theorem: for f ∈ L^p, g ∈ L^q with 1/p + 1/q = 1 (1 < p,q < ∞),
    h = f * g is continuous and vanishes at infinity.

    -- (Memory: e-codexpilot-prove-Holder-convolution-vanishes-at-infinity-by-compact-support-density)
    --    Strategy: Hölder bound + L^p translation continuity + C_c density for vanishing at infinity.
    -- (Memory: math-informal/monotone-approximation) C_c density approximates L^p functions. -/
theorem convolution_continuous_vanishes
    (p q : ℝ) (hp : 1 < p) (hq : 1 < q) (hpq : 1/p + 1/q = 1)
    (f : ℝ → ℝ) (g : ℝ → ℝ)
    (hf : MemLp f (ENNReal.ofReal p) volume)
    (hg : MemLp g (ENNReal.ofReal q) volume) :
    Continuous (conv f g) ∧
    Tendsto (conv f g) atTop (𝓝 0) ∧
    Tendsto (conv f g) atBot (𝓝 0) := by
  have hpq' : p.HolderConjugate q := by
    rw [Real.holderConjugate_iff]
    refine ⟨hp, ?_⟩
    simpa only [one_div] using hpq
  have hc : Continuous (conv f g) := by
    simpa only [conv] using convolution_continuous hpq' hf hg
  have hv : Tendsto (conv f g) (cocompact ℝ) (𝓝 0) := by
    simpa only [conv] using convolution_tendsto_zero hpq' hf hg
  exact ⟨hc, hv.mono_left atTop_le_cocompact, hv.mono_left atBot_le_cocompact⟩

#print axioms APMa97J03.convolution_continuous_vanishes

end APMa97J03
