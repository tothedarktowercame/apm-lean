import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# APM a01A02: Weak L² bound implies L¹ bound on sets

**Problem.** Let `f : ℝⁿ → ℝ` be Lebesgue measurable with
`m{|x : |f(x)| > λ} ≤ C λ⁻²` for some constant `C > 0`. Prove that there
exists a constant `C₁` such that for any Borel set `E ⊂ ℝⁿ` with
`0 < m(E) < ∞`, we have `∫_E |f(x)| dx ≤ C₁ √(m(E))`.

**Statement repair note.**

The informal-solution file `apm-a01A02.md` was harvested with the **wrong
content**: it contains the proof for a01A01 (typewriter sequence), not a01A02
(weak-type estimate). The proposed Lean statements are for the typewriter
problem. This file implements the correct problem from `a01A02.tex`.

**Proof.**

By the layer cake formula (Cavalieri's principle):
`∫_E |f| dm = ∫_0^∞ m(E ∩ {|f| > t}) dt`.

Using `m(E ∩ {|f| > t}) ≤ min(m(E), C/t²)`, split the integral at
`t₀ = √(C/m(E))`:

- `∫_0^{t₀} m(E) dt = m(E) · t₀ = m(E) · √(C/m(E)) = √(C·m(E))`
- `∫_{t₀}^∞ C/t² dt = C/t₀ = C · √(m(E)/C) = √(C·m(E))`

Total: `2√(C·m(E))`. So `C₁ = 2√C` suffices.

**Formalization status.**

The theorem statement is correct and captures the mathematical problem
faithfully. The proof requires the layer cake formula
(`Integrable.integral_eq_integral_meas_lt`) applied to `|f|` restricted to
`E`, combined with a careful integral splitting argument. The main
formalization challenges are:
1. Establishing integrability of `|f| · 𝟙_E` (needed for the Bochner integral
   version of layer cake, or working with `∫⁻` and ENNReal).
2. Managing the ENNReal/Real conversions in the tail-measure bound.
3. Computing the split integral `∫_0^{t₀} min(m(E), C/t²) dt` with explicit
   bound `2√(C·m(E))`.
-/

set_option linter.unusedVariables false in
noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal

namespace ApmCanaries.A01A02

variable {α : Type*} [MeasureSpace α]

/-- **Main theorem.** If `f` satisfies the weak-`L²` bound
    `m{|x : |f(x)| > t} ≤ C / t²` for all `t > 0`, then for every measurable
    set `E` with finite positive measure, `∫_E |f| dm ≤ C₁ √(m(E))`.

    The constant `C₁ = 2 √C` works, by the layer cake argument.

    **SORRY BOUNDARY:** The proof requires applying the layer cake formula
    (`Integrable.integral_eq_integral_meas_lt`) to `|f|` restricted to `E`,
    then splitting the resulting integral at `t₀ = √(C/m(E))` and bounding
    each piece. The main difficulties:
    (1) Establishing that `|f| · 𝟙_E` is integrable (to apply the Bochner
        layer cake) — this follows from the weak bound but requires proof.
    (2) Managing ENNReal/Real conversions in the tail-measure bound
        `m(E ∩ {|f| > t}) ≤ min(m(E), C/t²)`.
    (3) Computing `∫_0^{t₀} m(E) dt + ∫_{t₀}^∞ C/t² dt = 2√(C·m(E))`.
    Each piece is mathematically standard but requires careful formalization
    of the measure-theoretic hypotheses and the integral estimates.
-/
-- STATEMENT REPAIR 2026-07-30 (Joe-authorised). See faithfulness-ledger #4.
-- The weak-L² hypothesis was written with `.toReal` and no finiteness
-- side-condition. Mathlib defines `ENNReal.toReal ⊤ = 0`, so a function whose
-- superlevel sets have INFINITE measure satisfied it VACUOUSLY — machine-checked
-- refutation at α = ℝ, f ≡ 1, C = 1, applied to Icc 0 (C₁²+1). The informal
-- solution states the hypothesis as the MEASURE bound `m({|f| > λ}) ≤ C λ⁻²`
-- (line 15), so this is a translation defect, not a mathematical one. Restated
-- in `ENNReal`, where `⊤ ≤ ofReal (C/t²)` is false rather than vacuously true,
-- which is exactly the intended content.
theorem weakL2_implies_L1_bound
    (f : α → ℝ) (hf_meas : Measurable f) (C : ℝ) (hC : 0 < C)
    (hweak : ∀ t : ℝ, 0 < t →
      volume {x : α | t < |f x|} ≤ ENNReal.ofReal (C / t ^ 2)) :
    ∃ C₁ : ℝ, ∀ (E : Set α), MeasurableSet E →
      0 < (volume E).toReal → (volume E) < ⊤ →
      ∫ x in E, |f x| ≤ C₁ * Real.sqrt (volume E).toReal := by
  refine ⟨2 * Real.sqrt C, ?_⟩
  intro E hE hm hE_top
  let m : ℝ := (volume E).toReal
  let a : ℝ := Real.sqrt C / Real.sqrt m
  have hm' : 0 < m := hm
  have hsqrtC : 0 < Real.sqrt C := Real.sqrt_pos.2 hC
  have hsqrtm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm'
  have ha : 0 < a := div_pos hsqrtC hsqrtm
  have hmeasureE : volume E = ENNReal.ofReal m := by
    exact (ENNReal.ofReal_toReal hE_top.ne).symm

  have hlayer :
      (∫⁻ x in E, ENNReal.ofReal |f x|) =
        ∫⁻ t in Ioi (0 : ℝ),
          (volume.restrict E) {x : α | t < |f x|} := by
    exact MeasureTheory.lintegral_eq_lintegral_meas_lt
      (volume.restrict E) (Eventually.of_forall fun _ => abs_nonneg _)
      (by simpa only [Real.norm_eq_abs] using hf_meas.norm.aemeasurable)

  have htail_low (t : ℝ) :
      (volume.restrict E) {x : α | t < |f x|} ≤ ENNReal.ofReal m := by
    calc
      (volume.restrict E) {x : α | t < |f x|}
          ≤ (volume.restrict E) univ := measure_mono (subset_univ _)
      _ = volume E := Measure.restrict_apply_univ E
      _ = ENNReal.ofReal m := hmeasureE

  have htail_high (t : ℝ) (ht : 0 < t) :
      (volume.restrict E) {x : α | t < |f x|}
        ≤ ENNReal.ofReal (C / t ^ 2) := by
    exact (Measure.restrict_le_self {x : α | t < |f x|}).trans (hweak t ht)

  have hlow :
      (∫⁻ t in Ioc (0 : ℝ) a,
          (volume.restrict E) {x : α | t < |f x|})
        ≤ ENNReal.ofReal (m * a) := by
    calc
      (∫⁻ t in Ioc (0 : ℝ) a,
          (volume.restrict E) {x : α | t < |f x|})
          ≤ ∫⁻ _t in Ioc (0 : ℝ) a, ENNReal.ofReal m :=
            setLIntegral_mono' measurableSet_Ioc fun t _ => htail_low t
      _ = ENNReal.ofReal (m * a) := by
        rw [setLIntegral_const]
        simp [Real.volume_Ioc, ENNReal.ofReal_mul hm'.le]

  have hhigh_integrable :
      IntegrableOn (fun t : ℝ => C / t ^ 2) (Ioi a) volume := by
    have hrpow :=
      (integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) ha).const_mul C
    apply hrpow.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hp : t ^ (-2 : ℝ) = (t ^ 2)⁻¹ := by
      rw [Real.rpow_neg_ofNat]
      norm_num [zpow_neg]
      rfl
    rw [hp, div_eq_mul_inv]

  have hhigh_eval :
      ∫ t : ℝ in Ioi a, C / t ^ 2 = C / a := by
    calc
      (∫ t : ℝ in Ioi a, C / t ^ 2) =
          ∫ t : ℝ in Ioi a, C * t ^ (-2 : ℝ) := by
            apply integral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            have hp : t ^ (-2 : ℝ) = (t ^ 2)⁻¹ := by
              rw [Real.rpow_neg_ofNat]
              norm_num [zpow_neg]
              rfl
            rw [hp, div_eq_mul_inv]
      _ = C * ∫ t : ℝ in Ioi a, t ^ (-2 : ℝ) := by
        rw [integral_const_mul]
      _ = C / a := by
        rw [integral_Ioi_rpow_of_lt (by norm_num) ha]
        norm_num [Real.rpow_neg_one, div_eq_mul_inv]

  have hhigh :
      (∫⁻ t in Ioi a,
          (volume.restrict E) {x : α | t < |f x|})
        ≤ ENNReal.ofReal (C / a) := by
    calc
      (∫⁻ t in Ioi a,
          (volume.restrict E) {x : α | t < |f x|})
          ≤ ∫⁻ t in Ioi a, ENNReal.ofReal (C / t ^ 2) :=
            setLIntegral_mono' measurableSet_Ioi fun t ht =>
              htail_high t (ha.trans ht)
      _ = ENNReal.ofReal (∫ t : ℝ in Ioi a, C / t ^ 2) := by
        exact
          (ofReal_integral_eq_lintegral_ofReal hhigh_integrable
            (by
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
              positivity)).symm
      _ = ENNReal.ofReal (C / a) := congrArg ENNReal.ofReal hhigh_eval

  have hdisjoint : Disjoint (Ioc (0 : ℝ) a) (Ioi a) := by
    rw [Set.disjoint_left]
    intro t ht₁ ht₂
    exact (not_lt_of_ge ht₁.2) ht₂

  have hsplit :
      (∫⁻ t in Ioi (0 : ℝ),
          (volume.restrict E) {x : α | t < |f x|}) =
        (∫⁻ t in Ioc (0 : ℝ) a,
          (volume.restrict E) {x : α | t < |f x|}) +
        ∫⁻ t in Ioi a,
          (volume.restrict E) {x : α | t < |f x|} := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi ha.le]
    exact lintegral_union measurableSet_Ioi hdisjoint

  have hopt :
      m * a + C / a = 2 * Real.sqrt C * Real.sqrt m := by
    dsimp [a]
    have hsqrtC_sq : (Real.sqrt C) ^ 2 = C := Real.sq_sqrt hC.le
    have hsqrtm_sq : (Real.sqrt m) ^ 2 = m := Real.sq_sqrt hm'.le
    field_simp
    nlinarith

  have hlintegral :
      (∫⁻ x in E, ENNReal.ofReal |f x|)
        ≤ ENNReal.ofReal (2 * Real.sqrt C * Real.sqrt m) := by
    rw [hlayer, hsplit]
    calc
      (∫⁻ t in Ioc (0 : ℝ) a,
          (volume.restrict E) {x : α | t < |f x|}) +
          (∫⁻ t in Ioi a,
            (volume.restrict E) {x : α | t < |f x|})
          ≤ ENNReal.ofReal (m * a) + ENNReal.ofReal (C / a) :=
            add_le_add hlow hhigh
      _ = ENNReal.ofReal (m * a + C / a) := by
        rw [ENNReal.ofReal_add (mul_nonneg hm'.le ha.le)
          (div_nonneg hC.le ha.le)]
      _ = ENNReal.ofReal (2 * Real.sqrt C * Real.sqrt m) := by rw [hopt]

  have hintegral :=
    norm_integral_le_lintegral_norm
      (μ := volume.restrict E) (fun x : α => |f x|)
  have hintegral' :
      ‖∫ x in E, |f x|‖ ≤
        (∫⁻ x in E, ENNReal.ofReal |f x|).toReal := by
    simpa only [Real.norm_eq_abs, abs_abs] using hintegral
  have hle_norm :
      (∫ x in E, |f x|) ≤ ‖∫ x in E, |f x|‖ := by
    rw [Real.norm_eq_abs]
    exact le_abs_self _
  calc
    (∫ x in E, |f x|) ≤ ‖∫ x in E, |f x|‖ := hle_norm
    _ ≤ (∫⁻ x in E, ENNReal.ofReal |f x|).toReal := hintegral'
    _ ≤ (ENNReal.ofReal (2 * Real.sqrt C * Real.sqrt m)).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hlintegral
    _ = 2 * Real.sqrt C * Real.sqrt m := by
      rw [ENNReal.toReal_ofReal]
      positivity

end ApmCanaries.A01A02
