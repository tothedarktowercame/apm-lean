/-
! # APM a97J01: Bounded integrals over bounded pieces force global integrability

Let f: ℝ → ℝ be Lebesgue measurable. Assume ∃ c > 0 such that for every
bounded measurable set A on which f is bounded, |∫_A f dm| ≤ c.
Prove that f ∈ L¹(ℝ), i.e. ∫_ℝ |f| dm ≤ 2c.

## Note on the statement

The problem.tex says "Prove that f is Lebesgue measurable", but f is already
assumed measurable — this is circular. The intended conclusion (standard for
this UT-Austin prelim) is that f is Lebesgue **integrable**, with the bound
∫|f| ≤ 2c. We prove exactly that.

## Strategy (from informal-solution.md)

1. Split f = f⁺ - f⁻ where f⁺ = max(f,0), f⁻ = max(-f,0).
2. For each n, define A_n = {|x| ≤ n, 0 ≤ f ≤ n}. Apply hypothesis: ∫_{A_n} f ≤ c.
   Since f ≥ 0 on A_n, ∫_{A_n} f⁺ ≤ c.
3. A_n ↑ {f ≥ 0}, so by MCT, ∫ f⁺ = lim ∫_{A_n} f⁺ ≤ c.
4. Symmetrically ∫ f⁻ ≤ c.
5. ∫|f| = ∫f⁺ + ∫f⁻ ≤ 2c.

## Phase-A hints used
-- (Memory: math-informal/monotone-approximation) MCT is the core passage from per-n bounds to the limit.
-- (Memory: math-informal/exhaustion-as-theorem) the A_n, B_n exhaustion is the structural technique.

## Phase-A hints dropped
- #3 (finite interval measure): not needed; we use ENNReal-level arguments.

## Completed MCT bridge

The truncated sets A_n, B_n are defined, the hypothesis is applied to each,
and the per-n integral bounds are transported to global bounds as follows:

1. Connecting the Bochner set integral ∫_{A_n} f to the lintegral
   ∫⁻_{A_n} ENNReal.ofReal(f). The API `ofReal_integral_eq_lintegral_ofReal`
   requires `Integrable f (μ.restrict s)`. This follows from
   `Measure.integrableOn_of_bounded`, since each truncation has finite measure.

2. Applying `lintegral_iSup_ae` (MCT) to pass from per-n bounds to the global
   lintegral bound ∫⁻ ENNReal.ofReal(f⁺) ≤ c.

3. The symmetric argument for f⁻ and the final combination.

APIs searched:
- `lintegral_indicator` — FOUND: ∫⁻ indicator · f = ∫⁻_{s} f
- `ofReal_integral_eq_lintegral_ofReal` — FOUND: connects Bochner and lintegral
  for nonneg integrable functions
- `integral_eq_lintegral_of_nonneg_ae` — FOUND: alternative connection
- `lintegral_iSup_ae` — FOUND: MCT in iSup form
- `lintegral_tendsto_of_tendsto_of_monotone` — FOUND: MCT in limit form

Implemented route: indicator functions on A_n and B_n, conversion via
`ofReal_integral_eq_lintegral_ofReal`, and MCT via `lintegral_iSup_ae`.
The simple-function, direct-tendsto, and L1/AEEqFun alternatives were unnecessary.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Filter Set
open scoped ENNReal

namespace APMa97J01

/-- Main theorem: under the bounded-integral hypothesis, f is integrable with ∫|f| ≤ 2c.

    Note: problem.tex says "prove f is measurable" which is circular since measurability
    is assumed. The intended conclusion is integrability, with ∫|f| ≤ 2c.

    The proof uses the exhaustion technique: define truncated sets A_n = {|x|≤n, 0≤f≤n}
    and B_n = {|x|≤n, -n≤f≤0}, apply the hypothesis to each, then pass to the limit
    via the Monotone Convergence Theorem.

    -- (Memory: math-informal/monotone-approximation) MCT passes per-n bounds to the limit.
    -- (Memory: math-informal/exhaustion-as-theorem) the A_n, B_n sets exhaust {f ≥ 0} and {f ≤ 0}. -/
theorem bounded_integral_implies_integrable
    (f : ℝ → ℝ)
    (hf_meas : Measurable f)
    (c : ℝ) (hc : 0 < c)
    (hbound : ∀ (A : Set ℝ), MeasurableSet A → Bornology.IsBounded A →
      (∃ M, ∀ x ∈ A, |f x| ≤ M) →
      |∫ x in A, f x ∂volume| ≤ c) :
    Integrable f volume ∧ ∫⁻ x, ENNReal.ofReal |f x| ∂volume ≤ ENNReal.ofReal (2 * c) := by
  -- Step 1: Define A_n = {|x| ≤ n, 0 ≤ f ≤ n}
  let A := fun (n : ℕ) => (Icc (-n : ℝ) n) ∩ {x | 0 ≤ f x} ∩ {x | f x ≤ n}

  have hA_meas : ∀ n : ℕ, MeasurableSet (A n) := fun n => by
    refine measurableSet_Icc.inter ?_ |>.inter ?_
    · exact hf_meas measurableSet_Ici
    · exact hf_meas measurableSet_Iic
  have hA_bounded : ∀ n : ℕ, Bornology.IsBounded (A n) := fun n =>
    Bornology.IsBounded.subset (Metric.isBounded_Icc (-(n:ℝ)) n) fun x hx => by
      simp only [A] at hx; exact hx.1.1
  have hA_fbounded : ∀ n : ℕ, ∃ M, ∀ x ∈ A n, |f x| ≤ M := fun n => by
    refine ⟨n, fun x hx => ?_⟩
    show |f x| ≤ n
    have hf : 0 ≤ f x ∧ f x ≤ (n : ℝ) := by
      show _ ∧ _
      simp only [A] at hx
      exact ⟨hx.1.2, hx.2⟩
    exact abs_le.mpr ⟨by linarith [hf.1], mod_cast hf.2⟩

  -- Step 2: Apply the hypothesis to each A_n: |∫_{A_n} f| ≤ c
  have hA_int_bound : ∀ n : ℕ, |∫ x in A n, f x ∂volume| ≤ c := fun n =>
    hbound (A n) (hA_meas n) (hA_bounded n) (hA_fbounded n)

  -- Step 3: On A_n, f ≥ 0, so ∫_{A_n} f ≥ 0, thus ∫_{A_n} f ≤ c
  have hA_int_nonneg : ∀ n : ℕ, 0 ≤ ∫ x in A n, f x ∂volume := fun n => by
    apply setIntegral_nonneg (hA_meas n)
    intro x hx
    show 0 ≤ f x
    simp only [A] at hx
    exact hx.1.2
  have hA_int_le : ∀ n : ℕ, ∫ x in A n, f x ∂volume ≤ c := fun n => by
    have hn := hA_int_nonneg n
    have hb := hA_int_bound n
    exact (abs_of_nonneg hn).symm ▸ hb

  -- Step 4: Define B_n = {|x| ≤ n, -n ≤ f ≤ 0} (the negative part truncation)
  let B := fun (n : ℕ) => (Icc (-n : ℝ) n) ∩ {x | -n ≤ f x} ∩ {x | f x ≤ 0}
  have hB_meas : ∀ n : ℕ, MeasurableSet (B n) := fun n => by
    refine measurableSet_Icc.inter ?_ |>.inter ?_
    · exact hf_meas measurableSet_Ici
    · exact hf_meas measurableSet_Iic
  have hB_bounded : ∀ n : ℕ, Bornology.IsBounded (B n) := fun n =>
    Bornology.IsBounded.subset (Metric.isBounded_Icc (-(n:ℝ)) n) fun x hx => by
      simp only [B] at hx; exact hx.1.1
  have hB_fbounded : ∀ n : ℕ, ∃ M, ∀ x ∈ B n, |f x| ≤ M := fun n => by
    refine ⟨n, fun x hx => ?_⟩
    show |f x| ≤ n
    have hf : -(n:ℝ) ≤ f x ∧ f x ≤ 0 := by
      simp only [B] at hx; exact ⟨hx.1.2, hx.2⟩
    exact abs_le.mpr ⟨mod_cast hf.1, by linarith [hf.2]⟩
  have hB_int_bound : ∀ n : ℕ, |∫ x in B n, f x ∂volume| ≤ c := fun n =>
    hbound (B n) (hB_meas n) (hB_bounded n) (hB_fbounded n)
  have hB_int_nonpos : ∀ n : ℕ, ∫ x in B n, f x ∂volume ≤ 0 := fun n => by
    apply setIntegral_nonpos (hB_meas n)
    intro x hx
    show f x ≤ 0
    simp only [B] at hx; exact hx.2
  have hB_int_ge_neg_c : ∀ n : ℕ, -c ≤ ∫ x in B n, f x ∂volume := fun n => by
    have hb := hB_int_bound n
    have hn := hB_int_nonpos n
    have : |∫ x in B n, f x ∂volume| = -(∫ x in B n, f x ∂volume) := by
      rw [abs_of_nonpos hn]
    rw [this] at hb
    linarith

  -- Step 5: Bounded lintegral of positive part via MCT
  -- f⁺ = max(f,0), and on A_n, f⁺ = f. The per-n Bochner integral bound ∫_{A_n} f ≤ c
  -- must be transported to the lintegral level to apply MCT.
  -- See the file-level comment for the completed finite-measure + MCT bridge.
  have hlint_pos : ∫⁻ x, ENNReal.ofReal (max (f x) 0) ∂volume ≤ ENNReal.ofReal c := by
    let g : ℕ → ℝ → ℝ≥0∞ := fun n x => (A n).indicator (fun x => ENNReal.ofReal (max (f x) 0)) x
    have hg_meas : ∀ n, Measurable (g n) := fun n => by
      exact ((hf_meas.max measurable_const).ennreal_ofReal).indicator (hA_meas n)
    have hA_mono : ∀ n, A n ⊆ A n.succ := fun n x hx => by
      simp only [A, mem_inter_iff, mem_Icc, mem_setOf_eq] at hx ⊢
      norm_num at hx ⊢
      rcases hx with ⟨⟨⟨hxl, hxu⟩, hnonneg⟩, hfu⟩
      exact ⟨⟨⟨by linarith, by linarith⟩, hnonneg⟩,
        hfu.trans (by exact_mod_cast Nat.le_succ n)⟩
    have hg_mono : ∀ n, ∀ᵐ x ∂volume, g n x ≤ g n.succ x := fun n =>
      Filter.Eventually.of_forall fun x => by
        by_cases hx : x ∈ A n
        · simp [g, hx, hA_mono n hx]
        · simp [g, hx]
    have hA_finite : ∀ n, volume (A n) ≠ ∞ := fun n => by
      apply ne_of_lt
      exact (measure_mono (fun x hx => hx.1.1)).trans_lt measure_Icc_lt_top
    have hf_int : ∀ n, Integrable f (volume.restrict (A n)) := fun n => by
      apply Measure.integrableOn_of_bounded (hA_finite n) hf_meas.aestronglyMeasurable
      filter_upwards [ae_restrict_mem (hA_meas n)] with x hx
      exact hA_fbounded n |>.choose_spec x hx
    have hg_bound : ∀ n, ∫⁻ x, g n x ∂volume ≤ ENNReal.ofReal c := fun n => by
      rw [lintegral_indicator (hA_meas n)]
      calc
        (∫⁻ x in A n, ENNReal.ofReal (max (f x) 0) ∂volume) =
            ENNReal.ofReal (∫ x in A n, f x ∂volume) := by
          rw [ofReal_integral_eq_lintegral_ofReal (hf_int n)]
          · apply lintegral_congr
            intro x
            by_cases hx : x ∈ A n
            · have hfx : 0 ≤ f x := by simpa only [A] using hx.1.2
              simp [max_eq_left hfx]
            · simp [Measure.restrict_apply (hA_meas n), hx]
          · filter_upwards [ae_restrict_mem (hA_meas n)] with x hx
            simpa only [A] using hx.1.2
        _ ≤ ENNReal.ofReal c := ENNReal.ofReal_le_ofReal (hA_int_le n)
    have hsup : (⨆ n, ∫⁻ x, g n x ∂volume) ≤ ENNReal.ofReal c := iSup_le hg_bound
    rw [← lintegral_iSup_ae hg_meas hg_mono] at hsup
    calc
      (∫⁻ x, ENNReal.ofReal (max (f x) 0) ∂volume) = ∫⁻ x, ⨆ n, g n x ∂volume := by
        apply lintegral_congr
        intro x
        apply le_antisymm
        · by_cases hx : 0 ≤ f x
          · let n₁ : ℕ := (exists_nat_ge |x|).choose
            let n₂ : ℕ := (exists_nat_ge (f x)).choose
            let n := max n₁ n₂
            have hn₁ : |x| ≤ (n₁ : ℝ) := (exists_nat_ge |x|).choose_spec
            have hn₂ : f x ≤ (n₂ : ℝ) := (exists_nat_ge (f x)).choose_spec
            have hnx : |x| ≤ (n : ℝ) ∧ f x ≤ (n : ℝ) := ⟨
              hn₁.trans (by exact_mod_cast Nat.le_max_left n₁ n₂),
              hn₂.trans (by exact_mod_cast Nat.le_max_right n₁ n₂)⟩
            have hmem : x ∈ A n := by
              unfold A
              exact ⟨⟨⟨(neg_le_of_abs_le hnx.1), (le_of_abs_le hnx.1)⟩, hx⟩, hnx.2⟩
            apply le_trans ?_ (le_iSup (fun k => g k x) n)
            simp [g, hmem]
          · simp [max_eq_right (le_of_not_ge hx)]
        · apply iSup_le
          intro n
          show (A n).indicator (fun x => ENNReal.ofReal (max (f x) 0)) x ≤ _
          exact Set.indicator_le_self (A n) _ x
      _ ≤ ENNReal.ofReal c := hsup

  -- Step 6: Bounded lintegral of negative part via MCT (symmetric)
  have hlint_neg : ∫⁻ x, ENNReal.ofReal (max (-f x) 0) ∂volume ≤ ENNReal.ofReal c := by
    let g : ℕ → ℝ → ℝ≥0∞ := fun n x => (B n).indicator (fun x => ENNReal.ofReal (max (-f x) 0)) x
    have hg_meas : ∀ n, Measurable (g n) := fun n => by
      exact (((hf_meas.neg).max measurable_const).ennreal_ofReal).indicator (hB_meas n)
    have hB_mono : ∀ n, B n ⊆ B n.succ := fun n x hx => by
      simp only [B, mem_inter_iff, mem_Icc, mem_setOf_eq] at hx ⊢
      norm_num at hx ⊢
      rcases hx with ⟨⟨⟨hxl, hxu⟩, hfl⟩, hnonpos⟩
      exact ⟨⟨⟨by linarith, by linarith⟩,
        (by linarith)⟩, hnonpos⟩
    have hg_mono : ∀ n, ∀ᵐ x ∂volume, g n x ≤ g n.succ x := fun n =>
      Filter.Eventually.of_forall fun x => by
        by_cases hx : x ∈ B n
        · simp [g, hx, hB_mono n hx]
        · simp [g, hx]
    have hB_finite : ∀ n, volume (B n) ≠ ∞ := fun n => by
      apply ne_of_lt
      exact (measure_mono (fun x hx => hx.1.1)).trans_lt measure_Icc_lt_top
    have hf_int : ∀ n, Integrable f (volume.restrict (B n)) := fun n => by
      apply Measure.integrableOn_of_bounded (hB_finite n) hf_meas.aestronglyMeasurable
      filter_upwards [ae_restrict_mem (hB_meas n)] with x hx
      exact hB_fbounded n |>.choose_spec x hx
    have hg_bound : ∀ n, ∫⁻ x, g n x ∂volume ≤ ENNReal.ofReal c := fun n => by
      rw [lintegral_indicator (hB_meas n)]
      calc
        (∫⁻ x in B n, ENNReal.ofReal (max (-f x) 0) ∂volume) =
            ENNReal.ofReal (∫ x in B n, (-f) x ∂volume) := by
          symm
          rw [ofReal_integral_eq_lintegral_ofReal (hf_int n).neg]
          · apply lintegral_congr
            intro x
            by_cases hx : x ∈ B n
            · have hfx : f x ≤ 0 := hx.2
              simp [max_eq_left (neg_nonneg.mpr hfx)]
            · simp [hx]
          · filter_upwards [ae_restrict_mem (hB_meas n)] with x hx
            exact neg_nonneg.mpr hx.2
        _ = ENNReal.ofReal (-(∫ x in B n, f x ∂volume)) := by
          congr 1
          change (∫ x in B n, -f x ∂volume) = _
          rw [integral_neg]
        _ ≤ ENNReal.ofReal c := ENNReal.ofReal_le_ofReal (by linarith [hB_int_ge_neg_c n])
    have hsup : (⨆ n, ∫⁻ x, g n x ∂volume) ≤ ENNReal.ofReal c := iSup_le hg_bound
    rw [← lintegral_iSup_ae hg_meas hg_mono] at hsup
    calc
      (∫⁻ x, ENNReal.ofReal (max (-f x) 0) ∂volume) = ∫⁻ x, ⨆ n, g n x ∂volume := by
        apply lintegral_congr
        intro x
        apply le_antisymm
        · by_cases hx : f x ≤ 0
          · let n₁ : ℕ := (exists_nat_ge |x|).choose
            let n₂ : ℕ := (exists_nat_ge (-f x)).choose
            let n := max n₁ n₂
            have hn₁ : |x| ≤ (n₁ : ℝ) := (exists_nat_ge |x|).choose_spec
            have hn₂ : -f x ≤ (n₂ : ℝ) := (exists_nat_ge (-f x)).choose_spec
            have hnx : |x| ≤ (n : ℝ) ∧ -f x ≤ (n : ℝ) := ⟨
              hn₁.trans (by exact_mod_cast Nat.le_max_left n₁ n₂),
              hn₂.trans (by exact_mod_cast Nat.le_max_right n₁ n₂)⟩
            have hmem : x ∈ B n := by
              unfold B
              exact ⟨⟨⟨neg_le_of_abs_le hnx.1, le_of_abs_le hnx.1⟩,
                by simpa using neg_le_neg hnx.2⟩, hx⟩
            apply le_trans ?_ (le_iSup (fun k => g k x) n)
            simp [g, hmem]
          · have : -f x ≤ 0 := by linarith
            simp [max_eq_right this]
        · apply iSup_le
          intro n
          show (B n).indicator (fun x => ENNReal.ofReal (max (-f x) 0)) x ≤ _
          exact Set.indicator_le_self (B n) _ x
      _ ≤ ENNReal.ofReal c := hsup

  -- Step 7: Combine
  -- |f| = f⁺ + f⁻, so ∫⁻ ofReal|f| = ∫⁻ ofReal(f⁺) + ∫⁻ ofReal(f⁻) ≤ 2c
  have hlint_abs : ∫⁻ x, ENNReal.ofReal |f x| ∂volume ≤ ENNReal.ofReal (2 * c) := by
    have hpoint : ∀ x, |f x| = max (f x) 0 + max (-f x) 0 := fun x => by
      rcases le_total 0 (f x) with hx | hx <;> simp [max_eq_left, max_eq_right, hx]
    rw [lintegral_congr (fun x => by rw [hpoint x, ENNReal.ofReal_add] <;> positivity),
      lintegral_add_left ((hf_meas.max measurable_const).ennreal_ofReal)]
    calc
      (∫⁻ x, ENNReal.ofReal (max (f x) 0) ∂volume) +
          ∫⁻ x, ENNReal.ofReal (max (-f x) 0) ∂volume ≤
          ENNReal.ofReal c + ENNReal.ofReal c := add_le_add hlint_pos hlint_neg
      _ = ENNReal.ofReal (2 * c) := by
        rw [← ENNReal.ofReal_add hc.le hc.le]
        congr 1
        ring

  -- Step 8: Conclude integrability from finite lintegral
  refine ⟨?_, hlint_abs⟩
  refine ⟨hf_meas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  have htop : ENNReal.ofReal (2 * c) < ∞ := ENNReal.ofReal_lt_top
  exact lt_of_le_of_lt (by simpa only [Real.norm_eq_abs] using hlint_abs) htop

#print axioms APMa97J01.bounded_integral_implies_integrable

end APMa97J01
