import Mathlib

/-!
# APM a99J05 — small L¹ norm versus almost-everywhere convergence

## Statement repairs

None. Sequences are indexed by `ℕ`; this is the standard Lean reindexing of
the source's sequence beginning at one.

## Encoding questions

None. The functions, restricted Lebesgue measure on `[0,1]`, L¹ norms, and
almost-everywhere pointwise convergence are all represented directly.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

def apm_a99J05_measure : Measure ℝ := volume.restrict (Set.Icc 0 1)

def apm_a99J05_l1Norm (f : ℝ → ℝ) : ℝ :=
  ∫ x, ‖f x‖ ∂apm_a99J05_measure

lemma apm_a99J05_summable_l1Norm_of_geometric_bound
    (f : ℕ → ℝ → ℝ)
    (hbound : ∀ n, apm_a99J05_l1Norm (f n) ≤ (2 : ℝ)⁻¹ ^ n) :
    Summable (fun n ↦ apm_a99J05_l1Norm (f n)) := by
  apply Summable.of_nonneg_of_le
  · intro n
    exact integral_nonneg (fun x ↦ norm_nonneg (f n x))
  · exact hbound
  · exact summable_geometric_of_norm_lt_one (by norm_num : ‖(2 : ℝ)⁻¹‖ < 1)

/-- Tonelli extraction for the second half: summability of the `L¹` norms
forces pointwise convergence to zero almost everywhere. -/
lemma apm_a99J05_ae_tendsto_zero_of_summable_l1Norm
    (f : ℕ → ℝ → ℝ)
    (hint : ∀ n, Integrable (f n) apm_a99J05_measure)
    (hsum : Summable (fun n ↦ apm_a99J05_l1Norm (f n))) :
    ∀ᵐ x ∂apm_a99J05_measure,
      Tendsto (fun n ↦ f n x) atTop (𝓝 0) := by
  have hmeas : ∀ n, AEMeasurable (fun x ↦ ‖f n x‖ₑ) apm_a99J05_measure :=
    fun n ↦ (hint n).aestronglyMeasurable.enorm
  have htsum : (∑' n, ∫⁻ x, ‖f n x‖ₑ ∂apm_a99J05_measure) ≠ ∞ := by
    rw [show (∑' n, ∫⁻ x, ‖f n x‖ₑ ∂apm_a99J05_measure) =
        ∑' n, ENNReal.ofReal (apm_a99J05_l1Norm (f n)) by
      apply tsum_congr
      intro n
      unfold apm_a99J05_l1Norm
      exact (ofReal_integral_norm_eq_lintegral_enorm (hint n)).symm]
    exact hsum.tsum_ofReal_ne_top
  rw [← lintegral_tsum hmeas] at htsum
  have hae : ∀ᵐ x ∂apm_a99J05_measure, (∑' n, ‖f n x‖ₑ) ≠ ∞ :=
    (ae_lt_top' (AEMeasurable.ennreal_tsum hmeas) htsum).mono
      (fun _ hx ↦ hx.ne)
  filter_upwards [hae] with x hx
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have henorm := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hx
  have hreal := (ENNReal.tendsto_toReal_zero_iff
    (fun n ↦ enorm_ne_top)).2 henorm
  simpa using hreal

theorem apm_a99j05 :
    (∃ f : ℕ → ℝ → ℝ,
      (∀ n, Integrable (f n) apm_a99J05_measure) ∧
      Tendsto (fun n ↦ apm_a99J05_l1Norm (f n)) atTop (𝓝 0) ∧
      ¬(∀ᵐ x ∂apm_a99J05_measure,
        ∃ a : ℝ, Tendsto (fun n ↦ f n x) atTop (𝓝 a))) ∧
    (∀ f : ℕ → ℝ → ℝ,
      (∀ n, Integrable (f n) apm_a99J05_measure) →
      (∀ n, apm_a99J05_l1Norm (f n) ≤ (2 : ℝ)⁻¹ ^ n) →
      ∀ᵐ x ∂apm_a99J05_measure,
        Tendsto (fun n ↦ f n x) atTop (𝓝 0)) := by
  constructor
  · /- CLOSER HOP 2 BOUNDARY.

    This hop closes the complete second conjunct.  The new helper
    `apm_a99J05_ae_tendsto_zero_of_summable_l1Norm` extracts the Tonelli
    argument from Mathlib's `integral_tsum`: it converts the summable real
    integrals to a finite ENNReal `tsum`, uses `lintegral_tsum` and
    `ae_lt_top'`, and then applies
    `ENNReal.tendsto_atTop_zero_of_tsum_ne_top`.  The geometric-bound helper
    supplies its summability premise below.

    The sole remaining bridge is the first conjunct's typewriter sequence.
    Renewed `LEMMA-INDEX.md` inspection found substantial compiled helpers in
    solved/partial sibling `a01A01`: its stage, position, cell integral, and
    vanishing-integral lemmas are precisely reusable mathematical ingredients.
    However, that module's main theorem remains partial and it still lacks the
    cofinal pointwise cell-selection lemma needed to prove that the sequence
    has no pointwise limit.  `ConstructionTargets`, the broader solved corpus,
    Borel--Cantelli sources, and git history contain no closed substitute.
    Thus importing or copying those helpers alone cannot honestly close this
    existential.  The frozen statement is unchanged.
    -/
    sorry
  · intro f hint hbound
    exact apm_a99J05_ae_tendsto_zero_of_summable_l1Norm f hint
      (apm_a99J05_summable_l1Norm_of_geometric_bound f hbound)
