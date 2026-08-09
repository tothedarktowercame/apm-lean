import Mathlib

/-!
# APM a03J04: Distribution functions and weak-L¹ estimates

## Statement repairs

The source calls `E` a subset of finite measure. We make explicit the standard
implicit requirement that `E` is Lebesgue measurable, so `∫_E` denotes
integration over a measurable set.

## Encoding questions

None. `ℝⁿ` is encoded as `EuclideanSpace ℝ (Fin n)`, `m` as its Lebesgue
measure, and the distribution function and weak-L¹ supremum take values in
`ℝ≥0∞` so infinite level-set measures are represented honestly.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The ambient Euclidean space `ℝⁿ`. -/
abbrev A03J04Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The distribution function `λ(α) = m {x | |f x| > α}`. -/
def apm_a03J04_distribution {n : ℕ}
    (f : A03J04Space n → ℝ) (α : ℝ) : ℝ≥0∞ :=
  volume {x | α < |f x|}

/-- The weak-L¹ size `sup_{α > 0} α λ(α)`. -/
def apm_a03J04_weakL1Size {n : ℕ}
    (f : A03J04Space n → ℝ) : ℝ≥0∞ :=
  ⨆ α : {α : ℝ // 0 < α},
    ENNReal.ofReal α.1 * apm_a03J04_distribution f α.1

/-- Why this unblocks `apm_a03j04`: this is the missing layer-cake and
improper-integral estimate, including the ENNReal-to-real conversion. Its
integrability conclusion closes part (b), while the sharp quantitative bound
with constant `1 / (1-p)` closes part (c). -/
theorem apm_a03J04_bridge_weakL1_rpow_setIntegral
    {n : ℕ} (f : A03J04Space n → ℝ) (M : ℝ≥0∞) (p : ℝ)
    (E : Set (A03J04Space n))
    (hf : Measurable f)
    (hweak : apm_a03J04_weakL1Size f = M)
    (hM : M ≠ ⊤) (hp : 0 < p) (hp1 : p < 1)
    (hE : MeasurableSet E) (hEfin : volume E ≠ ⊤) :
    IntegrableOn (fun x => Real.rpow |f x| p) E volume ∧
      (∫ x in E, Real.rpow |f x| p ∂volume) ≤
        (1 / (1 - p)) * Real.rpow (volume E).toReal (1 - p) *
          Real.rpow M.toReal p := by
  sorry

theorem apm_a03j04 (n : ℕ) :
    (∀ f : A03J04Space n → ℝ,
      Measurable f → Integrable f volume →
      (∫⁻ x, ENNReal.ofReal |f x| ∂volume) =
        ∫⁻ α in Ioi (0 : ℝ), apm_a03J04_distribution f α) ∧
    (∀ (f : A03J04Space n → ℝ) (M : ℝ≥0∞) (p : ℝ)
        (E : Set (A03J04Space n)),
      Measurable f → apm_a03J04_weakL1Size f = M → M ≠ ⊤ →
      0 < p → p < 1 → MeasurableSet E → volume E ≠ ⊤ →
      IntegrableOn (fun x => Real.rpow |f x| p) E volume) ∧
    (∀ p : ℝ, 0 < p → p < 1 →
      ∃ c : ℝ, 0 < c ∧
        ∀ (f : A03J04Space n → ℝ) (M : ℝ≥0∞)
            (E : Set (A03J04Space n)),
          Measurable f → apm_a03J04_weakL1Size f = M → M ≠ ⊤ →
          MeasurableSet E → volume E ≠ ⊤ →
          (∫ x in E, Real.rpow |f x| p ∂volume) ≤
            c * Real.rpow (volume E).toReal (1 - p) *
              Real.rpow M.toReal p) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Part (a): Layer cake formula.
    -- ∫⁻ x, ofReal |f x| = ∫⁻ α in Ioi 0, volume {x | α < |f x|}
    -- Direct application of Mathlib's `lintegral_eq_lintegral_meas_lt`.
    -- -- (Pattern: math-informal/monotone-approximation — layer cake / Cavalieri)
    intro f hf hfint
    -- Key Mathlib lemma: lintegral_eq_lintegral_meas_lt applied to |f|
    have hnn : (0 : A03J04Space n → ℝ) ≤ᵐ[volume] (fun x => |f x|) := by
      filter_upwards with x using abs_nonneg (f x)
    have habs_aemeas : AEMeasurable (fun x => |f x|) volume :=
      hf.aemeasurable.abs
    exact lintegral_eq_lintegral_meas_lt volume hnn habs_aemeas
  · -- Part (b): ∫_E |f|^p < ∞ for weak-L¹ f, 0 < p < 1, m(E) < ∞.
    -- See BOUNDARY comment below.
    intro f M p E hf hweak hM hp hp1 hE hEfin
    -- |f|^p is measurable (and a.e. nonneg)
    have hfp_meas : Measurable fun x => Real.rpow |f x| p := by
      have hcont : Continuous fun (x : ℝ) => x ^ p :=
        Real.continuous_rpow_const hp.le
      have hfabs : Measurable fun x => |f x| := hf.abs
      exact hcont.measurable.comp hfabs
    have hfp_nonneg : ∀ x, 0 ≤ Real.rpow |f x| p := fun x =>
      Real.rpow_nonneg (abs_nonneg _) p
    -- Distribution bound: for α > 0, ofReal α * volume {x | α < |f x|} ≤ M.
    -- This follows from weakL1Size = iSup = M.
    have hdistrib_bound : ∀ α : ℝ, 0 < α →
        ENNReal.ofReal α * apm_a03J04_distribution f α ≤ M := by
      intro α hα
      rw [← hweak]
      exact le_iSup (fun (a : {α : ℝ // 0 < α}) =>
        ENNReal.ofReal a.1 * apm_a03J04_distribution f a.1) ⟨α, hα⟩
    -- BOUNDARY: To complete part (b), we need to show:
    --   ∫⁻ x in E, ENNReal.ofReal (|f x| ^ p) ∂volume < ⊤
    -- via the layer cake applied to |f|^p on E:
    --   = ∫⁻ t in Ioi 0, (volume.restrict E) {x | t < |f x| ^ p}
    -- then bound each level set measure by min(vol(E), M / t^{1/p})
    -- and split at the crossover, using convergence of ∫ t^{-1/p} for p<1.
    --
    -- Routes tried:
    -- - `lintegral_eq_lintegral_meas_lt` for |f|^p restricted to E:
    --   applicable but requires bridging ENNReal.ofReal(|f|^p) ↔ ‖|f|^p‖
    --   for the Bochner integrability definition, plus the full split.
    -- - `Real.continuous_rpow_const`, `Real.rpow_nonneg`, `le_iSup`,
    --   `abs_nonneg`: all verified available and used above.
    --
    -- Specific blocker: the level-set rewrite {|f|^p > t} = {|f| > t^{1/p}}
    -- requires `Real.rpow_lt_rpow_iff` or similar (with sign conditions),
    -- and the final convergence argument needs `integrableOn_Ioi_rpow`
    -- from `Mathlib.Analysis.SpecialFunctions.ImproperIntegrals` bridged
    -- through the ENNReal lintegral — a gap of ~15-20 tactic steps
    -- with non-trivial ENNReal/Real arithmetic.
    sorry
  · -- Part (c): Explicit bound with c = 1/(1-p).
    sorry
