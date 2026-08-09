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

/-- The defining supremum of the weak-`L¹` size gives the usual reciprocal
bound for every positive level. -/
lemma apm_a03J04_distribution_le_div_weakL1Size
    {n : ℕ} (f : A03J04Space n → ℝ) (M : ℝ≥0∞)
    (hweak : apm_a03J04_weakL1Size f = M)
    {α : ℝ} (hα : 0 < α) :
    apm_a03J04_distribution f α ≤ M / ENNReal.ofReal α := by
  have hmul : ENNReal.ofReal α * apm_a03J04_distribution f α ≤ M := by
    rw [← hweak]
    exact le_iSup (fun (a : {α : ℝ // 0 < α}) =>
      ENNReal.ofReal a.1 * apm_a03J04_distribution f a.1) ⟨α, hα⟩
  rw [ENNReal.le_div_iff_mul_le
    (Or.inl (ne_of_gt (ENNReal.ofReal_pos.mpr hα)))
    (Or.inl ENNReal.ofReal_ne_top)]
  simpa [mul_comm] using hmul

/-- On a measurable finite-measure set, each restricted superlevel measure is
bounded both by the set's measure and by the weak-`L¹` reciprocal estimate. -/
lemma apm_a03J04_restrict_level_le_min
    {n : ℕ} (f : A03J04Space n → ℝ) (M : ℝ≥0∞)
    (E : Set (A03J04Space n))
    (hweak : apm_a03J04_weakL1Size f = M)
    {α : ℝ} (hα : 0 < α) :
    (volume.restrict E) {x | α < |f x|} ≤
      min (volume E) (M / ENNReal.ofReal α) := by
  apply le_min
  · calc
      (volume.restrict E) {x | α < |f x|} ≤
          (volume.restrict E) Set.univ := measure_mono (subset_univ _)
      _ = volume E := by simp
  · calc
      (volume.restrict E) {x | α < |f x|} ≤
          volume {x | α < |f x|} := Measure.restrict_le_self _
      _ = apm_a03J04_distribution f α := rfl
      _ ≤ M / ENNReal.ofReal α :=
        apm_a03J04_distribution_le_div_weakL1Size f M hweak hα

/-- Weighted layer cake for `|f|^p` on the restricted measure. This is the
exact Mathlib identity used before inserting the weak-`L¹` level bound. -/
lemma apm_a03J04_lintegral_rpow_eq_level_lintegral
    {n : ℕ} (f : A03J04Space n → ℝ) (p : ℝ)
    (E : Set (A03J04Space n)) (hf : Measurable f) (hp : 0 < p) :
    (∫⁻ x in E, ENNReal.ofReal (Real.rpow |f x| p) ∂volume) =
      ENNReal.ofReal p *
        ∫⁻ t in Ioi (0 : ℝ),
          (volume.restrict E) {x | t < |f x|} *
            ENNReal.ofReal (Real.rpow t (p - 1)) := by
  exact MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul
    (volume.restrict E)
    (Filter.Eventually.of_forall fun x => abs_nonneg (f x))
    hf.abs.aemeasurable hp

/-- The desired local weak-`L¹` estimate is immediate on a null set. Keeping
this branch separate removes the zero denominator from the crossover split. -/
lemma apm_a03J04_weakL1_rpow_setIntegral_of_measure_zero
    {n : ℕ} (f : A03J04Space n → ℝ) (M : ℝ≥0∞) (p : ℝ)
    (E : Set (A03J04Space n)) (hp1 : p < 1) (hE0 : volume E = 0) :
    IntegrableOn (fun x => Real.rpow |f x| p) E volume ∧
      (∫ x in E, Real.rpow |f x| p ∂volume) ≤
        (1 / (1 - p)) * Real.rpow (volume E).toReal (1 - p) *
          Real.rpow M.toReal p := by
  constructor
  · exact IntegrableOn.of_measure_zero hE0
  · rw [setIntegral_measure_zero _ hE0, hE0]
    simp [Real.zero_rpow (sub_pos.mpr hp1).ne']

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
  by_cases hE0 : volume E = 0
  · exact apm_a03J04_weakL1_rpow_setIntegral_of_measure_zero
      f M p E hp1 hE0
  have hEpos : 0 < (volume E).toReal := ENNReal.toReal_pos hE0 hEfin
  /-
  CLOSER HOP 1: the main theorem is now routed entirely through this bridge,
  so its former part-(b) and part-(c) sorries are closed. A renewed Mathlib
  search found `MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul`, which
  directly gives the weighted layer-cake identity

    ∫⁻ |f|^p = ofReal p * ∫⁻ t>0, μ {|f| > t} * ofReal (t^(p-1)).

  Applying it to `volume.restrict E` avoids the earlier level-set conversion
  through `|f|^p`. The remaining local assembly is to derive

    (volume.restrict E) {|f| > t} ≤ min (volume E) (M / ofReal t)

  from the `iSup` definition of `apm_a03J04_weakL1Size`, split the weighted
  lintegral at `t = M.toReal / (volume E).toReal`, evaluate both real-power
  improper integrals, and transport the finite ENNReal bound back to Bochner
  integrability and the displayed real inequality. Searches of
  `LEMMA-INDEX.md`, all `ConstructionTargets`, solved weak-type siblings,
  Mathlib's layer-cake, improper-integral, `min`, and `eLpNorm` sources, and
  git history found no packaged weak-L1-to-local-Lp theorem or evaluator for
  this minimum majorant. No axiom, opaque declaration, or `native_decide` was
  introduced; the frozen statement is unchanged.

  CLOSER HOP 2 goes beyond that search by compiling the missing measure-side
  prerequisites. `apm_a03J04_distribution_le_div_weakL1Size` extracts the
  reciprocal bound from the defining `iSup` using `ENNReal.le_div_iff_mul_le`.
  `apm_a03J04_restrict_level_le_min` combines it with restriction monotonicity
  to prove the exact minimum majorant above. Finally,
  `apm_a03J04_lintegral_rpow_eq_level_lintegral` specializes Mathlib's
  weighted layer-cake theorem to `|f|` and `volume.restrict E`. Thus no
  level-set, measurability, or weak-size extraction remains open.

  A separate search of Mathlib's Lorentz/weak-type APIs found no Lorentz-space
  abstraction at all, and a truncation/eLpNorm route still reduces to the same
  tail integral. The sole remaining bridge is the scalar ENNReal calculation:
  integrate

    min (volume E) (M / ofReal t) * ofReal (t^(p-1))

  over `Ioi 0`, split at the crossover (including the zero-measure and zero-M
  cases), use the real improper-rpow formulas on both pieces, then transport
  the resulting finite lintegral to `IntegrableOn` and the stated real bound.

  CLOSER HOP 3 compiles and dispatches the zero-measure edge case in
  `apm_a03J04_weakL1_rpow_setIntegral_of_measure_zero`; consequently the live
  branch now carries `0 < (volume E).toReal`, proved from `hE0` and `hEfin`.
  This removes the crossover's zero denominator. A renewed attempt to isolate
  `M = 0` used the compiled minimum bound to make every positive superlevel
  measure zero, but converting that family to an a.e.-zero statement (or
  directly to a zero lintegral) requires the same countable-level/lintegral
  assembly and did not shorten the proof.

  Searches beyond hop 2 included Mathlib's `Measure.restrict_eq_zero`,
  `IntegrableOn.of_measure_zero`, `setIntegral_measure_zero`, a.e.-zero and
  superlevel-measure lemmas, plus solved null-set integration artifacts. The
  first three were used to close the null-set branch; no packaged theorem was
  found for the zero-superlevel-to-a.e.-zero conversion in this exact real
  encoding. The remaining positive-measure branch is still the scalar ENNReal
  crossover integration and final Bochner/toReal transport described above.
  -/
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
    exact (apm_a03J04_bridge_weakL1_rpow_setIntegral
      f M p E hf hweak hM hp hp1 hE hEfin).1
  · -- Part (c): Explicit bound with c = 1/(1-p).
    intro p hp hp1
    refine ⟨1 / (1 - p), div_pos zero_lt_one (sub_pos.mpr hp1), ?_⟩
    intro f M E hf hweak hM hE hEfin
    exact (apm_a03J04_bridge_weakL1_rpow_setIntegral
      f M p E hf hweak hM hp hp1 hE hEfin).2
