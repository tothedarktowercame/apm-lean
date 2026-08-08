import Mathlib

/-!
# APM a93A02 — L²-bounded a.e. convergence and convergence in Lᵖ

## Statement repairs

The source's finite supremum is encoded by a bound in `NNReal`; an `ENNReal`
bound could be `⊤` and would be vacuous. Sequences are indexed by `ℕ`, using
`n + 1` in the explicit spike family corresponding to the source's indexing
from one.

## Encoding questions

None. Both parts use the actual restricted Lebesgue measure and Mathlib's
`MemLp` and `eLpNorm`.

The counterexample follows the normalized-spike construction used in
`problems/a01J01/lean/Main.lean`.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

def apm_a93A02_measure : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

def apm_a93A02_counterexample (n : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt (n.succ : ℝ) *
    Set.indicator (Icc (0 : ℝ) ((n.succ : ℝ)⁻¹)) (fun _ ↦ (1 : ℝ)) x

/-- Uniform `L²` boundedness implies uniform integrability in every
`Lᵖ`, `1 ≤ p < 2`. Adapted from the earlier a93A02 development at commit
`4f07f5f`. -/
lemma apm_a93A02_unifIntegrable_of_L2_bounded
    {f : ℕ → ℝ → ℝ} {μ : Measure ℝ}
    (hfm : ∀ n, AEStronglyMeasurable (f n) μ)
    (hf2 : ∀ n, MemLp (f n) 2 μ)
    (hbdd : ∃ C : NNReal, ∀ n, eLpNorm (f n) 2 μ ≤ C)
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p < 2) :
    UnifIntegrable f p μ := by
  obtain ⟨C, hC⟩ := hbdd
  have hp_top : p ≠ ∞ := ne_of_lt (hp2.trans_le le_top)
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos (by positivity) hp_top
  have hp2_real : p.toReal < 2 := by
    simpa using (ENNReal.toReal_lt_toReal hp_top (by norm_num)).2 hp2
  let r : ℝ := 1 / p.toReal - 1 / 2
  have hr : 0 < r := by
    dsimp [r]
    exact sub_pos.2 (one_div_lt_one_div_of_lt hp_pos hp2_real)
  intro ε hε
  let D : ℝ := C + 1
  have hD : 0 < D := by dsimp [D]; positivity
  let δ : ℝ := (ε / D) ^ (1 / r)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact Real.rpow_pos_of_pos (div_pos hε hD) _
  refine ⟨δ, hδ, fun n s hs hμs => ?_⟩
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
  calc
    eLpNorm (f n) p (μ.restrict s) ≤
        eLpNorm (f n) 2 (μ.restrict s) * (μ.restrict s) univ ^ r := by
      exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp2.le
        ((hfm n).mono_measure Measure.restrict_le_self)
    _ ≤ eLpNorm (f n) 2 μ * μ s ^ r := by
      rw [Measure.restrict_apply_univ]
      exact mul_le_mul'
        (eLpNorm_mono_measure (f n) Measure.restrict_le_self)
        (ENNReal.rpow_le_rpow le_rfl hr.le)
    _ ≤ (C : ℝ≥0∞) * μ s ^ r := mul_le_mul_left (hC n) _
    _ ≤ (C : ℝ≥0∞) * ENNReal.ofReal δ ^ r := by
      exact mul_le_mul_right (ENNReal.rpow_le_rpow hμs hr.le) _
    _ ≤ ENNReal.ofReal D * ENNReal.ofReal δ ^ r := by
      gcongr
      rw [ENNReal.coe_nnreal_eq]
      exact ENNReal.ofReal_le_ofReal (by dsimp [D]; linarith)
    _ = ENNReal.ofReal ε := by
      rw [ENNReal.ofReal_rpow_of_pos hδ, ← ENNReal.ofReal_mul hD.le]
      congr 1
      dsimp [δ]
      rw [← Real.rpow_mul (le_of_lt (div_pos hε hD)),
        one_div_mul_cancel hr.ne', Real.rpow_one, mul_div_cancel₀ ε hD.ne']

lemma apm_a93A02_tendsto_Lp_of_ae_tendsto_of_L2_bounded
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {μ : Measure ℝ}
    (hfm : ∀ n, AEStronglyMeasurable (f n) μ)
    (hgm : AEStronglyMeasurable g μ)
    (hf2 : ∀ n, MemLp (f n) 2 μ)
    (hbdd : ∃ C : NNReal, ∀ n, eLpNorm (f n) 2 μ ≤ C)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p < 2) [IsFiniteMeasure μ] :
    Tendsto (fun n => eLpNorm (fun x => f n x - g x) p μ) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := hbdd
  have hg2_norm : eLpNorm g 2 μ ≤ C :=
    Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall hC) hfm hae
  have hg2 : MemLp g 2 μ := ⟨hgm, hg2_norm.trans_lt ENNReal.coe_lt_top⟩
  have hgp : MemLp g p μ := hg2.mono_exponent hp2.le
  have hui : UnifIntegrable f p μ :=
    apm_a93A02_unifIntegrable_of_L2_bounded hfm hf2 ⟨C, hC⟩ hp1 hp2
  simpa only [Pi.sub_apply] using
    tendsto_Lp_finite_of_tendsto_ae hp1 (ne_of_lt (hp2.trans_le le_top))
      hfm hgp hui hae

theorem apm_a93a02 :
    (∀ (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (p : ℝ≥0∞),
      (∀ n, MemLp (f n) 2 apm_a93A02_measure) →
      (∃ C : NNReal, ∀ n, eLpNorm (f n) 2 apm_a93A02_measure ≤ C) →
      (∀ᵐ x ∂apm_a93A02_measure,
        Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) →
      1 ≤ p → p < 2 →
      Tendsto
        (fun n ↦ eLpNorm (fun x ↦ f n x - g x) p apm_a93A02_measure)
        atTop (𝓝 0)) ∧
    (∀ n, MemLp (apm_a93A02_counterexample n) 2 apm_a93A02_measure) ∧
    (∀ n, eLpNorm (apm_a93A02_counterexample n) 2 apm_a93A02_measure ≤ 1) ∧
    (∀ᵐ x ∂apm_a93A02_measure,
      Tendsto (fun n ↦ apm_a93A02_counterexample n x) atTop (𝓝 0)) ∧
    ¬Tendsto
      (fun n ↦ eLpNorm (fun x ↦ apm_a93A02_counterexample n x - 0)
        2 apm_a93A02_measure)
      atTop (𝓝 0) := by
  constructor
  · intro f g p hf hbdd hae hp1 hp2
    have hfm : ∀ n, AEStronglyMeasurable (f n) apm_a93A02_measure :=
      fun n ↦ (hf n).1
    have hgm : AEStronglyMeasurable g apm_a93A02_measure :=
      aestronglyMeasurable_of_tendsto_ae atTop hfm hae
    letI : IsFiniteMeasure apm_a93A02_measure := by
      unfold apm_a93A02_measure
      infer_instance
    exact apm_a93A02_tendsto_Lp_of_ae_tendsto_of_L2_bounded
      hfm hgm hf hbdd hae hp1 hp2
  · /-
    Closer hop 1 recovered and localized the complete positive-result proof
    from git commit `4f07f5f`: the `L²` bound yields uniform integrability in
    `Lᵖ` by the finite-measure exponent comparison, and Mathlib's Vitali
    theorem gives convergence.

    Searches of `LEMMA-INDEX.md`, all `ConstructionTargets/`, Mathlib's
    indicator `eLpNorm` API, prior spike artifact `a01J01`, and git history
    found the necessary primitives but no proof for this exact normalized
    square-root spike over the restricted measure. The remaining conjunction
    requires evaluating

      `eLpNorm (sqrt(n+1) * 1_[0,1/(n+1)]) 2 = 1`,

    transporting the interval volume through the outer restriction, proving
    pointwise eventual vanishing away from the null singleton `{0}`, and using
    the constant norm-one computation to refute convergence to zero. These are
    now independent of the fully compiled Vitali half.
    -/
    sorry
