import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory Set Filter Topology

noncomputable section

/-! # APM a03J03: f ∈ Lp, g ∈ Lq ⟹ f*g continuous and vanishes at ∞

  Proof structure:
  Part 1 (Continuity): Hölder gives |f*g(x+h)-f*g(x)| ≤ ‖τ_h f - f‖_p · ‖g‖_q.
    Translation continuity in Lp (‖τ_h f - f‖_p → 0) closes it.
  Part 2 (Vanishing): Approximate f by φ ∈ C_c. Then |f*g(x)| ≤ |φ*g(x)| + ε.
    φ*g(x) involves integration over a compact sliding window → 0 as |x| → ∞.

  Mathlib has:
  - Convolution definition: Analysis.Convolution
  - Hölder: integral_mul_le_Lp_mul_Lq_of_nonneg
  - Translation continuity through `Continuous.compMeasurePreservingLp`
  - C_c approximation in Lp: `MemLp.exists_hasCompactSupport_eLpNorm_sub_le`
  The specific "Lp * Lq is continuous + C₀" is NOT in Mathlib.
-/

/-! The Hölder hypotheses do at least make every pointwise convolution integral
well-defined.  This is kept separate from the missing analytic input below:
strong continuity of translations in `Lᵖ`. -/

lemma integrable_convolution_at {p q : ℝ} (hpq : p.HolderConjugate q)
    {f : ℝ → ℝ} {g : ℝ → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) volume)
    (hg : MemLp g (ENNReal.ofReal q) volume) (x : ℝ) :
    Integrable (fun y => f (x - y) * g y) volume := by
  letI : ENNReal.HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal q) 1 :=
    hpq.ennrealOfReal
  have hfx : MemLp (fun y => f (x - y)) (ENNReal.ofReal p) volume := by
    simpa [Function.comp_def] using
      hf.comp_measurePreserving ((volume : Measure ℝ).measurePreserving_sub_left x)
  simpa only [Pi.mul_apply] using hfx.integrable_mul hg

-- Part 1: Continuity of f*g
-- |f*g(x+h) - f*g(x)| ≤ ‖τ_h f - f‖_p · ‖g‖_q → 0
-- Key ingredient: translation continuity in Lp
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
