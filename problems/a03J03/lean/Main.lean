import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
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
  -- Approximate f by φ ∈ C_c with ‖f-φ‖_p < ε/(2‖g‖_q)
  -- |f*g(x)| ≤ |φ*g(x)| + ε/2
  -- φ*g(x) = ∫_{x-R}^{x+R} φ(x-y)g(y)dy → 0 as |x|→∞
  -- (sliding window integral of g^q → 0)
  sorry
