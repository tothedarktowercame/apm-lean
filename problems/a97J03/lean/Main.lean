import Mathlib

/-!
# APM a97J03: Convolution of conjugate Lp functions

## Statement repairs

None.

## Encoding questions

None. Because the source explicitly declares `h : ℝ → ℂ`, the `L^p` and
`L^q` functions are encoded as complex-valued measurable functions. Membership
is represented by Mathlib's `MemLp` at the finite real exponents embedded in
`ℝ≥0∞`.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

noncomputable section

/-- The convolution `h(y) = ∫ x, f(y-x)g(x) dx`. -/
def apm_a97J03_convolution (f g : ℝ → ℂ) (y : ℝ) : ℂ :=
  ∫ x : ℝ, f (y - x) * g x ∂volume

-- (Sibling: a03J03) The real-valued proof is scalar-polymorphic; this is its
-- complex specialization, using the complex multiplication pairing.
private theorem apm_a97J03_convolution_continuous {p q : ℝ}
    (hpq : p.HolderConjugate q) {f g : ℝ → ℂ}
    (hf : MemLp f (ENNReal.ofReal p) volume)
    (hg : MemLp g (ENNReal.ofReal q) volume) :
    Continuous (fun x ↦ ∫ y, f (x - y) * g y) := by
  let P := ENNReal.ofReal p
  let Q := ENNReal.ofReal q
  letI : P.HolderConjugate Q := hpq.ennrealOfReal
  letI : Fact (1 ≤ P) := ⟨ENNReal.HolderConjugate.one_le P Q⟩
  letI : Fact (1 ≤ Q) := ⟨ENNReal.HolderConjugate.one_le Q P⟩
  have hPtop : P ≠ ⊤ := by simp [P]
  let τ : ℝ → C(ℝ, ℝ) :=
    fun x ↦ ⟨fun y ↦ x - y, continuous_const.sub continuous_id⟩
  have hτ : Continuous τ := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : ℝ × ℝ ↦ z.1 - z.2)
    fun_prop
  have hτmp : ∀ x, MeasurePreserving (τ x) volume volume :=
    fun x ↦ (volume : Measure ℝ).measurePreserving_sub_left x
  let F : Lp ℂ P (volume : Measure ℝ) := hf.toLp f
  let G : Lp ℂ Q (volume : Measure ℝ) := hg.toLp g
  have htrans : Continuous (fun x ↦ Lp.compMeasurePreserving (τ x) (hτmp x) F) :=
    continuous_const.compMeasurePreservingLp hτ hτmp hPtop
  let pairing : Lp ℂ P (volume : Measure ℝ) →L[ℂ]
      Lp ℂ Q (volume : Measure ℝ) →L[ℂ] ℂ :=
    (ContinuousLinearMap.mul ℂ ℂ).lpPairing (volume : Measure ℝ) P Q
  have hpair :
      Continuous (fun x ↦ pairing (Lp.compMeasurePreserving (τ x) (hτmp x) F) G) := by
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

-- (Sibling: a03J03) Compact-support density plus the Lp pairing norm gives
-- uniform approximation by a compactly supported convolution.
private theorem apm_a97J03_convolution_tendsto_zero {p q : ℝ}
    (hpq : p.HolderConjugate q) {f g : ℝ → ℂ}
    (hf : MemLp f (ENNReal.ofReal p) volume)
    (hg : MemLp g (ENNReal.ofReal q) volume) :
    Tendsto (fun x ↦ ∫ y, f (x - y) * g y) (cocompact ℝ) (nhds 0) := by
  let P := ENNReal.ofReal p
  let Q := ENNReal.ofReal q
  letI : P.HolderConjugate Q := hpq.ennrealOfReal
  letI : Fact (1 ≤ P) := ⟨ENNReal.HolderConjugate.one_le P Q⟩
  letI : Fact (1 ≤ Q) := ⟨ENNReal.HolderConjugate.one_le Q P⟩
  have hPtop : P ≠ ⊤ := by simp [P]
  have hQtop : Q ≠ ⊤ := by simp [Q]
  let τ : ℝ → C(ℝ, ℝ) :=
    fun x ↦ ⟨fun y ↦ x - y, continuous_const.sub continuous_id⟩
  have hτmp : ∀ x, MeasurePreserving (τ x) volume volume :=
    fun x ↦ (volume : Measure ℝ).measurePreserving_sub_left x
  let pairing : Lp ℂ P (volume : Measure ℝ) →L[ℂ]
      Lp ℂ Q (volume : Measure ℝ) →L[ℂ] ℂ :=
    (ContinuousLinearMap.mul ℂ ℂ).lpPairing (volume : Measure ℝ) P Q
  let F : Lp ℂ P (volume : Measure ℝ) := hf.toLp f
  let G : Lp ℂ Q (volume : Measure ℝ) := hg.toLp g
  have pair_translate_eq {a b : ℝ → ℂ}
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
  let Φ : Lp ℂ P (volume : Measure ℝ) := hφmem.toLp φ
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
  let Ψ : Lp ℂ Q (volume : Measure ℝ) := hψmem.toLp ψ
  have hGΨ : ‖G - Ψ‖ ≤ δg := by
    change ‖hg.toLp g - hψmem.toLp ψ‖ ≤ δg
    rw [← hg.toLp_sub hψmem, Lp.norm_toLp]
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hψerr
    simpa [ENNReal.toReal_ofReal hδg.le] using h
  let core : ℝ → ℂ :=
    fun x ↦ pairing (Lp.compMeasurePreserving (τ x) (hτmp x) Φ) Ψ
  have hcore_eq :
      core = convolution φ ψ (ContinuousLinearMap.mul ℂ ℂ) (volume : Measure ℝ) := by
    funext x
    rw [convolution_eq_swap]
    exact pair_translate_eq hφmem hψmem x
  have hcorec : HasCompactSupport core := by
    rw [hcore_eq]
    exact hφc.convolution (ContinuousLinearMap.mul ℂ ℂ) hψc
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

theorem apm_a97j03
    (p q : ℝ) (hp : 1 < p) (hq : 1 < q)
    (hpq : 1 / p + 1 / q = 1)
    (f g : ℝ → ℂ)
    (hf : MemLp f (ENNReal.ofReal p) volume)
    (hg : MemLp g (ENNReal.ofReal q) volume) :
    Continuous (apm_a97J03_convolution f g) ∧
      Tendsto (apm_a97J03_convolution f g) atTop (𝓝 0) ∧
      Tendsto (apm_a97J03_convolution f g) atBot (𝓝 0) := by
  have hpq' : p.HolderConjugate q := by
    rw [Real.holderConjugate_iff]
    refine ⟨hp, ?_⟩
    simpa only [one_div] using hpq
  have hc : Continuous (apm_a97J03_convolution f g) := by
    simpa only [apm_a97J03_convolution] using
      apm_a97J03_convolution_continuous hpq' hf hg
  have hv : Tendsto (apm_a97J03_convolution f g) (cocompact ℝ) (𝓝 0) := by
    simpa only [apm_a97J03_convolution] using
      apm_a97J03_convolution_tendsto_zero hpq' hf hg
  exact ⟨hc, hv.mono_left atTop_le_cocompact, hv.mono_left atBot_le_cocompact⟩

#print axioms apm_a97j03
