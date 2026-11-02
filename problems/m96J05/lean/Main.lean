import Mathlib

/-!
# APM m96J05

## Statement repairs

The malformed formula
`(f(x+ε-f(x-ε)))/2ε` is repaired to the symmetric difference quotient
`(f(x+ε)-f(x-ε))/(2ε)`, as required by the hint and supplied solution.

## Encoding questions

`L²(ℝ)` is taken over `ℂ`, the natural scalar field for the Fourier transform.
The difference quotient `apm_m96j05_D` and unit translation `apm_m96j05_T` are the
physical-space operators, built from translation on `L²`; `apm_m96j05_Tr_apply_ae` and
`apm_m96j05_D_apply_ae` pin them to the repaired formula almost everywhere.  The main
theorem is `apm_m96j05`.  `apm_m96j05_fourier` is the multiplier-side statement it is
derived from, by conjugation with the Fourier transform.
-/

open MeasureTheory Filter
open scoped FourierTransform SchwartzMap Topology

noncomputable section

abbrev apm_m96j05_L2 := Lp ℂ 2 (volume : Measure ℝ)

/-- Translation by `a` on `L²(ℝ, ℂ)`, with the convention
`(Tr a f)(x) = f(x + a)` almost everywhere. -/
def apm_m96j05_Tr (a : ℝ) :
    apm_m96j05_L2 →L[ℂ] apm_m96j05_L2 :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => x + a)
    (measurePreserving_add_right volume a)).toContinuousLinearMap

/-- The symmetric difference quotient built from translations. -/
def apm_m96j05_D (ε : ℝ) :
    apm_m96j05_L2 →L[ℂ] apm_m96j05_L2 :=
  ((2 * ε : ℝ) : ℂ)⁻¹ • (apm_m96j05_Tr ε - apm_m96j05_Tr (-ε))

/-- Unit translation on `L²(ℝ, ℂ)`. -/
def apm_m96j05_T : apm_m96j05_L2 →L[ℂ] apm_m96j05_L2 :=
  apm_m96j05_Tr 1

def apm_m96j05_phase (a ξ : ℝ) : ℂ :=
  Complex.exp (Complex.I * (2 * Real.pi * a * ξ))

def apm_m96j05_phaseLp (a : ℝ) : Lp ℂ ⊤ (volume : Measure ℝ) :=
  MemLp.toLp (apm_m96j05_phase a)
    (memLp_top_of_bound
      (by unfold apm_m96j05_phase; fun_prop) 1
      (.of_forall fun ξ => by
        simp [apm_m96j05_phase, Complex.norm_exp]))

lemma apm_m96j05_phaseLp_apply_ae (a : ℝ) :
    (fun ξ : ℝ => apm_m96j05_phaseLp a ξ) =ᵐ[volume]
      apm_m96j05_phase a := by
  rw [apm_m96j05_phaseLp]
  exact MemLp.coeFn_toLp _

/-- Multiplication by the Fourier phase corresponding to translation by `a`. -/
def apm_m96j05_Mphase (a : ℝ) :
    apm_m96j05_L2 →L[ℂ] apm_m96j05_L2 :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL volume ⊤ 2 2
    (apm_m96j05_phaseLp a)

lemma apm_m96j05_Mphase_apply_ae (a : ℝ) (f : apm_m96j05_L2) :
    (fun ξ : ℝ => apm_m96j05_Mphase a f ξ) =ᵐ[volume]
      fun ξ => apm_m96j05_phase a ξ * f ξ := by
  filter_upwards [ContinuousLinearMap.coeFn_holder (r := (2 : ENNReal))
      (ContinuousLinearMap.mul ℂ ℂ)
      (apm_m96j05_phaseLp a) f,
    apm_m96j05_phaseLp_apply_ae a] with ξ hmul hphase
  exact hmul.trans (congrArg (fun z : ℂ => z * f ξ) hphase)

lemma apm_m96j05_Tr_apply (a : ℝ) (f : apm_m96j05_L2) :
    apm_m96j05_Tr a f =
      Lp.compMeasurePreserving (fun x : ℝ => x + a)
        (measurePreserving_add_right volume a) f := rfl

lemma apm_m96j05_Tr_apply_ae (a : ℝ) (f : apm_m96j05_L2) :
    (fun x : ℝ => apm_m96j05_Tr a f x) =ᵐ[volume]
      fun x => f (x + a) := by
  exact Lp.coeFn_compMeasurePreserving f
    (measurePreserving_add_right volume a)

lemma apm_m96j05_D_apply_ae (ε : ℝ) (f : apm_m96j05_L2) :
    (fun x : ℝ => apm_m96j05_D ε f x) =ᵐ[volume]
      fun x => ((2 * ε : ℝ) : ℂ)⁻¹ * (f (x + ε) - f (x - ε)) := by
  filter_upwards [Lp.coeFn_smul (((2 * ε : ℝ) : ℂ)⁻¹)
      ((apm_m96j05_Tr ε) f - (apm_m96j05_Tr (-ε)) f),
    Lp.coeFn_sub (apm_m96j05_Tr ε f) (apm_m96j05_Tr (-ε) f),
    apm_m96j05_Tr_apply_ae ε f, apm_m96j05_Tr_apply_ae (-ε) f]
      with x hsmul hsub hpos hneg
  change (((((2 * ε : ℝ) : ℂ)⁻¹) •
    ((apm_m96j05_Tr ε) f - (apm_m96j05_Tr (-ε)) f) :
      apm_m96j05_L2) x) = _
  rw [hsmul]
  change ((2 * ε : ℝ) : ℂ)⁻¹ *
    (((apm_m96j05_Tr ε) f - (apm_m96j05_Tr (-ε)) f) x) = _
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hpos, hneg]
  congr 2

lemma apm_m96j05_fourier_Tr_eq (a : ℝ) (f : apm_m96j05_L2) :
    𝓕 (apm_m96j05_Tr a f) = apm_m96j05_Mphase a (𝓕 f) := by
  let p : apm_m96j05_L2 → Prop := fun g =>
    𝓕 (apm_m96j05_Tr a g) = apm_m96j05_Mphase a (𝓕 g)
  apply DenseRange.induction_on (p := p)
    (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ)
      (p := 2) ENNReal.ofNat_ne_top) f
  · apply isClosed_eq
    · exact (Lp.fourierTransformₗᵢ ℝ ℂ).continuous.comp
        (apm_m96j05_Tr a).continuous
    · exact (apm_m96j05_Mphase a).continuous.comp
        (Lp.fourierTransformₗᵢ ℝ ℂ).continuous
  intro g
  let ga : 𝓢(ℝ, ℂ) := g.compSubConstCLM ℂ (-a)
  have hgshift :
      (fun x : ℝ => (g.toLp 2 : apm_m96j05_L2) (x + a)) =ᵐ[volume]
        fun x => g (x + a) :=
    (g.coeFn_toLp 2 volume).comp_tendsto
      (measurePreserving_add_right volume a).quasiMeasurePreserving.tendsto_ae
  have htr : apm_m96j05_Tr a (g.toLp 2) = ga.toLp 2 := by
    apply Lp.ext
    filter_upwards [apm_m96j05_Tr_apply_ae a (g.toLp 2),
      hgshift, ga.coeFn_toLp 2 volume] with x htr hg hga
    rw [htr, hga, hg]
    simp [ga]
  change 𝓕 (apm_m96j05_Tr a (g.toLp 2)) =
    apm_m96j05_Mphase a (𝓕 (g.toLp 2))
  rw [htr, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [apm_m96j05_Mphase_apply_ae a ((𝓕 g).toLp 2),
    (𝓕 ga).coeFn_toLp 2 volume, (𝓕 g).coeFn_toLp 2 volume]
      with ξ hmul hga hg
  rw [hga, hmul, hg]
  have hfourier := congrFun
    (Fourier.fourierIntegral_comp_add_right
      Real.fourierChar volume (g : ℝ → ℂ) a) ξ
  have hinter (x y : ℝ) : inner ℝ x y = x * y := by
    change y * x = x * y
    ring
  have hphase : (Real.fourierChar (a * ξ) : ℂ) =
      apm_m96j05_phase a ξ := by
    simp only [Real.fourierChar_apply, apm_m96j05_phase]
    congr 1
    push_cast
    ring
  rw [Circle.smul_def, hphase] at hfourier
  rw [SchwartzMap.fourier_coe ga, SchwartzMap.fourier_coe g]
  simpa [ga, Real.fourier_eq,
    Fourier.fourierIntegral, VectorFourier.fourierIntegral, real_inner_comm,
    hinter]
    using hfourier

lemma apm_m96j05_fourier_Tr (a : ℝ) (f : apm_m96j05_L2) :
    (fun ξ : ℝ => 𝓕 (apm_m96j05_Tr a f) ξ) =ᵐ[volume]
      fun ξ => apm_m96j05_phase a ξ * 𝓕 f ξ := by
  rw [apm_m96j05_fourier_Tr_eq]
  exact apm_m96j05_Mphase_apply_ae a (𝓕 f)

def apm_m96j05_differenceSymbol (ε ξ : ℝ) : ℂ :=
  Complex.I * (Real.sin (2 * Real.pi * ε * ξ) / ε)

lemma apm_m96j05_phase_difference (ε ξ : ℝ) (hε : ε ≠ 0) :
    (((2 * ε : ℝ) : ℂ)⁻¹) *
        (apm_m96j05_phase ε ξ - apm_m96j05_phase (-ε) ξ) =
      apm_m96j05_differenceSymbol ε ξ := by
  rw [show apm_m96j05_phase ε ξ =
      Complex.exp (((2 * Real.pi * ε * ξ : ℝ) : ℂ) * Complex.I) by
    simp only [apm_m96j05_phase]; congr 1; push_cast; ring,
    show apm_m96j05_phase (-ε) ξ =
      Complex.exp ((-(2 * Real.pi * ε * ξ : ℝ) : ℂ) * Complex.I) by
    simp only [apm_m96j05_phase]; congr 1; push_cast; ring]
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  simp only [map_neg, Complex.cos_neg, Complex.sin_neg]
  simp only [apm_m96j05_differenceSymbol]
  rw [div_eq_mul_inv]
  push_cast
  field_simp
  ring

lemma apm_m96j05_fourier_D (ε : ℝ) (hε : ε ≠ 0)
    (f : apm_m96j05_L2) :
    (fun ξ : ℝ => 𝓕 (apm_m96j05_D ε f) ξ) =ᵐ[volume]
      fun ξ => apm_m96j05_differenceSymbol ε ξ * 𝓕 f ξ := by
  have hlin : 𝓕 (apm_m96j05_D ε f) =
      (((2 * ε : ℝ) : ℂ)⁻¹) •
        ((Lp.fourierTransformₗᵢ ℝ ℂ) (apm_m96j05_Tr ε f) -
          (Lp.fourierTransformₗᵢ ℝ ℂ) (apm_m96j05_Tr (-ε) f)) := by
    change (Lp.fourierTransformₗᵢ ℝ ℂ)
      (((((2 * ε : ℝ) : ℂ)⁻¹) •
        (apm_m96j05_Tr ε - apm_m96j05_Tr (-ε))) f) = _
    rw [ContinuousLinearMap.smul_apply, map_smul, ContinuousLinearMap.sub_apply,
      map_sub]
  rw [hlin]
  change (fun ξ : ℝ =>
    ((((2 * ε : ℝ) : ℂ)⁻¹) •
      (𝓕 (apm_m96j05_Tr ε f) - 𝓕 (apm_m96j05_Tr (-ε) f)) :
        apm_m96j05_L2) ξ) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_smul (((2 * ε : ℝ) : ℂ)⁻¹)
      (𝓕 (apm_m96j05_Tr ε f) - 𝓕 (apm_m96j05_Tr (-ε) f)),
    Lp.coeFn_sub (𝓕 (apm_m96j05_Tr ε f)) (𝓕 (apm_m96j05_Tr (-ε) f)),
    apm_m96j05_fourier_Tr ε f, apm_m96j05_fourier_Tr (-ε) f]
      with ξ hsmul hsub hp hn
  rw [hsmul]
  change (((2 * ε : ℝ) : ℂ)⁻¹) *
    ((𝓕 (apm_m96j05_Tr ε f) - 𝓕 (apm_m96j05_Tr (-ε) f)) ξ) = _
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hp, hn]
  rw [← sub_mul, ← mul_assoc, apm_m96j05_phase_difference ε ξ hε]

lemma apm_m96j05_fourier_D_pow_apply_ae (ε : ℝ) (hε : ε ≠ 0) :
    ∀ (n : ℕ) (f : apm_m96j05_L2),
      (fun ξ : ℝ => 𝓕 (((apm_m96j05_D ε) ^ n) f) ξ) =ᵐ[volume]
        fun ξ => apm_m96j05_differenceSymbol ε ξ ^ n * 𝓕 f ξ := by
  intro n
  induction n with
  | zero =>
      intro f
      simp
  | succ n ih =>
      intro f
      filter_upwards [apm_m96j05_fourier_D ε hε
        (((apm_m96j05_D ε) ^ n) f), ih f] with ξ hstep hpow
      simp only [pow_succ', ContinuousLinearMap.mul_apply] at hstep ⊢
      rw [hstep, hpow]
      ring

def apm_m96j05_shiftSymbol (ξ : ℝ) : ℂ :=
  Complex.exp (Complex.I * (2 * Real.pi * ξ))

/-- Both Fourier multipliers occurring in the dominated-convergence argument
have modulus one. -/
lemma apm_m96j05_symbol_norms (ε ξ : ℝ) :
    ‖Complex.exp (apm_m96j05_differenceSymbol ε ξ)‖ = 1 ∧
      ‖apm_m96j05_shiftSymbol ξ‖ = 1 := by
  constructor
  · rw [Complex.norm_exp]
    have hre : (apm_m96j05_differenceSymbol ε ξ).re = 0 := by
      simp only [apm_m96j05_differenceSymbol, Complex.mul_re, Complex.I_re,
        zero_mul, Complex.I_im, one_mul, zero_sub, neg_eq_zero]
      rw [← Complex.ofReal_div]
      exact Complex.ofReal_im _
    rw [hre, Real.exp_zero]
  · simp [apm_m96j05_shiftSymbol, Complex.norm_exp]

/-- The scalar difference symbol converges pointwise to the infinitesimal
translation symbol along the punctured neighborhood used in the theorem. -/
lemma apm_m96j05_differenceSymbol_tendsto (ξ : ℝ) :
    Tendsto (fun ε : ℝ => apm_m96j05_differenceSymbol ε ξ)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhds (Complex.I * (2 * Real.pi * ξ))) := by
  have hinner : HasDerivAt (fun ε : ℝ => 2 * Real.pi * ε * ξ)
      (2 * Real.pi * ξ) 0 := by
    convert ((hasDerivAt_id (x := (0 : ℝ))).const_mul (2 * Real.pi)).mul_const ξ using 1 <;>
      ring
  have hsin : HasDerivAt (fun ε : ℝ => Real.sin (2 * Real.pi * ε * ξ))
      (2 * Real.pi * ξ) 0 := by
    simpa using (Real.hasDerivAt_sin (2 * Real.pi * 0 * ξ)).comp 0 hinner
  have hslope := hsin.tendsto_slope
  have hquot : Tendsto (fun ε : ℝ => Real.sin (2 * Real.pi * ε * ξ) / ε)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (2 * Real.pi * ξ)) := by
    convert hslope using 1
    funext ε
    simp [slope, div_eq_inv_mul]
  have hI : Tendsto (fun _ : ℝ => Complex.I)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds Complex.I) := tendsto_const_nhds
  convert hI.mul hquot.ofReal using 1 <;>
    simp [apm_m96j05_differenceSymbol, Complex.ofReal_div]

/-- Exponentiating the preceding scalar limit gives exactly the translation
symbol. -/
lemma apm_m96j05_exp_differenceSymbol_tendsto (ξ : ℝ) :
    Tendsto (fun ε : ℝ => Complex.exp (apm_m96j05_differenceSymbol ε ξ))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (apm_m96j05_shiftSymbol ξ)) := by
  exact Complex.continuous_exp.continuousAt.tendsto.comp
    (apm_m96j05_differenceSymbol_tendsto ξ)

/-- Pointwise convergence after multiplying by an arbitrary Fourier datum. -/
lemma apm_m96j05_exp_differenceSymbol_mul_tendsto (ξ : ℝ) (z : ℂ) :
    Tendsto
      (fun ε : ℝ => Complex.exp (apm_m96j05_differenceSymbol ε ξ) * z)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhds (apm_m96j05_shiftSymbol ξ * z)) := by
  exact (apm_m96j05_exp_differenceSymbol_tendsto ξ).mul_const z

/-- Iterating an operator which is a.e. multiplication by `m` gives the
corresponding pointwise powers.  This is the finite-power bridge needed before
passing from the operator exponential series to the scalar exponential. -/
lemma apm_m96j05_pow_apply_ae
    (A : apm_m96j05_L2 →L[ℂ] apm_m96j05_L2) (m : ℝ → ℂ)
    (hA : ∀ f : apm_m96j05_L2,
      (fun ξ : ℝ => A f ξ) =ᵐ[volume] fun ξ => m ξ * f ξ) :
    ∀ (n : ℕ) (f : apm_m96j05_L2),
      (fun ξ : ℝ => (A ^ n) f ξ) =ᵐ[volume]
        fun ξ => m ξ ^ n * f ξ := by
  intro n
  induction n with
  | zero =>
      intro f
      simp
  | succ n ih =>
      intro f
      filter_upwards [hA ((A ^ n) f), ih f] with ξ hstep hpow
      simp only [pow_succ', ContinuousLinearMap.mul_apply] at hstep ⊢
      rw [hstep, hpow]
      ring

lemma apm_m96j05_finset_sum_apply_ae {ι : Type*}
    (v : ι → apm_m96j05_L2) (t : Finset ι) :
    (fun ξ : ℝ => (∑ i ∈ t, v i) ξ) =ᵐ[volume]
      fun ξ => ∑ i ∈ t, v i ξ := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simpa using (Lp.coeFn_zero ℂ (2 : ENNReal) (volume : Measure ℝ))
  | insert a t ha ih =>
      filter_upwards [Lp.coeFn_add (v a) (∑ i ∈ t, v i), ih] with ξ hadd hsum
      simp only [Finset.sum_insert ha]
      rw [hadd]
      change v a ξ + (∑ i ∈ t, v i) ξ = v a ξ + ∑ i ∈ t, v i ξ
      rw [hsum]

/-- Why this unblocks `apm_m96j05`: the finite-power identities above identify
every partial sum; this is the missing passage through the operator-norm
`tsum`, identifying the resulting `Lp` element almost everywhere with the
scalar exponential multiplier.  The compiled pointwise limit and modulus-one
bound can then be fed directly to `Lp` dominated convergence. -/
theorem apm_m96J05_bridge_1
    (D : ℝ → apm_m96j05_L2 →L[ℂ] apm_m96j05_L2)
    (hD : ∀ (ε : ℝ), ε ≠ 0 → ∀ f : apm_m96j05_L2,
      (fun ξ : ℝ => D ε f ξ) =ᵐ[volume]
        fun ξ => apm_m96j05_differenceSymbol ε ξ * f ξ)
    (ε : ℝ) (hε : ε ≠ 0) (f : apm_m96j05_L2) :
    (fun ξ : ℝ => NormedSpace.exp (D ε) f ξ) =ᵐ[volume]
      fun ξ => Complex.exp (apm_m96j05_differenceSymbol ε ξ) * f ξ := by
  let A := D ε
  let u : ℕ → apm_m96j05_L2 := fun n =>
    (NormedSpace.expSeries ℂ
      (apm_m96j05_L2 →L[ℂ] apm_m96j05_L2) n fun _ => A) f
  let s : ℕ → apm_m96j05_L2 := fun n => ∑ k ∈ Finset.range n, u k
  have hu : HasSum u (NormedSpace.exp A f) := by
    have h := (NormedSpace.expSeries_hasSum_exp (𝕂 := ℂ) A).map
      (ContinuousLinearMap.apply ℂ apm_m96j05_L2 f)
      (ContinuousLinearMap.apply ℂ apm_m96j05_L2 f).continuous
    simpa [u, Function.comp_def] using h
  have hs : Tendsto s atTop (nhds (NormedSpace.exp A f)) := by
    exact hu.tendsto_sum_nat
  obtain ⟨ns, hns, hsub⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hs).exists_seq_tendsto_ae
  have hpowers : ∀ᵐ ξ ∂volume, ∀ n : ℕ,
      (A ^ n) f ξ = apm_m96j05_differenceSymbol ε ξ ^ n * f ξ := by
    rw [ae_all_iff]
    intro n
    exact apm_m96j05_pow_apply_ae A
      (apm_m96j05_differenceSymbol ε) (hD ε hε) n f
  have hsums : ∀ᵐ ξ ∂volume, ∀ n : ℕ,
      s n ξ = ∑ k ∈ Finset.range n, u k ξ := by
    rw [ae_all_iff]
    intro n
    exact apm_m96j05_finset_sum_apply_ae u (Finset.range n)
  have hterms : ∀ᵐ ξ ∂volume, ∀ n : ℕ,
      u n ξ = (n.factorial : ℂ)⁻¹ *
        apm_m96j05_differenceSymbol ε ξ ^ n * f ξ := by
    rw [ae_all_iff]
    intro n
    rw [show u n = (n.factorial : ℂ)⁻¹ • (A ^ n) f by
      simp [u, NormedSpace.expSeries_apply_eq]]
    filter_upwards [Lp.coeFn_smul (n.factorial : ℂ)⁻¹ ((A ^ n) f),
      apm_m96j05_pow_apply_ae A (apm_m96j05_differenceSymbol ε)
        (hD ε hε) n f] with ξ hsmul hpow
    rw [hsmul]
    change (n.factorial : ℂ)⁻¹ * ((A ^ n) f ξ) = _
    rw [hpow]
    ring
  filter_upwards [hsub, hpowers, hsums, hterms] with ξ hlim hpow hsum hterm
  have hscalar : Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range n,
        (k.factorial : ℂ)⁻¹ *
          apm_m96j05_differenceSymbol ε ξ ^ k * f ξ)
      atTop
      (nhds (Complex.exp (apm_m96j05_differenceSymbol ε ξ) * f ξ)) := by
    have he := (NormedSpace.expSeries_hasSum_exp (𝕂 := ℂ)
      (apm_m96j05_differenceSymbol ε ξ)).mul_right (f ξ)
    simpa only [NormedSpace.expSeries_apply_eq, smul_eq_mul,
      mul_assoc, ← Complex.exp_eq_exp_ℂ] using he.tendsto_sum_nat
  apply tendsto_nhds_unique hlim
  have hc := hscalar.comp hns.tendsto_atTop
  apply hc.congr'
  filter_upwards [] with n
  symm
  change s (ns n) ξ = _
  rw [hsum]
  simp only [u]
  apply Finset.sum_congr rfl
  intro k hk
  exact hterm k

theorem apm_m96j05_fourier
    (D : ℝ → apm_m96j05_L2 →L[ℂ] apm_m96j05_L2)
    (T : apm_m96j05_L2 →L[ℂ] apm_m96j05_L2)
    (hD : ∀ (ε : ℝ), ε ≠ 0 → ∀ f : apm_m96j05_L2,
      (fun ξ : ℝ => D ε f ξ) =ᵐ[volume]
        fun ξ => apm_m96j05_differenceSymbol ε ξ * f ξ)
    (hT : ∀ f : apm_m96j05_L2,
      (fun ξ : ℝ => T f ξ) =ᵐ[volume]
        fun ξ => apm_m96j05_shiftSymbol ξ * f ξ) :
    ∀ f : apm_m96j05_L2,
      Tendsto (fun ε : ℝ => NormedSpace.exp (D ε) f)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (T f)) := by
  intro f
  rw [tendsto_iff_seq_tendsto]
  intro ε hε
  have hev : ∀ᶠ n in atTop, ε n ≠ 0 :=
    hε.eventually (self_mem_nhdsWithin :
      ({0} : Set ℝ)ᶜ ∈ nhdsWithin 0 ({0} : Set ℝ)ᶜ)
  rcases (eventually_atTop.1 hev) with ⟨k, hk⟩
  rw [← tendsto_add_atTop_iff_nat k]
  let e : ℕ → ℝ := fun n => ε (n + k)
  have he : Tendsto e atTop (nhdsWithin 0 ({0} : Set ℝ)ᶜ) :=
    hε.comp (tendsto_add_atTop_nat k)
  change Tendsto (fun n => NormedSpace.exp (D (e n)) f) atTop (nhds (T f))
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'
    (fun n => NormedSpace.exp (D (e n)) f) (T f)).2
  let q : ℕ → ℝ → ℂ := fun n ξ =>
    NormedSpace.exp (D (e n)) f ξ - T f ξ
  let F : ℕ → ℝ → ENNReal := fun n ξ => ‖q n ξ‖ₑ ^ (2 : ℝ)
  let B : ℝ → ENNReal := fun ξ => ‖(2 : ℂ) * f ξ‖ₑ ^ (2 : ℝ)
  have hεne : ∀ n, e n ≠ 0 := fun n => hk (n + k) (Nat.le_add_left k n)
  have hqae : ∀ᵐ ξ ∂volume, ∀ n : ℕ,
      q n ξ =
        (Complex.exp (apm_m96j05_differenceSymbol (e n) ξ) -
          apm_m96j05_shiftSymbol ξ) * f ξ := by
    rw [ae_all_iff]
    intro n
    filter_upwards [apm_m96J05_bridge_1 D hD (e n) (hεne n) f,
      hT f] with ξ hexp hshift
    simp only [q]
    rw [hexp, hshift]
    ring
  have hFmeas : ∀ n, AEMeasurable (F n) volume := by
    intro n
    exact ((Lp.memLp (NormedSpace.exp (D (e n)) f)).sub
      (Lp.memLp (T f))).1.enorm.pow_const _
  have hbound : ∀ n, F n ≤ᵐ[volume] B := by
    intro n
    filter_upwards [hqae] with ξ hq
    simp only [F, B, hq]
    have hex := (apm_m96j05_symbol_norms (e n) ξ).1
    have hs := (apm_m96j05_symbol_norms (e n) ξ).2
    rw [enorm_mul]
    apply ENNReal.rpow_le_rpow
    rw [enorm_mul]
    apply mul_le_mul_right'
    · rw [enorm_le_iff_norm_le]
      simpa using (show ‖Complex.exp (apm_m96j05_differenceSymbol (e n) ξ) -
      apm_m96j05_shiftSymbol ξ‖ ≤ 2 by
        calc
          _ ≤ ‖Complex.exp (apm_m96j05_differenceSymbol (e n) ξ)‖ +
              ‖apm_m96j05_shiftSymbol ξ‖ := norm_sub_le _ _
          _ = 2 := by rw [hex, hs]; norm_num)
    · positivity
  have hBfin : ∫⁻ ξ, B ξ ∂volume ≠ ⊤ := by
    have hm := (Lp.memLp ((2 : ℂ) • f)).2
    apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num : (2 : ENNReal) ≠ 0)
      (by norm_num : (2 : ENNReal) ≠ ⊤)).1 at hm
    apply ne_of_lt
    refine (lintegral_congr_ae ?_).trans_lt hm
    filter_upwards [Lp.coeFn_smul (2 : ℂ) f] with ξ hsmul
    rw [hsmul]
    simp [B, enorm_smul, smul_eq_mul]
  have hFlim : ∀ᵐ ξ ∂volume,
      Tendsto (fun n => F n ξ) atTop (nhds 0) := by
    filter_upwards [hqae] with ξ hq
    have hsym := apm_m96j05_exp_differenceSymbol_mul_tendsto ξ (f ξ)
    have hseq := hsym.comp he
    have hzero : Tendsto (fun n => q n ξ) atTop (nhds 0) := by
      have hz := hseq.sub_const (apm_m96j05_shiftSymbol ξ * f ξ)
      have hz' : Tendsto
          (fun n => ((fun ε => Complex.exp
            (apm_m96j05_differenceSymbol ε ξ) * f ξ) ∘ e) n -
              apm_m96j05_shiftSymbol ξ * f ξ)
          atTop (nhds 0) := by simpa using hz
      apply hz'.congr'
      filter_upwards [] with n
      rw [hq n]
      simp only [Function.comp_apply]
      ring
    have hen := hzero.enorm
    simp only [enorm_zero] at hen
    have hc : Continuous (fun a : ENNReal => a ^ (2 : ℝ)) :=
      ENNReal.continuous_rpow_const
    simpa [F] using (hc.tendsto 0 |>.comp hen)
  have hint := tendsto_lintegral_of_dominated_convergence'
    B hFmeas hbound hBfin hFlim
  have hint' : Tendsto (fun n => ∫⁻ a, F n a ∂volume) atTop (nhds 0) := by
    simpa using hint
  have hc : Continuous (fun a : ENNReal => a ^ (1 / (2 : ℝ))) :=
    ENNReal.continuous_rpow_const
  have hrpow := hc.tendsto 0 |>.comp hint'
  convert hrpow using 1
  · funext n
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ENNReal) ≠ 0)
      (by norm_num : (2 : ENNReal) ≠ ⊤)]
    congr 1
  · simp

/-- The Fourier transform regarded as a continuous linear equivalence. -/
def apm_m96j05_Φ : apm_m96j05_L2 ≃L[ℂ] apm_m96j05_L2 :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).toContinuousLinearEquiv

def apm_m96j05_M (ε : ℝ) :
    apm_m96j05_L2 →L[ℂ] apm_m96j05_L2 :=
  (apm_m96j05_Φ.conjContinuousAlgEquiv) (apm_m96j05_D ε)

def apm_m96j05_N : apm_m96j05_L2 →L[ℂ] apm_m96j05_L2 :=
  (apm_m96j05_Φ.conjContinuousAlgEquiv) apm_m96j05_T

lemma apm_m96j05_M_apply_ae (ε : ℝ) (hε : ε ≠ 0)
    (g : apm_m96j05_L2) :
    (fun ξ : ℝ => apm_m96j05_M ε g ξ) =ᵐ[volume]
      fun ξ => apm_m96j05_differenceSymbol ε ξ * g ξ := by
  change (fun ξ : ℝ =>
    apm_m96j05_Φ (apm_m96j05_D ε (apm_m96j05_Φ.symm g)) ξ) =ᵐ[volume] _
  have hsym : apm_m96j05_Φ (apm_m96j05_Φ.symm g) = g :=
    apm_m96j05_Φ.apply_symm_apply g
  conv_rhs => rw [← hsym]
  change (fun ξ : ℝ => 𝓕 (apm_m96j05_D ε (apm_m96j05_Φ.symm g)) ξ) =ᵐ[volume]
    fun ξ => apm_m96j05_differenceSymbol ε ξ *
      𝓕 (apm_m96j05_Φ.symm g) ξ
  exact apm_m96j05_fourier_D ε hε (apm_m96j05_Φ.symm g)

lemma apm_m96j05_N_apply_ae (g : apm_m96j05_L2) :
    (fun ξ : ℝ => apm_m96j05_N g ξ) =ᵐ[volume]
      fun ξ => apm_m96j05_shiftSymbol ξ * g ξ := by
  change (fun ξ : ℝ =>
    apm_m96j05_Φ (apm_m96j05_T (apm_m96j05_Φ.symm g)) ξ) =ᵐ[volume] _
  have hsym : apm_m96j05_Φ (apm_m96j05_Φ.symm g) = g :=
    apm_m96j05_Φ.apply_symm_apply g
  conv_rhs => rw [← hsym]
  change (fun ξ : ℝ => 𝓕 (apm_m96j05_Tr 1 (apm_m96j05_Φ.symm g)) ξ) =ᵐ[volume]
    fun ξ => apm_m96j05_shiftSymbol ξ * 𝓕 (apm_m96j05_Φ.symm g) ξ
  simpa [apm_m96j05_shiftSymbol, apm_m96j05_phase] using
    (apm_m96j05_fourier_Tr 1 (apm_m96j05_Φ.symm g))

lemma apm_m96j05_exp_conj (A : apm_m96j05_L2 →L[ℂ] apm_m96j05_L2) :
    NormedSpace.exp
        ((apm_m96j05_Φ.conjContinuousAlgEquiv) A) =
      (apm_m96j05_Φ.conjContinuousAlgEquiv) (NormedSpace.exp A) := by
  symm
  exact NormedSpace.map_exp_of_mem_ball (𝕂 := ℂ)
    (apm_m96j05_Φ.conjContinuousAlgEquiv)
    apm_m96j05_Φ.conjContinuousAlgEquiv.continuous A
    (by rw [NormedSpace.expSeries_radius_eq_top]; exact edist_lt_top _ _)

theorem apm_m96j05 (f : apm_m96j05_L2) :
    Tendsto (fun ε : ℝ => NormedSpace.exp (apm_m96j05_D ε) f)
      (𝓝[≠] 0) (𝓝 (apm_m96j05_T f)) := by
  have hconv := apm_m96j05_fourier apm_m96j05_M apm_m96j05_N
    apm_m96j05_M_apply_ae apm_m96j05_N_apply_ae (apm_m96j05_Φ f)
  have hmapped := apm_m96j05_Φ.symm.continuous.tendsto
    (apm_m96j05_N (apm_m96j05_Φ f)) |>.comp hconv
  convert hmapped using 1
  · funext ε
    change NormedSpace.exp (apm_m96j05_D ε) f =
      apm_m96j05_Φ.symm
        (NormedSpace.exp ((apm_m96j05_Φ.conjContinuousAlgEquiv)
          (apm_m96j05_D ε)) (apm_m96j05_Φ f))
    rw [apm_m96j05_exp_conj]
    simp [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply]
  · simp [apm_m96j05_N, ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply]
