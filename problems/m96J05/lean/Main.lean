import Mathlib

/-!
# APM m96J05

## Statement repairs

The malformed formula
`(f(x+ε-f(x-ε)))/2ε` is repaired to the symmetric difference quotient
`(f(x+ε)-f(x-ε))/(2ε)`, as required by the hint and supplied solution.

## Encoding questions

`L²(ℝ)` is taken over `ℂ`, the natural scalar field for the Fourier transform.
The difference quotient and unit translation are represented in Fourier coordinates
and pinned almost everywhere to their exact multipliers; no pointwise representative
of an `L²` equivalence class is treated as canonical.
-/

open MeasureTheory Filter

noncomputable section

abbrev apm_m96j05_L2 := Lp ℂ 2 (volume : Measure ℝ)

def apm_m96j05_differenceSymbol (ε ξ : ℝ) : ℂ :=
  Complex.I * (Real.sin (ε * ξ) / ε)

def apm_m96j05_shiftSymbol (ξ : ℝ) : ℂ :=
  Complex.exp (Complex.I * ξ)

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
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Complex.I * ξ)) := by
  have hinner : HasDerivAt (fun ε : ℝ => ε * ξ) ξ 0 := by
    simpa using (hasDerivAt_id (x := (0 : ℝ))).mul_const ξ
  have hsin : HasDerivAt (fun ε : ℝ => Real.sin (ε * ξ)) ξ 0 := by
    simpa using (Real.hasDerivAt_sin (0 * ξ)).comp 0 hinner
  have hslope := hsin.tendsto_slope
  have hquot : Tendsto (fun ε : ℝ => Real.sin (ε * ξ) / ε)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds ξ) := by
    convert hslope using 1
    funext ε
    simp [slope, div_eq_inv_mul]
  convert tendsto_const_nhds.mul hquot.ofReal using 1 <;>
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

theorem apm_m96j05
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
  /-
  PARTIAL (operator exponential versus a.e. `Lp` multipliers).  The helper
  `apm_m96j05_symbol_norms` proves the uniform modulus-one estimate for both
  scalar exponentials, which supplies the domination bound.  The scalar
  analytic part is available: for each `ξ`,
  `sin (ε * ξ) / ε → ξ` on the punctured neighborhood of zero,
  `Complex.exp (I * sin (ε * ξ) / ε) → Complex.exp (I * ξ)`, and both
  exponentials have norm one.  Mathlib's filter-form dominated convergence
  and `Lp.tendsto_Lp_iff_tendsto_eLpNorm` can then prove the final `L²`
  convergence once the two `Lp` elements are identified with these
  pointwise multipliers.

  The missing load-bearing lemma is that an operator characterized only by
  `hD` as multiplication a.e. has Banach-algebra exponential characterized
  a.e. by the scalar exponential:

  `NormedSpace.exp (D ε) f =ᵐ exp (differenceSymbol ε ·) * f`.

  Mathlib supplies `NormedSpace.exp_eq_tsum` and `map_exp` for continuous ring
  homomorphisms.  Point evaluation is not a well-defined, let alone
  continuous, ring homomorphism on `Lp`, so `map_exp` cannot be applied to
  `D ε` pointwise.  Expanding the operator power series directly requires
  proving by induction that every `(D ε)^k` is the multiplier by `mε^k`,
  intersecting the countably many a.e. identities, proving convergence of
  the representative scalar series in `L²`, and identifying its `Lp` limit
  with application of the operator-norm series.  A cleaner route would first
  construct the continuous algebra homomorphism from bounded measurable
  multipliers (`L∞`) to continuous operators on `L²`; no such packaged API or
  corpus construction was found.

  `LEMMA-INDEX.md` supplied strong `L²` translation continuity from
  `ConstructionTargets.L2Translation` and several approximate-identity
  convergence results, but these concern physical translations rather than
  exponentials of multiplier operators.  Completed sibling `a93A02` gives a
  Vitali-style sequence theorem, not the punctured real filter or multiplier
  identification.  Partial sibling `m95J03` exposes the same
  `NormedSpace.exp` power-series API but does not prove an infinite-dimensional
  multiplier result.  `ConstructionTargets.KernelAverage`, the other
  `ConstructionTargets/` modules, `YoungL2.lean`, and the fully closed artifact
  scan yielded no missing homomorphism.  The frozen statement appears sound;
  the unformalized multiplier-exponential interface is the blocker.

  Closer hop 1 additionally reduced the scalar quotient limit to
  `Real.hasDerivAt_sin 0 |>.tendsto_slope` and inspected
  `NormedSpace.exp_continuousMap_eq`, which proves pointwise compatibility of
  exponential for the Banach algebra of continuous functions.  That theorem
  cannot be transported here: the symbols are merely bounded measurable
  functions on an unbounded domain, and their multiplication operators act on
  `Lp`; neither point evaluation nor a continuous-function coercion is
  available for `Lp` equivalence classes.  Mathlib's distributional Fourier
  multiplier API acts on Schwartz maps and tempered distributions, not as the
  required bounded-multiplier algebra homomorphism into `L² →L L²`.  Thus the
  original a.e.-power-series bridge remains open; the statement is unchanged.

  CLOSER HOP 2 compiles the complete scalar convergence pipeline rather than
  merely citing the sine derivative. `apm_m96j05_differenceSymbol_tendsto`
  derives the punctured-filter quotient limit from
  `HasDerivAt.tendsto_slope`; `apm_m96j05_exp_differenceSymbol_tendsto`
  transports it through the complex exponential and identifies the result
  with `shiftSymbol`; and `apm_m96j05_exp_differenceSymbol_mul_tendsto`
  proves pointwise convergence after multiplication by arbitrary Fourier data.
  Together with `apm_m96j05_symbol_norms`, every scalar and domination input
  for an `Lp` dominated-convergence proof is therefore closed.

  The remaining boundary is now exclusively operator-to-representative
  identification: prove that `NormedSpace.exp (D ε) f` is a.e. the scalar
  exponential multiplier. Renewed inspection of the `Lp` holder/smul APIs and
  the multiplier-related siblings found no bounded-function multiplication
  algebra homomorphism, so the countable a.e. operator-power-series assembly
  remains honestly open.

  CLOSER HOP 3 goes beyond that search by proving the finite-power part of the
  assembly directly. `apm_m96j05_pow_apply_ae` shows, by induction and finite
  intersection of the supplied a.e. identities, that every operator power
  `(D ε)^n` acts as multiplication by `differenceSymbol ε ξ ^ n`. Thus no
  multiplier algebra homomorphism is needed for polynomial approximants.
  The remaining bridge is specifically passage to the infinite series:
  reconcile the operator-norm `tsum` defining `NormedSpace.exp` with an a.e.
  representative of the scalar exponential series, then invoke the compiled
  dominated-convergence data. Searches of the `tsum`/`Lp` representative APIs
  found no theorem commuting a countable operator series with representatives,
  so this final bridge remains honestly open; the frozen statement is unchanged.
  -/
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
