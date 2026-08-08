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
  sorry
