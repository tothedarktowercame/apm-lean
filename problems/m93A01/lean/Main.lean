import Mathlib

/-!
# APM m93A01: compact Sobolev embeddings and derivative maps

## Statement repairs

None.

## Encoding questions

Mathlib presently has no general Sobolev-space type. Rather than replace the
problem by an unrelated scalar shadow, this statement uses the exact Fourier
models induced by the printed Sobolev norms. On the circle, `H¹`, `H²`, and
`L²` are identified isometrically with weighted copies of `ℓ²(ℤ,ℂ)`; the
three operators are pinned below by their exact diagonal multipliers. On the
line, the Fourier model is `L²(ℝ,ℂ)`, and the inclusion is pinned almost
everywhere by the multiplier `(1+ξ²)⁻¹ᐟ²`. Thus the discrete/continuous
spectrum distinction central to the problem remains explicit.

Because the four maps are supplied as continuous linear maps, their requested
boundedness is encoded in their types; the conclusion records precisely which
are compact.
-/

noncomputable section

open MeasureTheory

abbrev apm_m93A01_l2Z := lp (fun _ : ℤ => ℂ) 2
abbrev apm_m93A01_l2R := Lp ℂ 2 (volume : Measure ℝ)

/-- Fourier multiplier for `H¹(S¹) ↪ L²(S¹)` after isometric weighting. -/
def apm_m93A01_circleInclCoeff (n : ℤ) : ℂ :=
  ((Real.sqrt (1 + (n : ℝ) ^ 2))⁻¹ : ℝ)

/-- Fourier multiplier for `D : H¹(S¹) → L²(S¹)`. -/
def apm_m93A01_circleDerivH1Coeff (n : ℤ) : ℂ :=
  Complex.I * (n : ℂ) / (Real.sqrt (1 + (n : ℝ) ^ 2) : ℂ)

/-- Fourier multiplier for `D : H²(S¹) → L²(S¹)` under the printed norm. -/
def apm_m93A01_circleDerivH2Coeff (n : ℤ) : ℂ :=
  Complex.I * (n : ℂ) /
    (Real.sqrt (1 + (n : ℝ) ^ 2 + (n : ℝ) ^ 4) : ℂ)

/-- Fourier multiplier for `H¹(ℝ) ↪ L²(ℝ)` after isometric weighting. -/
def apm_m93A01_realInclCoeff (ξ : ℝ) : ℂ :=
  ((Real.sqrt (1 + ξ ^ 2))⁻¹ : ℝ)

theorem apm_m93a01
    (ιS1 D1 D2 : apm_m93A01_l2Z →L[ℂ] apm_m93A01_l2Z)
    (ιR : apm_m93A01_l2R →L[ℂ] apm_m93A01_l2R)
    (hιS1 : ∀ (f : apm_m93A01_l2Z) (n : ℤ),
      ιS1 f n = apm_m93A01_circleInclCoeff n * f n)
    (hD1 : ∀ (f : apm_m93A01_l2Z) (n : ℤ),
      D1 f n = apm_m93A01_circleDerivH1Coeff n * f n)
    (hD2 : ∀ (f : apm_m93A01_l2Z) (n : ℤ),
      D2 f n = apm_m93A01_circleDerivH2Coeff n * f n)
    (hιR : ∀ f : apm_m93A01_l2R,
      (fun ξ : ℝ => ιR f ξ) =ᵐ[volume]
        fun ξ => apm_m93A01_realInclCoeff ξ * f ξ) :
    IsCompactOperator ιS1 ∧
    ¬ IsCompactOperator ιR ∧
    ¬ IsCompactOperator D1 ∧
    IsCompactOperator D2 := by
  /-
  SKIPPED (compact multiplier API boundary). Searches of Mathlib found the
  abstract characterizations in `Analysis.Normed.Operator.Compact`, but no
  theorem characterizing compact diagonal multipliers on `lp`, and no theorem
  showing that a nonzero multiplication operator on nonatomic `Lp` is
  noncompact.

  A local proof must construct finite-coordinate truncation operators on
  `lp (fun _ : ℤ ⇒ ℂ) 2`, prove their finite rank and operator-norm
  convergence for the two decaying symbols, and build normalized coordinate
  witnesses for noncompactness of `D1`. For `ιR`, the a.e. multiplier identity
  must be combined with infinitely many disjoint positive-measure sets on
  which `(1 + ξ²)⁻¹ᐟ²` is bounded below, yielding a separated bounded
  sequence in the image. None of the solved siblings provides these exact
  `lp`/`Lp` operator constructions, so no sibling code was reused and the
  frozen statement was left unchanged.
  -/
  sorry
