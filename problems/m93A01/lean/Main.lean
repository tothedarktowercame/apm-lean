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

/-- A compact operator cannot send a sequence in the closed unit ball to a
uniformly separated sequence. This is the common final step for the two
noncompactness clauses below. -/
lemma apm_m93A01_not_compact_of_separated_unit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : E →L[ℂ] E) (u : ℕ → E)
    (hu : ∀ n, ‖u n‖ ≤ 1)
    (hsep : ∀ n m, n ≠ m → 1 ≤ dist (A (u n)) (A (u m))) :
    ¬ IsCompactOperator A := by
  intro hcompact
  obtain ⟨K, hK, hAK⟩ := hcompact.image_closedBall_subset_compact 1
  have hmem : ∀ n, A (u n) ∈ K := by
    intro n
    apply hAK
    exact ⟨u n, by simpa [Metric.mem_closedBall, dist_eq_norm] using hu n, rfl⟩
  obtain ⟨x, hx, φ, hφ, htend⟩ := hK.tendsto_subseq hmem
  have hcauchy : CauchySeq (A ∘ u ∘ φ) := htend.cauchySeq
  obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp hcauchy) 1 zero_lt_one
  have hlt := hN N le_rfl (N + 1) (Nat.le_succ N)
  have hne : φ N ≠ φ (N + 1) := ne_of_lt (hφ (Nat.lt_succ_self N))
  have hge := hsep (φ N) (φ (N + 1)) hne
  exact (not_lt_of_ge hge) (by simpa [Function.comp_apply] using hlt)

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
  CLOSER HOP 1 (partial). The common sequential obstruction for both
  noncompactness clauses is now compiled as
  `apm_m93A01_not_compact_of_separated_unit`, adapted from solved sibling
  `m99A03`. It reduces each negative clause to the explicit bounded separated
  witnesses described below.

  Searches of Mathlib found the
  abstract characterizations in `Analysis.Normed.Operator.Compact`, but no
  theorem characterizing compact diagonal multipliers on `lp`, and no theorem
  showing that a nonzero multiplication operator on nonatomic `Lp` is
  noncompact.

  Renewed searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, solved
  Fourier/operator artifacts, Mathlib source, and git history found no
  diagonal-multiplier theorem. A local proof must construct finite-coordinate truncation operators on
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
