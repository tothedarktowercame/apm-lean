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

/-- The same compactness obstruction with an arbitrary positive separation
constant. This avoids an artificial normalization of the witnesses. -/
lemma apm_m93A01_not_compact_of_pos_separated_unit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : E →L[ℂ] E) (u : ℕ → E) {δ : ℝ} (hδ : 0 < δ)
    (hu : ∀ n, ‖u n‖ ≤ 1)
    (hsep : ∀ n m, n ≠ m → δ ≤ dist (A (u n)) (A (u m))) :
    ¬ IsCompactOperator A := by
  intro hcompact
  obtain ⟨K, hK, hAK⟩ := hcompact.image_closedBall_subset_compact 1
  have hmem : ∀ n, A (u n) ∈ K := fun n ↦ hAK ⟨u n, by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hu n, rfl⟩
  obtain ⟨x, hx, ψ, hψ, htend⟩ := hK.tendsto_subseq hmem
  have hcauchy : CauchySeq (A ∘ u ∘ ψ) := htend.cauchySeq
  obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp hcauchy) δ hδ
  have hlt := hN N le_rfl (N + 1) (Nat.le_succ N)
  have hne : ψ N ≠ ψ (N + 1) := ne_of_lt (hψ (Nat.lt_succ_self N))
  exact (not_lt_of_ge (hsep (ψ N) (ψ (N + 1)) hne))
    (by simpa [Function.comp_apply] using hlt)

/-- The `H¹` derivative symbol is uniformly bounded below on the strictly
positive integer frequencies. -/
lemma apm_m93A01_circleDerivH1Coeff_lower (n : ℕ) :
    (1 / 2 : ℝ) ≤ ‖apm_m93A01_circleDerivH1Coeff (n + 1)‖ := by
  rw [apm_m93A01_circleDerivH1Coeff, norm_div, norm_mul, Complex.norm_I]
  simp only [one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have hn : (1 : ℝ) ≤ n + 1 := by norm_num
  rw [norm_intCast_eq_abs_mul_norm_one ℂ, norm_one, mul_one,
    abs_of_nonneg (by omega : (0 : ℤ) ≤ (n : ℤ) + 1)]
  norm_num [Int.cast_add, Int.cast_natCast]
  have hspos : 0 < Real.sqrt (1 + ((n : ℝ) + 1) ^ 2) := by positivity
  rw [le_div_iff₀ hspos]
  have hs : Real.sqrt (1 + ((n : ℝ) + 1) ^ 2) ≤ 2 * ((n : ℝ) + 1) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith [sq_nonneg ((n : ℝ))]
  linarith

/-- The standard coordinate vectors in the Fourier `ℓ²` model are unit
vectors.  This is the bounded sequence used for the derivative obstruction. -/
lemma apm_m93A01_norm_single (n : ℤ) :
    ‖(lp.single 2 n (1 : ℂ) : apm_m93A01_l2Z)‖ = 1 := by
  rw [lp.norm_single (hp := by norm_num)]
  norm_num

/-- A continuous diagonal multiplier acts on a coordinate vector by scalar
multiplication.  This isolates the `lp` bookkeeping from the remaining scalar
estimate for the `H¹` derivative symbol. -/
lemma apm_m93A01_diagonal_single
    (A : apm_m93A01_l2Z →L[ℂ] apm_m93A01_l2Z) (c : ℤ → ℂ)
    (hA : ∀ (f : apm_m93A01_l2Z) (n : ℤ), A f n = c n * f n)
    (n : ℤ) :
    A (lp.single 2 n (1 : ℂ)) = c n • lp.single 2 n (1 : ℂ) := by
  ext j
  rw [hA]
  by_cases h : j = n
  · subst j
    simp
  · rw [lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 n (1 : ℂ) h]
    change c j * 0 = c n * (lp.single 2 n (1 : ℂ) : apm_m93A01_l2Z) j
    rw [lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 n (1 : ℂ) h]
    simp

/-- Consequently, the norm of a diagonal multiplier on a unit coordinate is
exactly the norm of its symbol at that coordinate. -/
lemma apm_m93A01_norm_diagonal_single
    (A : apm_m93A01_l2Z →L[ℂ] apm_m93A01_l2Z) (c : ℤ → ℂ)
    (hA : ∀ (f : apm_m93A01_l2Z) (n : ℤ), A f n = c n * f n)
    (n : ℤ) :
    ‖A (lp.single 2 n (1 : ℂ))‖ = ‖c n‖ := by
  rw [apm_m93A01_diagonal_single A c hA n, norm_smul,
    apm_m93A01_norm_single, mul_one]

/-- The `H¹` derivative multiplier is noncompact: positive-frequency unit
coordinates stay uniformly separated.  Looking at just the first coordinate
of each difference avoids any closed formula for the two-coordinate norm. -/
lemma apm_m93A01_circleDerivH1_not_compact
    (D1 : apm_m93A01_l2Z →L[ℂ] apm_m93A01_l2Z)
    (hD1 : ∀ (f : apm_m93A01_l2Z) (n : ℤ),
      D1 f n = apm_m93A01_circleDerivH1Coeff n * f n) :
    ¬ IsCompactOperator D1 := by
  apply apm_m93A01_not_compact_of_pos_separated_unit D1
    (fun n ↦ lp.single 2 ((n : ℤ) + 1) (1 : ℂ)) (δ := 1 / 2) (by norm_num)
  · intro n
    rw [apm_m93A01_norm_single]
  · intro n m hnm
    rw [dist_eq_norm]
    have hidx : (m : ℤ) + 1 ≠ (n : ℤ) + 1 := by
      exact fun h ↦ hnm (by exact_mod_cast (add_right_cancel h).symm)
    have hcoord := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
      (D1 (lp.single 2 ((n : ℤ) + 1) (1 : ℂ)) -
        D1 (lp.single 2 ((m : ℤ) + 1) (1 : ℂ))) ((n : ℤ) + 1)
    change ‖D1 (lp.single 2 ((n : ℤ) + 1) (1 : ℂ)) ((n : ℤ) + 1) -
      D1 (lp.single 2 ((m : ℤ) + 1) (1 : ℂ)) ((n : ℤ) + 1)‖ ≤ _ at hcoord
    rw [hD1, hD1, lp.single_apply,
      lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 ((m : ℤ) + 1) (1 : ℂ) hidx.symm]
      at hcoord
    simp at hcoord
    exact (apm_m93A01_circleDerivH1Coeff_lower n).trans hcoord

/-- Why this unblocks `apm_m93a01`: this is exactly the real-line inclusion
clause.  Its proof constructs normalized indicators of countably many
pairwise-disjoint positive finite-volume subsets of a bounded interval, where
`apm_m93A01_realInclCoeff` is uniformly bounded below; the pinned a.e.
multiplier identity then sends them to a uniformly separated sequence. -/
theorem apm_m93A01_bridge_1
    (A : apm_m93A01_l2R →L[ℂ] apm_m93A01_l2R)
    (hA : ∀ f : apm_m93A01_l2R,
      (fun ξ : ℝ ↦ A f ξ) =ᵐ[volume]
        fun ξ ↦ apm_m93A01_realInclCoeff ξ * f ξ) :
    ¬ IsCompactOperator A := by
  sorry

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

  CLOSER HOP 2 (partial). The `lp.single` coordinate route is now compiled
  through `apm_m93A01_norm_single`, `apm_m93A01_diagonal_single`, and
  `apm_m93A01_norm_diagonal_single`. Thus the proposed witnesses are proved
  to lie in the unit ball, every operator satisfying a frozen diagonal
  identity acts on them by the corresponding scalar symbol, and the image
  norm is exactly the symbol norm. This uses Mathlib's `lp.norm_single` and
  `lp.single_apply_ne`, following the coordinate calculations in solved
  sibling `m99A03`.

  The `D1` clause is consequently narrowed to a scalar lower bound for
  `|n| / sqrt (1+n^2)` along positive integer coordinates and the resulting
  two-coordinate separation estimate. The positive compactness clauses still
  require finite-coordinate projections and operator-norm tail estimates;
  `ιR` still requires measurable normalized indicators on disjoint sets and
  transport through the a.e. multiplier identity. Further searches of the
  `lp` single-coordinate API and the solved `m99A03`, `m95A02`, and `m02J06`
  artifacts found coordinate estimates but no packaged diagonal compactness
  or nonatomic multiplication-operator theorem. The frozen statement remains
  unchanged.

  CLOSER HOP 3 (partial). The `D1` noncompactness bridge is now closed.
  `apm_m93A01_not_compact_of_pos_separated_unit` generalizes the sequential
  obstruction to any positive separation constant;
  `apm_m93A01_circleDerivH1Coeff_lower` proves the symbol is at least `1/2`
  on every strictly positive integer frequency; and
  `apm_m93A01_circleDerivH1_not_compact` combines these with
  `lp.norm_apply_le_norm`. Crucially, evaluating the image difference at one
  selected coordinate avoids the previously open exact two-coordinate norm
  formula.

  The remaining three clauses are still open. Searches of Mathlib's compact-
  operator closure and finite-rank APIs found no ready-made diagonal
  multiplier criterion, so `ιS1` and `D2` still require explicit finite-rank
  coordinate truncations with operator-norm tail bounds. The `ιR` clause still
  requires constructing measurable normalized indicators on disjoint
  positive-measure subsets and transporting the pinned a.e. identity through
  quotient `Lp`. No `LEMMA-INDEX.md`, `ConstructionTargets/`, sibling, or git-
  history result supplies either bridge. The frozen statement is unchanged.
  -/
  sorry
