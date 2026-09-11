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

/-- On the bounded frequency window `[0,1]`, the real-line inclusion symbol
is bounded below by `1 / sqrt 2`.  This is the scalar estimate needed by the
disjoint-support obstruction below. -/
lemma apm_m93A01_realInclCoeff_lower {ξ : ℝ} (hξ₀ : 0 ≤ ξ) (hξ₁ : ξ ≤ 1) :
    (Real.sqrt 2)⁻¹ ≤ ‖apm_m93A01_realInclCoeff ξ‖ := by
  rw [apm_m93A01_realInclCoeff, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  rw [inv_le_inv₀ (by positivity) (by positivity)]
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg ξ, mul_nonneg hξ₀ (sub_nonneg.mpr hξ₁)]

/-- A concrete countable family of bounded, pairwise-disjoint frequency
windows.  Their endpoints tend to zero, but every window has positive finite
Lebesgue measure. -/
def apm_m93A01_realWindow (n : ℕ) : Set ℝ :=
  Set.Ioc ((n + 2 : ℕ) : ℝ)⁻¹ ((n + 1 : ℕ) : ℝ)⁻¹

lemma apm_m93A01_realWindow_measurable (n : ℕ) :
    MeasurableSet (apm_m93A01_realWindow n) := measurableSet_Ioc

lemma apm_m93A01_realWindow_subset (n : ℕ) :
    apm_m93A01_realWindow n ⊆ Set.Icc (0 : ℝ) 1 := by
  intro x hx
  rw [apm_m93A01_realWindow, Set.mem_Ioc] at hx
  constructor
  · exact (by positivity : (0 : ℝ) < ((n + 2 : ℕ) : ℝ)⁻¹).le.trans hx.1.le
  · exact hx.2.trans (by
      rw [inv_le_one₀]
      norm_num [Nat.cast_add, Nat.cast_one]
      positivity)

lemma apm_m93A01_realWindow_measure (n : ℕ) :
    volume (apm_m93A01_realWindow n) =
      ENNReal.ofReal (((n + 1 : ℕ) : ℝ)⁻¹ - ((n + 2 : ℕ) : ℝ)⁻¹) := by
  simp [apm_m93A01_realWindow, Real.volume_Ioc]

lemma apm_m93A01_realWindow_measure_pos (n : ℕ) :
    0 < volume (apm_m93A01_realWindow n) := by
  rw [apm_m93A01_realWindow_measure, ENNReal.ofReal_pos]
  have h₁ : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have h₂ : (0 : ℝ) < (n + 2 : ℕ) := by positivity
  rw [sub_pos, inv_lt_inv₀ h₂ h₁]
  norm_num

lemma apm_m93A01_realWindow_measure_ne_top (n : ℕ) :
    volume (apm_m93A01_realWindow n) ≠ (⊤ : ENNReal) := by
  rw [apm_m93A01_realWindow_measure]
  exact ENNReal.ofReal_ne_top

lemma apm_m93A01_realWindow_disjoint {n m : ℕ} (hnm : n ≠ m) :
    Disjoint (apm_m93A01_realWindow n) (apm_m93A01_realWindow m) := by
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · symm
    unfold apm_m93A01_realWindow
    apply Set.Ioc_disjoint_Ioc_of_le
    have hp : (0 : ℝ) < (n + 2 : ℕ) := by positivity
    have hq : (0 : ℝ) < (m + 1 : ℕ) := by positivity
    rw [inv_le_inv₀ hq hp]
    exact_mod_cast (by omega : n + 2 ≤ m + 1)
  · unfold apm_m93A01_realWindow
    apply Set.Ioc_disjoint_Ioc_of_le
    have hp : (0 : ℝ) < (m + 2 : ℕ) := by positivity
    have hq : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    rw [inv_le_inv₀ hq hp]
    exact_mod_cast (by omega : m + 2 ≤ n + 1)

/-- The normalized indicator of `realWindow n`, regarded as an element of the
Fourier `L²(ℝ,ℂ)` model. -/
def apm_m93A01_realWindowUnit (n : ℕ) : apm_m93A01_l2R :=
  indicatorConstLp 2 (apm_m93A01_realWindow_measurable n)
    (apm_m93A01_realWindow_measure_ne_top n)
    ((Real.sqrt (volume.real (apm_m93A01_realWindow n)))⁻¹ : ℝ)

lemma apm_m93A01_realWindowUnit_ae (n : ℕ) :
    (fun x : ℝ ↦ apm_m93A01_realWindowUnit n x) =ᵐ[volume]
      (apm_m93A01_realWindow n).indicator
        (fun _ ↦ (((Real.sqrt (volume.real (apm_m93A01_realWindow n)))⁻¹ : ℝ) : ℂ)) := by
  exact indicatorConstLp_coeFn

lemma apm_m93A01_realWindowUnit_norm (n : ℕ) :
    ‖apm_m93A01_realWindowUnit n‖ = 1 := by
  rw [apm_m93A01_realWindowUnit, norm_indicatorConstLp (by norm_num) (by norm_num)]
  have hm : 0 < volume.real (apm_m93A01_realWindow n) :=
    ENNReal.toReal_pos (ne_of_gt (apm_m93A01_realWindow_measure_pos n))
      (apm_m93A01_realWindow_measure_ne_top n)
  norm_num [Real.norm_eq_abs, ENNReal.toReal_ofNat]
  rw [← Real.sqrt_eq_rpow,
    abs_of_pos (Real.sqrt_pos.2 hm), inv_mul_cancel₀ (Real.sqrt_ne_zero'.2 hm)]

/-- The supplied real-line multiplier sends two distinct normalized windows
to points separated by the common lower bound of its symbol. -/
lemma apm_m93A01_realWindowUnit_separated
    (A : apm_m93A01_l2R →L[ℂ] apm_m93A01_l2R)
    (hA : ∀ f : apm_m93A01_l2R,
      (fun ξ : ℝ ↦ A f ξ) =ᵐ[volume]
        fun ξ ↦ apm_m93A01_realInclCoeff ξ * f ξ)
    {n m : ℕ} (hnm : n ≠ m) :
    (Real.sqrt 2)⁻¹ ≤
      dist (A (apm_m93A01_realWindowUnit n))
        (A (apm_m93A01_realWindowUnit m)) := by
  rw [dist_eq_norm]
  have hδnorm : ‖(((Real.sqrt 2)⁻¹ : ℝ) : ℂ)‖ = (Real.sqrt 2)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (Real.sqrt_pos.2 (by norm_num)))]
  have hae : ∀ᵐ x ∂volume,
      ‖((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
        apm_m93A01_realWindowUnit n) x‖ ≤
        ‖(A (apm_m93A01_realWindowUnit n) -
          A (apm_m93A01_realWindowUnit m)) x‖ := by
    filter_upwards [apm_m93A01_realWindowUnit_ae n,
      apm_m93A01_realWindowUnit_ae m,
      hA (apm_m93A01_realWindowUnit n),
      hA (apm_m93A01_realWindowUnit m),
      Lp.coeFn_smul (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
        (apm_m93A01_realWindowUnit n),
      Lp.coeFn_sub (A (apm_m93A01_realWindowUnit n))
        (A (apm_m93A01_realWindowUnit m))] with x hun hum hAn hAm hsmul hsub
    rw [hsmul, Pi.smul_apply, hsub, Pi.sub_apply, hAn, hAm]
    by_cases hx : x ∈ apm_m93A01_realWindow n
    · have hxm : x ∉ apm_m93A01_realWindow m := by
        intro hxm
        exact Set.disjoint_left.1 (apm_m93A01_realWindow_disjoint hnm) hx hxm
      rw [hun, hum, Set.indicator_of_mem hx, Set.indicator_of_notMem hxm]
      simp only [smul_eq_mul, mul_zero, sub_zero, norm_mul]
      rw [hδnorm]
      apply mul_le_mul_of_nonneg_right
        (apm_m93A01_realInclCoeff_lower
          ((apm_m93A01_realWindow_subset n hx).1)
          ((apm_m93A01_realWindow_subset n hx).2))
        (norm_nonneg _)
    · rw [hun, Set.indicator_of_notMem hx]
      simp
      positivity
  have hnorm := Lp.norm_le_norm_of_ae_le (p := (2 : ENNReal)) hae
  rw [norm_smul, apm_m93A01_realWindowUnit_norm, mul_one] at hnorm
  rw [hδnorm] at hnorm
  exact hnorm

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

/-- Evaluation at one Fourier coordinate, as a bounded linear functional. -/
def apm_m93A01_coord (n : ℤ) : apm_m93A01_l2Z →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ f n
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    1 (fun f ↦ by
      simpa only [one_mul] using
        lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) f n)

@[simp] lemma apm_m93A01_coord_apply (n : ℤ) (f : apm_m93A01_l2Z) :
    apm_m93A01_coord n f = f n := rfl

/-- A single diagonal matrix entry.  Factoring through `ℂ` makes its
compactness immediate and avoids introducing a finite-dimensional subspace of
`lp` explicitly. -/
def apm_m93A01_rankOne (c : ℤ → ℂ) (n : ℤ) :
    apm_m93A01_l2Z →L[ℂ] apm_m93A01_l2Z :=
  (lp.singleContinuousLinearMap ℂ (fun _ : ℤ ↦ ℂ) 2 n).comp
    (c n • apm_m93A01_coord n)

lemma apm_m93A01_rankOne_apply (c : ℤ → ℂ) (n : ℤ)
    (f : apm_m93A01_l2Z) :
    apm_m93A01_rankOne c n f = lp.single 2 n (c n * f n) := by
  rfl

lemma apm_m93A01_rankOne_compact (c : ℤ → ℂ) (n : ℤ) :
    IsCompactOperator (apm_m93A01_rankOne c n) := by
  simpa only [apm_m93A01_rankOne, ContinuousLinearMap.coe_comp', Function.comp_def] using
    (IsCompactOperator.clm_comp
      (isCompactOperator_of_locallyCompactSpace_dom (c n • apm_m93A01_coord n))
      (lp.singleContinuousLinearMap ℂ (fun _ : ℤ ↦ ℂ) 2 n))

/-- Finite-coordinate truncation of a diagonal multiplier. -/
def apm_m93A01_diagonalTrunc (c : ℤ → ℂ) (s : Finset ℤ) :
    apm_m93A01_l2Z →L[ℂ] apm_m93A01_l2Z :=
  ∑ n ∈ s, apm_m93A01_rankOne c n

lemma apm_m93A01_diagonalTrunc_compact (c : ℤ → ℂ) (s : Finset ℤ) :
    IsCompactOperator (apm_m93A01_diagonalTrunc c s) := by
  classical
  unfold apm_m93A01_diagonalTrunc
  induction s using Finset.induction_on with
  | empty =>
      change IsCompactOperator (0 : apm_m93A01_l2Z → apm_m93A01_l2Z)
      exact isCompactOperator_zero
  | @insert n s hn ih =>
      rw [Finset.sum_insert hn]
      exact (apm_m93A01_rankOne_compact c n).add ih

lemma apm_m93A01_diagonalTrunc_apply (c : ℤ → ℂ) (s : Finset ℤ)
    (f : apm_m93A01_l2Z) :
    apm_m93A01_diagonalTrunc c s f =
      ∑ n ∈ s, lp.single 2 n (c n * f n) := by
  classical
  simp [apm_m93A01_diagonalTrunc, apm_m93A01_rankOne_apply]

lemma apm_m93A01_diagonalTrunc_apply_coord (c : ℤ → ℂ) (s : Finset ℤ)
    (f : apm_m93A01_l2Z) (j : ℤ) :
    apm_m93A01_diagonalTrunc c s f j = if j ∈ s then c j * f j else 0 := by
  classical
  rw [apm_m93A01_diagonalTrunc_apply]
  rw [lp.coeFn_sum]
  simp [lp.single_apply]

/-- Uniform coordinate bounds pass to the `ℓ²` norm.  This is the analytic
estimate behind operator-norm convergence of the diagonal truncations. -/
lemma apm_m93A01_l2_norm_le_mul
    (g f : apm_m93A01_l2Z) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ j, ‖g j‖ ≤ C * ‖f j‖) :
    ‖g‖ ≤ C * ‖f‖ := by
  have hg := lp.hasSum_norm (f := g) (by norm_num : 0 < (2 : ENNReal).toReal)
  have hf := lp.hasSum_norm (f := f) (by norm_num : 0 < (2 : ENNReal).toReal)
  norm_num [Real.rpow_two] at hg hf
  have hsum : ‖g‖ ^ (2 : ℕ) ≤ C ^ (2 : ℕ) * ‖f‖ ^ (2 : ℕ) := by
    rw [← hg.tsum_eq, ← hf.tsum_eq, ← tsum_mul_left]
    apply Summable.tsum_le_tsum
    · intro j
      nlinarith [h j, norm_nonneg (g j), norm_nonneg (f j)]
    · exact hg.summable
    · exact hf.summable.mul_left _
  by_contra hn
  have hlt : C * ‖f‖ < ‖g‖ := lt_of_not_ge hn
  have hp : 0 ≤ C * ‖f‖ := mul_nonneg hC (norm_nonneg f)
  have hpos : 0 < C * ‖f‖ + ‖g‖ :=
    add_pos_of_nonneg_of_pos hp (lt_of_le_of_lt hp hlt)
  have hsquare := mul_lt_mul_of_pos_right hlt hpos
  nlinarith

lemma apm_m93A01_diagonal_sub_trunc_apply_norm
    (A : apm_m93A01_l2Z →L[ℂ] apm_m93A01_l2Z) (c : ℤ → ℂ)
    (hA : ∀ (f : apm_m93A01_l2Z) (n : ℤ), A f n = c n * f n)
    (s : Finset ℤ) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ j ∉ s, ‖c j‖ ≤ C) (f : apm_m93A01_l2Z) :
    ‖(A - apm_m93A01_diagonalTrunc c s) f‖ ≤ C * ‖f‖ := by
  apply apm_m93A01_l2_norm_le_mul _ f hC
  intro j
  rw [ContinuousLinearMap.sub_apply, lp.coeFn_sub, Pi.sub_apply, hA,
    apm_m93A01_diagonalTrunc_apply_coord]
  by_cases hj : j ∈ s
  · rw [if_pos hj, sub_self, norm_zero]
    positivity
  · rw [if_neg hj, sub_zero, norm_mul]
    exact mul_le_mul_of_nonneg_right (hc j hj) (norm_nonneg _)

lemma apm_m93A01_diagonal_sub_trunc_opNorm
    (A : apm_m93A01_l2Z →L[ℂ] apm_m93A01_l2Z) (c : ℤ → ℂ)
    (hA : ∀ (f : apm_m93A01_l2Z) (n : ℤ), A f n = c n * f n)
    (s : Finset ℤ) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ j ∉ s, ‖c j‖ ≤ C) :
    ‖A - apm_m93A01_diagonalTrunc c s‖ ≤ C := by
  exact ContinuousLinearMap.opNorm_le_bound _ hC
    (apm_m93A01_diagonal_sub_trunc_apply_norm A c hA s hC hc)

/-- A diagonal multiplier on `ℓ²(ℤ)` is compact when its symbol vanishes
uniformly off finite sets. -/
lemma apm_m93A01_diagonal_compact_of_cocompact_zero
    (A : apm_m93A01_l2Z →L[ℂ] apm_m93A01_l2Z) (c : ℤ → ℂ)
    (hA : ∀ (f : apm_m93A01_l2Z) (n : ℤ), A f n = c n * f n)
    (hc : ∀ ε : ℝ, 0 < ε → ∃ s : Finset ℤ, ∀ j ∉ s, ‖c j‖ ≤ ε) :
    IsCompactOperator A := by
  change A ∈ {T : apm_m93A01_l2Z →L[ℂ] apm_m93A01_l2Z | IsCompactOperator T}
  rw [← isClosed_setOf_isCompactOperator.closure_eq]
  apply Metric.mem_closure_iff.2
  intro ε hε
  obtain ⟨s, hs⟩ := hc (ε / 2) (half_pos hε)
  refine ⟨apm_m93A01_diagonalTrunc c s, apm_m93A01_diagonalTrunc_compact c s, ?_⟩
  rw [dist_eq_norm]
  exact (apm_m93A01_diagonal_sub_trunc_opNorm A c hA s (by positivity) hs).trans_lt
    (half_lt_self hε)

lemma apm_m93A01_circleInclCoeff_le_inv_abs (n : ℤ) (hn : n ≠ 0) :
    ‖apm_m93A01_circleInclCoeff n‖ ≤ |(n : ℝ)|⁻¹ := by
  rw [apm_m93A01_circleInclCoeff, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  rw [inv_le_inv₀]
  · rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith : (n : ℝ) ^ 2 ≤ 1 + (n : ℝ) ^ 2)
  · positivity
  · exact abs_pos.mpr (by exact_mod_cast hn)

/-- The elementary `1/|n|` tail is uniformly small away from a finite integer
interval. -/
lemma apm_m93A01_inv_abs_int_cocompact_zero
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset ℤ, ∀ j ∉ s, |(j : ℝ)|⁻¹ ≤ ε := by
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt ε⁻¹
  refine ⟨Finset.Icc (-(N : ℤ)) (N : ℤ), ?_⟩
  intro j hj
  simp only [Finset.mem_Icc, not_and_or, not_le] at hj
  have habs : (N : ℝ) < |(j : ℝ)| := by
    rcases hj with hj | hj
    · have hj' : (j : ℝ) < -(N : ℝ) := by exact_mod_cast hj
      rw [abs_of_neg (hj'.trans_le (neg_nonpos.mpr (Nat.cast_nonneg N)))]
      linarith
    · have hj' : (N : ℝ) < j := by exact_mod_cast hj
      rw [abs_of_pos (lt_of_le_of_lt (Nat.cast_nonneg N) hj')]
      exact hj'
  have habspos : 0 < |(j : ℝ)| :=
    lt_of_le_of_lt (Nat.cast_nonneg N) habs
  have hrecip : 1 / |(j : ℝ)| ≤ ε :=
    (one_div_le hε habspos).mp (by
      simpa only [one_div] using le_of_lt (hN.trans habs))
  simpa only [one_div] using hrecip

lemma apm_m93A01_circleInclCoeff_cocompact_zero :
    ∀ ε : ℝ, 0 < ε → ∃ s : Finset ℤ,
      ∀ j ∉ s, ‖apm_m93A01_circleInclCoeff j‖ ≤ ε := by
  intro ε hε
  obtain ⟨s, hs⟩ := apm_m93A01_inv_abs_int_cocompact_zero ε hε
  refine ⟨insert 0 s, ?_⟩
  intro j hj
  simp only [Finset.mem_insert, not_or] at hj
  exact (apm_m93A01_circleInclCoeff_le_inv_abs j hj.1).trans (hs j hj.2)

lemma apm_m93A01_circleDerivH2Coeff_le_inv_abs (n : ℤ) (hn : n ≠ 0) :
    ‖apm_m93A01_circleDerivH2Coeff n‖ ≤ |(n : ℝ)|⁻¹ := by
  rw [apm_m93A01_circleDerivH2Coeff, norm_div, norm_mul, Complex.norm_I,
    one_mul, norm_intCast_eq_abs_mul_norm_one ℂ, norm_one, mul_one,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have habs : 0 < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
  have hs : 0 < Real.sqrt (1 + (n : ℝ) ^ 2 + (n : ℝ) ^ 4) := by
    positivity
  rw [div_le_iff₀ hs, inv_mul_eq_div, le_div_iff₀ habs]
  have hsq : ((n : ℝ) ^ 2) ^ 2 ≤
      1 + (n : ℝ) ^ 2 + (n : ℝ) ^ 4 := by
    nlinarith [sq_nonneg (n : ℝ)]
  calc
    ((|n| : ℤ) : ℝ) * |(n : ℝ)| = |(n : ℝ)| * |(n : ℝ)| := by
      rw [Int.cast_abs]
    _ = (n : ℝ) ^ 2 := by rw [← sq, sq_abs]
    _ = Real.sqrt (((n : ℝ) ^ 2) ^ 2) := by
      rw [Real.sqrt_sq (sq_nonneg (n : ℝ))]
    _ ≤ Real.sqrt (1 + (n : ℝ) ^ 2 + (n : ℝ) ^ 4) :=
      Real.sqrt_le_sqrt hsq

lemma apm_m93A01_circleDerivH2Coeff_cocompact_zero :
    ∀ ε : ℝ, 0 < ε → ∃ s : Finset ℤ,
      ∀ j ∉ s, ‖apm_m93A01_circleDerivH2Coeff j‖ ≤ ε := by
  intro ε hε
  obtain ⟨s, hs⟩ := apm_m93A01_inv_abs_int_cocompact_zero ε hε
  refine ⟨insert 0 s, ?_⟩
  intro j hj
  simp only [Finset.mem_insert, not_or] at hj
  exact (apm_m93A01_circleDerivH2Coeff_le_inv_abs j hj.1).trans (hs j hj.2)

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
  apply apm_m93A01_not_compact_of_pos_separated_unit A
    apm_m93A01_realWindowUnit (δ := (Real.sqrt 2)⁻¹)
      (inv_pos.mpr (Real.sqrt_pos.2 (by norm_num)))
  · intro n
    rw [apm_m93A01_realWindowUnit_norm]
  · intro n m hnm
    exact apm_m93A01_realWindowUnit_separated A hA hnm

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

  CLOSER HOP 4 (partial). The measurable-set infrastructure for the real-line
  obstruction is now compiled. `apm_m93A01_realWindow` gives pairwise-disjoint
  intervals `(1/(n+2), 1/(n+1)]` inside `[0,1]`; their measurability, positive
  finite volume, and pairwise disjointness are proved. The normalized
  indicators `apm_m93A01_realWindowUnit` are constructed directly in
  `Lp ℂ 2 volume`, their representatives are pinned almost everywhere, and
  their norm is proved to equal one. Finally,
  `apm_m93A01_realInclCoeff_lower` proves the multiplier is at least
  `(sqrt 2)⁻¹` throughout the common bounded window.

  Thus `apm_m93A01_bridge_1` is reduced to transporting `hA` to these
  representatives and calculating that images with disjoint supports have a
  fixed positive separation. Independently, the two positive compactness
  clauses still require finite-coordinate truncation maps and operator-norm
  convergence. The final conjunction then follows from those three bridges
  and the already compiled `apm_m93A01_circleDerivH1_not_compact`.

  CLOSER HOP 5. `apm_m93A01_bridge_1` is now closed. The pointwise multiplier
  identity is transported to the normalized window representatives;
  disjointness makes the second image vanish on the first window, and
  `Lp.norm_le_norm_of_ae_le` lifts the scalar symbol lower bound to a uniform
  distance bound. The general positive-separation obstruction then proves the
  real-line multiplier noncompact.

  The sole executable `sorry` is now the final theorem. Its only substantive
  residuals are the independent positive clauses `IsCompactOperator ιS1` and
  `IsCompactOperator D2`: each needs finite-coordinate truncations on `lp`,
  compactness of those finite-rank maps, and operator-norm tail convergence.
  Once those are available, final assembly uses this bridge and the compiled
  `D1` bridge directly.

  CLOSER HOP 6 (partial). The shared positive-compactness infrastructure is
  now compiled. `apm_m93A01_coord` and `apm_m93A01_rankOne` construct bounded
  coordinate functionals and coordinate rank-one maps; the latter factor
  through locally compact `ℂ`. `apm_m93A01_diagonalTrunc` is therefore compact
  for every finite coordinate set. The `ℓ²` estimate
  `apm_m93A01_l2_norm_le_mul` lifts pointwise coordinate domination to norm
  domination, yielding exact operator-norm tail control. Finally,
  `apm_m93A01_diagonal_compact_of_cocompact_zero` closes the abstract theorem:
  any supplied diagonal map whose symbol is uniformly small off finite sets
  lies in the norm-closed set of compact operators.

  The two remaining independent scalar obligations are now precise: prove
  the finite-exception decay hypothesis for `circleInclCoeff` and for
  `circleDerivH2Coeff`. Final conjunction assembly then applies the shared
  criterion twice and the two compiled negative bridges.

  CLOSER HOP 7 (closed). Both scalar obligations are discharged through the
  common bound `1 / |n|`. A finite integer interval contains all exceptional
  coordinates for any positive tolerance. For the inclusion symbol, the
  denominator dominates `|n|`; for the `H²` derivative symbol, its denominator
  dominates `|n|²`, leaving the same reciprocal bound after cancellation.
  The two compact diagonal clauses now follow from the shared criterion, and
  the final conjunction combines them with the two compiled noncompactness
  bridges. The theorem is sorry-free and its axiom audit is printed below.
  -/
  refine ⟨?_, apm_m93A01_bridge_1 ιR hιR,
    apm_m93A01_circleDerivH1_not_compact D1 hD1, ?_⟩
  · exact apm_m93A01_diagonal_compact_of_cocompact_zero ιS1
      apm_m93A01_circleInclCoeff hιS1
      apm_m93A01_circleInclCoeff_cocompact_zero
  · exact apm_m93A01_diagonal_compact_of_cocompact_zero D2
      apm_m93A01_circleDerivH2Coeff hD2
      apm_m93A01_circleDerivH2Coeff_cocompact_zero

#print axioms apm_m93a01
