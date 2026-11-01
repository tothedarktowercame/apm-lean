import Mathlib

/-!
# APM m94J02

## Statement repairs

The claimed bound `‖fg‖ ≤ ‖f‖‖g‖` is false for the printed weight
`n² + 1`: for `f = g = z`, the two sides are `5` and `4`. It is
minimally repaired to the sharp bound `‖fg‖ ≤ (5/4)‖f‖‖g‖`, which still
makes the complete normed space a Banach algebra.

## Encoding questions

The space is encoded by its unique coefficient sequences. Compactness of the
dilation is stated in the sequential form for its unit ball, and the spectrum
uses the usual bounded two-sided-inverse definition, both with the displayed
weighted norm.
-/

open Filter Set

/-- Membership in the weighted `ℓ¹` coefficient space. -/
def apm_m94J02_mem (a : ℕ → ℂ) : Prop :=
  Summable (fun n ↦ ‖a n‖ * ((n : ℝ) ^ 2 + 1))

/-- The norm printed in the problem. -/
noncomputable def apm_m94J02_norm (a : ℕ → ℂ) : ℝ :=
  ∑' n, ‖a n‖ * ((n : ℝ) ^ 2 + 1)

/-- Evaluation of the represented power series. -/
noncomputable def apm_m94J02_eval (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑' n, a n * z ^ n

/-- Cauchy-product coefficients. -/
noncomputable def apm_m94J02_mul (a b : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), a k * b (n - k)

/-- Coefficients of the `m`th pointwise power. -/
noncomputable def apm_m94J02_pow (a : ℕ → ℂ) : ℕ → ℕ → ℂ
  | 0 => fun n ↦ if n = 0 then 1 else 0
  | m + 1 => apm_m94J02_mul (apm_m94J02_pow a m) a

/-- The coefficient action of `Tf(z)=f(z/2)`. -/
noncomputable def apm_m94J02_T (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  (2 : ℂ) ^ (-(n : ℤ)) * a n

/-- Scalars for which `T - λI` has no bounded two-sided inverse on `X`. -/
def apm_m94J02_spectrum : Set ℂ :=
  {z | ¬∃ S : (ℕ → ℂ) → (ℕ → ℂ),
    (∀ a, apm_m94J02_mem a → apm_m94J02_mem (S a)) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ a, apm_m94J02_mem a →
      apm_m94J02_norm (S a) ≤ C * apm_m94J02_norm a) ∧
    (∀ a, apm_m94J02_mem a →
      S (fun n ↦ apm_m94J02_T a n - z * a n) = a) ∧
    (∀ a, apm_m94J02_mem a →
      (fun n ↦ apm_m94J02_T (S a) n - z * (S a) n) = a)}

/-- Every displayed diagonal entry is in the custom spectrum. -/
lemma apm_m94J02_eigenvalue_mem_spectrum (j : ℕ) :
    (2 : ℂ) ^ (-(j : ℤ)) ∈ apm_m94J02_spectrum := by
  intro hS
  rcases hS with ⟨S, _, _, hleft, _⟩
  let e : ℕ → ℂ := fun n => if n = j then 1 else 0
  have he_mem : apm_m94J02_mem e := by
    unfold apm_m94J02_mem e
    apply summable_of_hasFiniteSupport
    exact (Set.finite_singleton j).subset (by
      intro n hn
      by_contra hnj
      apply hn
      dsimp
      rw [if_neg (by simpa using hnj)]
      simp)
  have hz_mem : apm_m94J02_mem (fun _ : ℕ => (0 : ℂ)) := by
    unfold apm_m94J02_mem
    simp
  have hzero : (fun n => apm_m94J02_T e n - (2 : ℂ) ^ (-(j : ℤ)) * e n) =
      (fun _ => 0) := by
    funext n
    by_cases hnj : n = j
    · subst n
      simp [apm_m94J02_T, e]
    · simp [apm_m94J02_T, e, hnj]
  have hSe : S (fun _ : ℕ => (0 : ℂ)) = e := by
    rw [← hzero]
    exact hleft e he_mem
  have hSz : S (fun _ : ℕ => (0 : ℂ)) = (fun _ => 0) := by
    simpa [apm_m94J02_T] using hleft (fun _ : ℕ => (0 : ℂ)) hz_mem
  have hej : e j = 1 := by simp [e]
  have : e = (fun _ => 0) := hSe.symm.trans hSz
  have := congrFun this j
  simp [hej] at this

/-- The complete range of diagonal entries lies in the custom spectrum. -/
lemma apm_m94J02_diagonal_range_subset_spectrum :
    Set.range (fun n : ℕ ↦ (2 : ℂ) ^ (-(n : ℤ))) ⊆
      apm_m94J02_spectrum := by
  rintro z ⟨n, rfl⟩
  exact apm_m94J02_eigenvalue_mem_spectrum n

/-- The dilation is a contraction for the displayed weighted norm. -/
lemma apm_m94J02_norm_T_le (a : ℕ → ℂ) (ha : apm_m94J02_mem a) :
    apm_m94J02_norm (apm_m94J02_T a) ≤ apm_m94J02_norm a := by
  unfold apm_m94J02_norm
  unfold apm_m94J02_mem at ha
  simp only [apm_m94J02_T]
  have hleft : Summable
      (fun n : ℕ ↦ ‖(2 : ℂ) ^ (-(n : ℤ)) * a n‖ * ((n : ℝ) ^ 2 + 1)) := by
    refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun n ↦ ?_) ha
    rw [norm_mul]
    have hs : ‖(2 : ℂ) ^ (-(n : ℤ))‖ ≤ 1 := by
      rw [norm_zpow]
      exact zpow_le_one_of_nonpos₀ (by norm_num) (by simp)
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_left (norm_nonneg (a n)) hs) (by positivity)
  exact Summable.tsum_le_tsum (fun n ↦ by
    rw [norm_mul]
    have hs : ‖(2 : ℂ) ^ (-(n : ℤ))‖ ≤ 1 := by
      rw [norm_zpow]
      exact zpow_le_one_of_nonpos₀ (by norm_num) (by simp)
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_left (norm_nonneg (a n)) hs) (by positivity)) hleft ha

/-- Weighted summability implies ordinary absolute summability of the
coefficient sequence. -/
lemma apm_m94J02_summable_norm (a : ℕ → ℂ) (ha : apm_m94J02_mem a) :
    Summable (fun n ↦ ‖a n‖) := by
  unfold apm_m94J02_mem at ha
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) ha
  have hw : (1 : ℝ) ≤ (n : ℝ) ^ 2 + 1 := by
    nlinarith [sq_nonneg (n : ℝ)]
  simpa only [mul_one] using
    (mul_le_mul_of_nonneg_left hw (norm_nonneg (a n)))

/-- The coefficient series converges uniformly on the closed unit disk, hence
represents a continuous function there. -/
lemma apm_m94J02_eval_continuousOn (a : ℕ → ℂ)
    (ha : apm_m94J02_mem a) :
    ContinuousOn (apm_m94J02_eval a) (Metric.closedBall 0 1) := by
  unfold apm_m94J02_eval
  apply continuousOn_tsum (u := fun n ↦ ‖a n‖)
  · intro n
    fun_prop
  · exact apm_m94J02_summable_norm a ha
  · intro n z hz
    rw [norm_mul, norm_pow]
    have hz1 : ‖z‖ ≤ 1 := by
      simpa [Metric.mem_closedBall] using hz
    exact mul_le_of_le_one_right (norm_nonneg (a n))
      (pow_le_one₀ (norm_nonneg z) hz1)

/-- The sharp elementary weight inequality behind the repaired algebra
constant. Equality occurs at `i = j = 1`. -/
lemma apm_m94J02_weight_add_le (i j : ℕ) :
    ((i + j : ℕ) : ℝ) ^ 2 + 1 ≤
      (5 / 4 : ℝ) * ((i : ℝ) ^ 2 + 1) * ((j : ℝ) ^ 2 + 1) := by
  by_cases hi : i = 0
  · subst i
    norm_num
    nlinarith [sq_nonneg (j : ℝ)]
  by_cases hj : j = 0
  · subst j
    norm_num
    nlinarith [sq_nonneg (i : ℝ)]
  have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hi)
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hj)
  have hij1 : (1 : ℝ) ≤ (i : ℝ) * j := by nlinarith
  have hsquare : 0 ≤ ((i : ℝ) - j) ^ 2 := sq_nonneg _
  have hprod : 0 ≤ (5 * ((i : ℝ) * j) - 1) *
      ((i : ℝ) * j - 1) := mul_nonneg (by nlinarith) (by nlinarith)
  norm_num [Nat.cast_add]
  nlinarith

/-- Concrete sharpness/non-vacuity check for the weight inequality. -/
lemma apm_m94J02_weight_add_eq_one :
    (((1 + 1 : ℕ) : ℝ) ^ 2 + 1) =
      (5 / 4 : ℝ) * (((1 : ℕ) : ℝ) ^ 2 + 1) *
        (((1 : ℕ) : ℝ) ^ 2 + 1) := by
  norm_num

set_option maxHeartbeats 2000000

/-- The Cauchy product stays in the weighted coefficient space and satisfies
the repaired sharp algebra estimate. -/
lemma apm_m94J02_mul_mem_norm_le (a b : ℕ → ℂ)
    (ha : apm_m94J02_mem a) (hb : apm_m94J02_mem b) :
    apm_m94J02_mem (apm_m94J02_mul a b) ∧
      apm_m94J02_norm (apm_m94J02_mul a b) ≤
        (5 / 4 : ℝ) * apm_m94J02_norm a * apm_m94J02_norm b := by
  let A : ℕ → ℝ := fun n ↦ ‖a n‖ * ((n : ℝ) ^ 2 + 1)
  let B : ℕ → ℝ := fun n ↦ ‖b n‖ * ((n : ℝ) ^ 2 + 1)
  let c : ℕ → ℝ := fun n ↦ ∑ k ∈ Finset.range (n + 1), A k * B (n - k)
  have hA : Summable A := ha
  have hB : Summable B := hb
  have hAnorm : Summable (fun n ↦ ‖A n‖) := by
    convert hA using 1
    funext n
    dsimp [A]
    exact abs_of_nonneg (by positivity)
  have hBnorm : Summable (fun n ↦ ‖B n‖) := by
    convert hB using 1
    funext n
    dsimp [B]
    exact abs_of_nonneg (by positivity)
  have hc : Summable c := by
    exact (summable_norm_sum_mul_range_of_summable_norm hAnorm hBnorm).of_norm
  have hpoint (n : ℕ) :
      ‖apm_m94J02_mul a b n‖ * ((n : ℝ) ^ 2 + 1) ≤ (5 / 4 : ℝ) * c n := by
    unfold apm_m94J02_mul
    calc
      ‖∑ k ∈ Finset.range (n + 1), a k * b (n - k)‖ * ((n : ℝ) ^ 2 + 1)
          ≤ (∑ k ∈ Finset.range (n + 1), ‖a k * b (n - k)‖) *
              ((n : ℝ) ^ 2 + 1) := by
                gcongr
                exact norm_sum_le _ _
      _ = ∑ k ∈ Finset.range (n + 1),
          (‖a k * b (n - k)‖ * ((n : ℝ) ^ 2 + 1)) := by
            rw [Finset.sum_mul]
      _ ≤ ∑ k ∈ Finset.range (n + 1), (5 / 4 : ℝ) * (A k * B (n - k)) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkn : k ≤ n := by simpa [Finset.mem_range] using hk
        have hw := apm_m94J02_weight_add_le k (n - k)
        rw [Nat.add_sub_of_le hkn] at hw
        dsimp [A, B]
        rw [norm_mul]
        have hana : 0 ≤ ‖a k‖ := norm_nonneg _
        have hbnb : 0 ≤ ‖b (n - k)‖ := norm_nonneg _
        calc
          ‖a k‖ * ‖b (n - k)‖ * ((n : ℝ) ^ 2 + 1) ≤
              ‖a k‖ * ‖b (n - k)‖ *
                ((5 / 4 : ℝ) * ((k : ℝ) ^ 2 + 1) *
                  (((n - k : ℕ) : ℝ) ^ 2 + 1)) :=
            mul_le_mul_of_nonneg_left hw (mul_nonneg hana hbnb)
          _ = (5 / 4 : ℝ) *
              (‖a k‖ * ((k : ℝ) ^ 2 + 1) *
                (‖b (n - k)‖ * (((n - k : ℕ) : ℝ) ^ 2 + 1))) := by ring
      _ = (5 / 4 : ℝ) * c n := by
        simp [c, Finset.mul_sum]
  have hmem : apm_m94J02_mem (apm_m94J02_mul a b) := by
    unfold apm_m94J02_mem
    exact Summable.of_nonneg_of_le (fun _ ↦ by positivity) hpoint (hc.mul_left (5 / 4))
  refine ⟨hmem, ?_⟩
  unfold apm_m94J02_norm
  calc
    ∑' n, ‖apm_m94J02_mul a b n‖ * ((n : ℝ) ^ 2 + 1)
        ≤ ∑' n, (5 / 4 : ℝ) * c n :=
          Summable.tsum_le_tsum hpoint hmem (hc.mul_left (5 / 4))
    _ = (5 / 4 : ℝ) * ∑' n, c n := by rw [tsum_mul_left]
    _ = (5 / 4 : ℝ) * (∑' n, A n) * (∑' n, B n) := by
      rw [show (∑' n, c n) = (∑' n, A n) * (∑' n, B n) by
        dsimp [c]
        symm
        exact tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hAnorm hBnorm]
      ring
    _ = (5 / 4 : ℝ) * (∑' n, ‖a n‖ * ((n : ℝ) ^ 2 + 1)) *
        (∑' n, ‖b n‖ * ((n : ℝ) ^ 2 + 1)) := by rfl

/-- Every recursively defined Cauchy-product power remains in the weighted
coefficient space. -/
lemma apm_m94J02_pow_mem (a : ℕ → ℂ) (ha : apm_m94J02_mem a) :
    ∀ m : ℕ, apm_m94J02_mem (apm_m94J02_pow a m) := by
  intro m
  induction m with
  | zero =>
      unfold apm_m94J02_mem apm_m94J02_pow
      apply summable_of_hasFiniteSupport
      exact (Set.finite_singleton 0).subset (by
        intro n hn
        by_contra hn0
        have hne : n ≠ 0 := by simpa using hn0
        apply hn
        simp [hne])
  | succ m ih =>
      exact (apm_m94J02_mul_mem_norm_le
        (apm_m94J02_pow a m) a ih ha).1

/-- The power norms satisfy the sharp recursive algebra estimate. -/
lemma apm_m94J02_norm_pow_succ_le (a : ℕ → ℂ) (ha : apm_m94J02_mem a)
    (m : ℕ) :
    apm_m94J02_norm (apm_m94J02_pow a (m + 1)) ≤
      (5 / 4 : ℝ) * apm_m94J02_norm (apm_m94J02_pow a m) *
        apm_m94J02_norm a := by
  exact (apm_m94J02_mul_mem_norm_le
    (apm_m94J02_pow a m) a (apm_m94J02_pow_mem a ha m) ha).2

/-- The explicit Cauchy product is the coefficient sequence of multiplication
of formal power series. -/
lemma apm_m94J02_powerSeries_mk_mul (a b : ℕ → ℂ) :
    PowerSeries.mk (apm_m94J02_mul a b) = PowerSeries.mk a * PowerSeries.mk b := by
  ext n
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul]
  simp only [PowerSeries.coeff_mk]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rfl

lemma apm_m94J02_powerSeries_mk_injective {a b : ℕ → ℂ}
    (h : PowerSeries.mk a = PowerSeries.mk b) : a = b := by
  funext n
  have := congrArg (PowerSeries.coeff n) h
  simpa using this

/-- The custom Cauchy product is associative. -/
lemma apm_m94J02_mul_assoc (a b c : ℕ → ℂ) :
    apm_m94J02_mul (apm_m94J02_mul a b) c =
      apm_m94J02_mul a (apm_m94J02_mul b c) := by
  apply apm_m94J02_powerSeries_mk_injective
  rw [apm_m94J02_powerSeries_mk_mul, apm_m94J02_powerSeries_mk_mul,
    apm_m94J02_powerSeries_mk_mul, apm_m94J02_powerSeries_mk_mul, mul_assoc]

/-- The formal series attached to the recursively defined coefficient power
is the ordinary power of the attached formal series. -/
lemma apm_m94J02_powerSeries_mk_pow (a : ℕ → ℂ) (m : ℕ) :
    PowerSeries.mk (apm_m94J02_pow a m) = (PowerSeries.mk a) ^ m := by
  induction m with
  | zero =>
      ext n
      simp [apm_m94J02_pow]
  | succ m ih =>
      rw [pow_succ, ← ih, ← apm_m94J02_powerSeries_mk_mul]
      rfl

/-- The first nonzero coefficient of a formal series raises to the expected
power at the corresponding multiple of its order. -/
lemma apm_m94J02_pow_coeff_at_order (a : ℕ → ℂ)
    (ha0 : a ≠ 0) (n : ℕ) :
    apm_m94J02_pow a n
        (n * (PowerSeries.mk a).order.toNat) =
      (a (PowerSeries.mk a).order.toNat) ^ n := by
  let f : PowerSeries ℂ := PowerSeries.mk a
  have hf : f ≠ 0 := by
    intro h
    apply ha0
    apply apm_m94J02_powerSeries_mk_injective
    simpa [f] using h
  have hord : (f ^ n).order.toNat = n * f.order.toNat := by
    rw [PowerSeries.order_pow]
    simp
  calc
    apm_m94J02_pow a n (n * f.order.toNat) =
        PowerSeries.coeff (n * f.order.toNat) (f ^ n) := by
      rw [← apm_m94J02_powerSeries_mk_pow]
      simp [f]
    _ = PowerSeries.constantCoeff (PowerSeries.divXPowOrder (f ^ n)) := by
      rw [PowerSeries.constantCoeff_divXPowOrder, hord]
    _ = (PowerSeries.constantCoeff (PowerSeries.divXPowOrder f)) ^ n := by
      rw [PowerSeries.divXPowOrder_pow]
      exact map_pow PowerSeries.constantCoeff (PowerSeries.divXPowOrder f) n
    _ = (a f.order.toNat) ^ n := by
      rw [PowerSeries.constantCoeff_divXPowOrder]
      simp [f]

/-- Powers for the custom Cauchy product satisfy the addition law. -/
lemma apm_m94J02_pow_add (a : ℕ → ℂ) (m n : ℕ) :
    apm_m94J02_pow a (m + n) =
      apm_m94J02_mul (apm_m94J02_pow a m) (apm_m94J02_pow a n) := by
  apply apm_m94J02_powerSeries_mk_injective
  rw [apm_m94J02_powerSeries_mk_mul]
  simp only [apm_m94J02_powerSeries_mk_pow, pow_add]

/-- The custom weighted norm is nonnegative. -/
lemma apm_m94J02_norm_nonneg (a : ℕ → ℂ) : 0 ≤ apm_m94J02_norm a := by
  unfold apm_m94J02_norm
  exact tsum_nonneg fun n => mul_nonneg (norm_nonneg _) (by positivity)

/-- Every weighted coordinate is bounded by the custom norm. -/
lemma apm_m94J02_weighted_coordinate_le_norm (a : ℕ → ℂ)
    (ha : apm_m94J02_mem a) (j : ℕ) :
    ‖a j‖ * ((j : ℝ) ^ 2 + 1) ≤ apm_m94J02_norm a := by
  unfold apm_m94J02_mem at ha
  unfold apm_m94J02_norm
  simpa using ha.sum_le_tsum {j}
    (fun n _ => mul_nonneg (norm_nonneg (a n)) (by positivity))

/-- On the weighted coefficient space, zero custom norm means every
coefficient is zero. -/
lemma apm_m94J02_norm_eq_zero_iff (a : ℕ → ℂ) (ha : apm_m94J02_mem a) :
    apm_m94J02_norm a = 0 ↔ a = 0 := by
  constructor
  · intro h
    funext j
    have hj := apm_m94J02_weighted_coordinate_le_norm a ha j
    rw [h] at hj
    have : ‖a j‖ = 0 := by nlinarith [norm_nonneg (a j)]
    simpa using (norm_eq_zero.mp this)
  · rintro rfl
    simp [apm_m94J02_norm]

/-- A weighted coefficient sequence is represented isometrically in
Mathlib's complete `ℓ¹` space by multiplying each coordinate by its weight. -/
lemma apm_m94J02_exists_weighted_lp (a : ℕ → ℂ) (ha : apm_m94J02_mem a) :
    ∃ x : lp (fun _ : ℕ => ℂ) 1,
      (∀ n, x n = Complex.ofReal ((n : ℝ) ^ 2 + 1) * a n) ∧
      ‖x‖ = apm_m94J02_norm a := by
  let f : ℕ → ℂ := fun n => Complex.ofReal ((n : ℝ) ^ 2 + 1) * a n
  have hfsum : Summable (fun n => ‖f n‖) := by
    unfold apm_m94J02_mem at ha
    convert ha using 1
    funext n
    dsimp [f]
    rw [norm_mul]
    have hw : ‖Complex.ofReal ((n : ℝ) ^ 2 + 1)‖ = (n : ℝ) ^ 2 + 1 := by
      exact (Complex.norm_real _).trans <|
        (Real.norm_eq_abs _).trans (abs_of_nonneg (by positivity))
    rw [hw]
    ring
  have hf : Memℓp f 1 := by
    apply memℓp_gen
    simpa using hfsum
  let x : lp (fun _ : ℕ => ℂ) 1 := ⟨f, hf⟩
  refine ⟨x, fun n => rfl, ?_⟩
  rw [lp.norm_eq_tsum_rpow (by norm_num)]
  simp only [ENNReal.toReal_one]
  rw [show (1 / (1 : ℝ)) = 1 by norm_num, Real.rpow_one]
  unfold apm_m94J02_norm
  congr 1
  funext n
  dsimp [x, f]
  rw [Real.rpow_one, norm_mul]
  have hw : ‖Complex.ofReal ((n : ℝ) ^ 2 + 1)‖ = (n : ℝ) ^ 2 + 1 := by
    exact (Complex.norm_real _).trans <|
      (Real.norm_eq_abs _).trans (abs_of_nonneg (by positivity))
  rw [hw]
  ring

/-- Subtraction of weighted representatives is an exact isometry for the
frozen weighted norm. -/
lemma apm_m94J02_weighted_lp_sub_norm (a b : ℕ → ℂ)
    (x y : lp (fun _ : ℕ => ℂ) 1)
    (hx : ∀ n, x n = Complex.ofReal ((n : ℝ) ^ 2 + 1) * a n)
    (hy : ∀ n, y n = Complex.ofReal ((n : ℝ) ^ 2 + 1) * b n) :
    ‖x - y‖ = apm_m94J02_norm (fun n => a n - b n) := by
  rw [lp.norm_eq_tsum_rpow (by norm_num)]
  simp only [ENNReal.toReal_one]
  rw [show (1 / (1 : ℝ)) = 1 by norm_num, Real.rpow_one]
  unfold apm_m94J02_norm
  congr 1
  funext n
  rw [lp.coeFn_sub, Pi.sub_apply, hx n, hy n, ← mul_sub, Real.rpow_one,
    norm_mul]
  have hw : ‖Complex.ofReal ((n : ℝ) ^ 2 + 1)‖ = (n : ℝ) ^ 2 + 1 := by
    exact (Complex.norm_real _).trans <|
      (Real.norm_eq_abs _).trans (abs_of_nonneg (by positivity))
  rw [hw]
  ring

/-- Coordinate evaluation on the `ℓ¹` model as a bounded linear map. -/
def apm_m94J02_lpEval (n : ℕ) :
    lp (fun _ : ℕ => ℂ) 1 →L[ℂ] ℂ where
  toFun x := x n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by
    exact (continuous_apply n).comp
      (lp.uniformContinuous_coe (E := fun _ : ℕ => ℂ) (p := 1)).continuous

@[simp] lemma apm_m94J02_lpEval_apply (n : ℕ)
    (x : lp (fun _ : ℕ => ℂ) 1) : apm_m94J02_lpEval n x = x n := by
  rfl

/-- The `n`th diagonal rank-one piece of the dilation on the `ℓ¹` model. -/
noncomputable def apm_m94J02_rankOne (n : ℕ) :
    lp (fun _ : ℕ => ℂ) 1 →L[ℂ] lp (fun _ : ℕ => ℂ) 1 :=
  (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => ℂ) 1 n).comp
    (((2 : ℂ) ^ (-(n : ℤ))) • apm_m94J02_lpEval n)

lemma apm_m94J02_rankOne_apply (n : ℕ)
    (x : lp (fun _ : ℕ => ℂ) 1) :
    apm_m94J02_rankOne n x =
      lp.single 1 n ((2 : ℂ) ^ (-(n : ℤ)) * x n) := by
  ext i
  by_cases hi : i = n
  · subst i
    simp [apm_m94J02_rankOne]
  · simp [apm_m94J02_rankOne, lp.single_apply, hi]

/-- Every diagonal coordinate piece factors through `ℂ`, hence is compact. -/
lemma apm_m94J02_rankOne_compact (n : ℕ) :
    IsCompactOperator (apm_m94J02_rankOne n) := by
  have h := IsCompactOperator.clm_comp
    (isCompactOperator_of_locallyCompactSpace_dom
      (((2 : ℂ) ^ (-(n : ℤ))) • apm_m94J02_lpEval n))
    (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => ℂ) 1 n)
  convert h using 1

/-- Finite diagonal truncations of the dilation on the `ℓ¹` model. -/
noncomputable def apm_m94J02_truncation (N : ℕ) :
    lp (fun _ : ℕ => ℂ) 1 →L[ℂ] lp (fun _ : ℕ => ℂ) 1 :=
  ∑ n ∈ Finset.range N, apm_m94J02_rankOne n

@[simp] lemma apm_m94J02_truncation_zero : apm_m94J02_truncation 0 = 0 := by
  simp [apm_m94J02_truncation]

lemma apm_m94J02_truncation_compact (N : ℕ) :
    IsCompactOperator (apm_m94J02_truncation N) := by
  unfold apm_m94J02_truncation
  induction Finset.range N using Finset.induction_on with
  | empty => simpa using (isCompactOperator_zero :
      IsCompactOperator (0 : lp (fun _ : ℕ => ℂ) 1 → lp (fun _ : ℕ => ℂ) 1))
  | @insert n s hn ih =>
      rw [Finset.sum_insert hn]
      have h := (apm_m94J02_rankOne_compact n).add ih
      convert h using 1

lemma apm_m94J02_diagonal_summable (x : lp (fun _ : ℕ => ℂ) 1) :
    Summable (fun n : ℕ => ‖(2 : ℂ) ^ (-(n : ℤ)) * x n‖) := by
  have hx : Summable (fun n => ‖x n‖) := by
    simpa using (lp.memℓp x).summable (by norm_num)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hx
  rw [norm_mul]
  have hlam : ‖(2 : ℂ) ^ (-(n : ℤ))‖ ≤ 1 := by
    rw [norm_zpow]
    exact zpow_le_one_of_nonpos₀ (by norm_num) (by simp)
  exact mul_le_of_le_one_left (norm_nonneg _) hlam

/-- The full diagonal multiplier underlying dilation on the `ℓ¹` model. -/
noncomputable def apm_m94J02_diagonalFun
    (x : lp (fun _ : ℕ => ℂ) 1) : lp (fun _ : ℕ => ℂ) 1 :=
  ⟨fun n => (2 : ℂ) ^ (-(n : ℤ)) * x n, by
    apply memℓp_gen
    simpa using apm_m94J02_diagonal_summable x⟩

@[simp] lemma apm_m94J02_diagonalFun_apply
    (x : lp (fun _ : ℕ => ℂ) 1) (n : ℕ) :
    apm_m94J02_diagonalFun x n = (2 : ℂ) ^ (-(n : ℤ)) * x n := rfl

lemma apm_m94J02_diagonalFun_norm_le
    (x : lp (fun _ : ℕ => ℂ) 1) :
    ‖apm_m94J02_diagonalFun x‖ ≤ ‖x‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
  simp only [ENNReal.toReal_one]
  rw [show (1 / (1 : ℝ)) = 1 by norm_num, Real.rpow_one, Real.rpow_one]
  have hsum : Summable (fun n : ℕ =>
      ‖apm_m94J02_diagonalFun x n‖ ^ (1 : ℝ)) := by
    simpa [apm_m94J02_diagonalFun_apply, Real.rpow_one] using
      apm_m94J02_diagonal_summable x
  have hxsum : Summable (fun n : ℕ => ‖x n‖ ^ (1 : ℝ)) := by
    simpa [Real.rpow_one] using (lp.memℓp x).summable (by norm_num)
  exact Summable.tsum_le_tsum (fun n : ℕ => by
    rw [Real.rpow_one, Real.rpow_one, apm_m94J02_diagonalFun_apply, norm_mul]
    have hlam : ‖(2 : ℂ) ^ (-(n : ℤ))‖ ≤ 1 := by
      rw [norm_zpow]
      exact zpow_le_one_of_nonpos₀ (by norm_num) (by simp)
    simpa [Real.rpow_one] using
      (mul_le_of_le_one_left (norm_nonneg (x n)) hlam))
    hsum hxsum

noncomputable def apm_m94J02_diagonalLinear :
    lp (fun _ : ℕ => ℂ) 1 →ₗ[ℂ] lp (fun _ : ℕ => ℂ) 1 where
  toFun := apm_m94J02_diagonalFun
  map_add' x y := by
    apply lp.ext
    funext n
    change (2 : ℂ) ^ (-(n : ℤ)) * (x n + y n) =
      (2 : ℂ) ^ (-(n : ℤ)) * x n + (2 : ℂ) ^ (-(n : ℤ)) * y n
    ring
  map_smul' c x := by
    apply lp.ext
    funext n
    simp [apm_m94J02_diagonalFun_apply]
    ring

noncomputable def apm_m94J02_diagonal :
    lp (fun _ : ℕ => ℂ) 1 →L[ℂ] lp (fun _ : ℕ => ℂ) 1 :=
  LinearMap.mkContinuous apm_m94J02_diagonalLinear 1 fun x => by
    simpa using apm_m94J02_diagonalFun_norm_le x

@[simp] lemma apm_m94J02_diagonal_apply
    (x : lp (fun _ : ℕ => ℂ) 1) (n : ℕ) :
    apm_m94J02_diagonal x n = (2 : ℂ) ^ (-(n : ℤ)) * x n := by
  rfl

lemma apm_m94J02_diagonal_norm_le : ‖apm_m94J02_diagonal‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simpa using apm_m94J02_diagonalFun_norm_le x

lemma apm_m94J02_truncation_apply (N : ℕ)
    (x : lp (fun _ : ℕ => ℂ) 1) (i : ℕ) :
    apm_m94J02_truncation N x i =
      if i < N then (2 : ℂ) ^ (-(i : ℤ)) * x i else 0 := by
  classical
  simp only [apm_m94J02_truncation, ContinuousLinearMap.sum_apply,
    apm_m94J02_rankOne_apply, lp.coeFn_sum, lp.coeFn_single]
  have h := Finset.sum_pi_single i
    (fun j => (2 : ℂ) ^ (-(j : ℤ)) * x j) (Finset.range N)
  simpa using h

lemma apm_m94J02_diagonal_sub_truncation_norm_le (N : ℕ)
    (x : lp (fun _ : ℕ => ℂ) 1) :
    ‖(apm_m94J02_diagonal - apm_m94J02_truncation N) x‖ ≤
      (2 : ℝ) ^ (-(N : ℤ)) * ‖x‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
  simp only [ENNReal.toReal_one, Real.rpow_one]
  rw [show (1 / (1 : ℝ)) = 1 by norm_num, Real.rpow_one, Real.rpow_one]
  calc
    ∑' i : ℕ, ‖((apm_m94J02_diagonal - apm_m94J02_truncation N) x) i‖ =
        ∑' i : ℕ, ‖apm_m94J02_diagonal x i -
          apm_m94J02_truncation N x i‖ := by
            rfl
    _ ≤ ∑' i : ℕ, (2 : ℝ) ^ (-(N : ℤ)) * ‖x i‖ := by
      apply Summable.tsum_le_tsum
      · intro i
        by_cases hi : i < N
        · rw [apm_m94J02_diagonal_apply,
            apm_m94J02_truncation_apply, if_pos hi, sub_self, norm_zero]
          positivity
        · rw [apm_m94J02_diagonal_apply,
            apm_m94J02_truncation_apply, if_neg hi, sub_zero, norm_mul]
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          rw [norm_zpow]
          norm_num
          apply inv_anti₀ (by positivity)
          exact pow_le_pow_right₀ (by norm_num) (Nat.le_of_not_gt hi)
      · have hs := ((lp.memℓp
            ((apm_m94J02_diagonal - apm_m94J02_truncation N) x)).summable
              (by norm_num))
        convert hs using 1
        funext i
        rw [ENNReal.toReal_one, Real.rpow_one]
        change ‖apm_m94J02_diagonal x i - apm_m94J02_truncation N x i‖ =
          ‖apm_m94J02_diagonal x i - apm_m94J02_truncation N x i‖
        rfl
      · exact Summable.mul_left _ (by
          simpa [Real.rpow_one] using (lp.memℓp x).summable (by norm_num))
    _ = (2 : ℝ) ^ (-(N : ℤ)) * ∑' i : ℕ, ‖x i‖ := by
      rw [tsum_mul_left]

lemma apm_m94J02_diagonal_sub_truncation_opNorm_le (N : ℕ) :
    ‖apm_m94J02_diagonal - apm_m94J02_truncation N‖ ≤
      (2 : ℝ) ^ (-(N : ℤ)) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  exact apm_m94J02_diagonal_sub_truncation_norm_le N x

lemma apm_m94J02_geometric_tendsto_zero :
    Tendsto (fun N : ℕ => (2 : ℝ) ^ (-(N : ℤ))) atTop (nhds 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_norm_lt_one
    (show ‖(2 : ℝ)⁻¹‖ < 1 by norm_num)
  convert h using 1
  funext N
  simp [zpow_neg, inv_pow]

lemma apm_m94J02_truncation_tendsto_diagonal :
    Tendsto apm_m94J02_truncation atTop (nhds apm_m94J02_diagonal) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun N => norm_nonneg _)
    (fun N => ?_) apm_m94J02_geometric_tendsto_zero
  simpa [norm_sub_rev] using
    apm_m94J02_diagonal_sub_truncation_opNorm_le N

lemma apm_m94J02_diagonal_compact :
    IsCompactOperator apm_m94J02_diagonal := by
  apply isCompactOperator_of_tendsto apm_m94J02_truncation_tendsto_diagonal
  filter_upwards [] with N
  exact apm_m94J02_truncation_compact N

/-- Completeness of the frozen weighted coefficient norm, transported from
the complete `ℓ¹` space by the exact weighted isometry. -/
lemma apm_m94J02_weighted_complete :
    ∀ a : ℕ → ℕ → ℂ,
      (∀ k, apm_m94J02_mem (a k)) →
      (∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
        apm_m94J02_norm (fun k ↦ a m k - a n k) < ε) →
      ∃ b, apm_m94J02_mem b ∧
        ∀ ε > 0, ∃ N, ∀ n ≥ N,
          apm_m94J02_norm (fun k ↦ a n k - b k) < ε := by
  intro a ha hc
  choose x hx hxn using fun k => apm_m94J02_exists_weighted_lp (a k) (ha k)
  have hxc : CauchySeq x := by
    apply Metric.cauchySeq_iff.2
    intro ε hε
    obtain ⟨N, hN⟩ := hc ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm, apm_m94J02_weighted_lp_sub_norm (a m) (a n)
      (x m) (x n) (hx m) (hx n)]
    exact hN m hm n hn
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hxc
  let b : ℕ → ℂ := fun n =>
    (Complex.ofReal ((n : ℝ) ^ 2 + 1))⁻¹ * y n
  have hby (n : ℕ) :
      Complex.ofReal ((n : ℝ) ^ 2 + 1) * b n = y n := by
    dsimp [b]
    rw [← mul_assoc, mul_inv_cancel₀]
    · simp
    · exact Complex.ofReal_ne_zero.mpr (by positivity)
  have hb : apm_m94J02_mem b := by
    have hysum : Summable (fun n => ‖y n‖) := by
      have hys := (lp.memℓp y).summable (by norm_num)
      simpa using hys
    unfold apm_m94J02_mem
    convert hysum using 1
    funext n
    have hw : ‖Complex.ofReal ((n : ℝ) ^ 2 + 1)‖ = (n : ℝ) ^ 2 + 1 := by
      exact (Complex.norm_real _).trans <|
        (Real.norm_eq_abs _).trans (abs_of_nonneg (by positivity))
    calc
      ‖b n‖ * ((n : ℝ) ^ 2 + 1) =
          ‖Complex.ofReal ((n : ℝ) ^ 2 + 1) * b n‖ := by
            rw [hby n]
            dsimp [b]
            rw [norm_mul, norm_inv, hw]
            field_simp
      _ = ‖y n‖ := by rw [hby n]
  obtain ⟨z, hz, hzn⟩ := apm_m94J02_exists_weighted_lp b hb
  have hzy : z = y := by
    apply lp.ext
    funext n
    rw [hz n, hby n]
  subst z
  refine ⟨b, hb, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero] at hy
  intro ε hε
  have hev := hy.eventually (gt_mem_nhds hε)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun n hn => ?_⟩
  rw [← apm_m94J02_weighted_lp_sub_norm (a n) b (x n) y (hx n) hz]
  exact hN n hn

/-- A nonzero sequence has an explicit exponential lower bound on its power
norms, furnished by its first nonzero formal-series coefficient. -/
lemma apm_m94J02_norm_pow_lower_at_order (a : ℕ → ℂ)
    (ha : apm_m94J02_mem a) (ha0 : a ≠ 0) (n : ℕ) :
    ‖a (PowerSeries.mk a).order.toNat‖ ^ n ≤
      apm_m94J02_norm (apm_m94J02_pow a n) := by
  let j := (PowerSeries.mk a).order.toNat
  have hc := apm_m94J02_weighted_coordinate_le_norm
    (apm_m94J02_pow a n) (apm_m94J02_pow_mem a ha n) (n * j)
  rw [apm_m94J02_pow_coeff_at_order a ha0 n, norm_pow] at hc
  calc
    ‖a j‖ ^ n ≤ ‖a j‖ ^ n * (((n * j : ℕ) : ℝ) ^ 2 + 1) := by
      nlinarith [pow_nonneg (norm_nonneg (a j)) n]
    _ ≤ apm_m94J02_norm (apm_m94J02_pow a n) := hc

/-- The logarithmic quotients in the nonzero branch have an explicit uniform
lower bound, as required by Fekete's lemma. -/
lemma apm_m94J02_log_rescaled_norm_pow_bddBelow (a : ℕ → ℂ)
    (ha : apm_m94J02_mem a) (ha0 : a ≠ 0)
    (hpos : ∀ n, 0 < (5 / 4 : ℝ) *
      apm_m94J02_norm (apm_m94J02_pow a n)) :
    BddBelow (Set.range fun n : ℕ =>
      Real.log ((5 / 4 : ℝ) *
        apm_m94J02_norm (apm_m94J02_pow a n)) / n) := by
  let j := (PowerSeries.mk a).order.toNat
  let c : ℝ := ‖a j‖
  have hf : PowerSeries.mk a ≠ 0 := by
    intro h
    apply ha0
    apply apm_m94J02_powerSeries_mk_injective
    simpa using h
  have hc : 0 < c := by
    dsimp [c, j]
    exact norm_pos_iff.mpr (by
      simpa using (PowerSeries.coeff_order hf))
  refine ⟨min 0 (Real.log c), ?_⟩
  rintro y ⟨n, rfl⟩
  by_cases hn : n = 0
  · subst n
    simp
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  have hlower := apm_m94J02_norm_pow_lower_at_order a ha ha0 n
  have hnorm := apm_m94J02_norm_nonneg (apm_m94J02_pow a n)
  have hscale : apm_m94J02_norm (apm_m94J02_pow a n) ≤
      (5 / 4 : ℝ) * apm_m94J02_norm (apm_m94J02_pow a n) := by
    nlinarith
  have hpow : c ^ n ≤ (5 / 4 : ℝ) *
      apm_m94J02_norm (apm_m94J02_pow a n) :=
    le_trans (by simpa [c, j] using hlower) hscale
  have hlog : Real.log (c ^ n) ≤ Real.log ((5 / 4 : ℝ) *
      apm_m94J02_norm (apm_m94J02_pow a n)) :=
    Real.strictMonoOn_log.monotoneOn (pow_pos hc n) (hpos n) hpow
  rw [Real.log_pow] at hlog
  apply le_trans (min_le_right 0 (Real.log c))
  exact (le_div_iff₀ hnpos).2 (by simpa [mul_comm] using hlog)

/-- The norms of arbitrary two powers obey the sharp product estimate. -/
lemma apm_m94J02_norm_pow_add_le (a : ℕ → ℂ) (ha : apm_m94J02_mem a)
    (m n : ℕ) :
    apm_m94J02_norm (apm_m94J02_pow a (m + n)) ≤
      (5 / 4 : ℝ) * apm_m94J02_norm (apm_m94J02_pow a m) *
        apm_m94J02_norm (apm_m94J02_pow a n) := by
  rw [apm_m94J02_pow_add]
  exact (apm_m94J02_mul_mem_norm_le
    (apm_m94J02_pow a m) (apm_m94J02_pow a n)
    (apm_m94J02_pow_mem a ha m) (apm_m94J02_pow_mem a ha n)).2

/-- Multiplying every power norm by the algebra constant turns the preceding
estimate into ordinary submultiplicativity. -/
lemma apm_m94J02_rescaled_norm_pow_add_le (a : ℕ → ℂ)
    (ha : apm_m94J02_mem a) (m n : ℕ) :
    (5 / 4 : ℝ) * apm_m94J02_norm (apm_m94J02_pow a (m + n)) ≤
      ((5 / 4 : ℝ) * apm_m94J02_norm (apm_m94J02_pow a m)) *
        ((5 / 4 : ℝ) * apm_m94J02_norm (apm_m94J02_pow a n)) := by
  have h := apm_m94J02_norm_pow_add_le a ha m n
  nlinarith [apm_m94J02_norm_nonneg (apm_m94J02_pow a m),
    apm_m94J02_norm_nonneg (apm_m94J02_pow a n)]

/-- If no rescaled power norm vanishes, their logarithms form the
subadditive sequence to which Fekete's lemma applies. -/
lemma apm_m94J02_log_rescaled_norm_pow_subadditive (a : ℕ → ℂ)
    (ha : apm_m94J02_mem a)
    (hpos : ∀ n, 0 < (5 / 4 : ℝ) *
      apm_m94J02_norm (apm_m94J02_pow a n)) :
    Subadditive (fun n => Real.log ((5 / 4 : ℝ) *
      apm_m94J02_norm (apm_m94J02_pow a n))) := by
  intro m n
  have hm := hpos m
  have hn := hpos n
  rw [← Real.log_mul hm.ne' hn.ne']
  exact Real.strictMonoOn_log.monotoneOn
    (hpos (m + n)) (mul_pos hm hn)
    (apm_m94J02_rescaled_norm_pow_add_le a ha m n)

/-- In the strictly-positive branch, Fekete's lemma gives convergence of the
roots of the rescaled power norms. -/
lemma apm_m94J02_rescaled_root_tendsto (a : ℕ → ℂ)
    (ha : apm_m94J02_mem a) (ha0 : a ≠ 0)
    (hpos : ∀ n, 0 < (5 / 4 : ℝ) *
      apm_m94J02_norm (apm_m94J02_pow a n)) :
    ∃ L : ℝ, Tendsto
      (fun n : ℕ => Real.rpow
        ((5 / 4 : ℝ) * apm_m94J02_norm (apm_m94J02_pow a n))
        ((n : ℝ)⁻¹)) atTop (nhds L) := by
  let u : ℕ → ℝ := fun n => Real.log ((5 / 4 : ℝ) *
    apm_m94J02_norm (apm_m94J02_pow a n))
  have hu : Subadditive u :=
    apm_m94J02_log_rescaled_norm_pow_subadditive a ha hpos
  have hbdd : BddBelow (Set.range fun n : ℕ => u n / n) :=
    apm_m94J02_log_rescaled_norm_pow_bddBelow a ha ha0 hpos
  refine ⟨Real.exp hu.lim, ?_⟩
  have hlim : Tendsto (fun n : ℕ => u n / n) atTop (nhds hu.lim) :=
    hu.tendsto_lim hbdd
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hlim
  apply hexp.congr'
  filter_upwards with n
  change Real.exp (u n / (n : ℝ)) = _
  rw [Real.rpow_eq_pow, Real.rpow_def_of_pos (hpos n)]
  congr 1

/-- The nth root of the fixed algebra constant tends to one. -/
lemma apm_m94J02_algebra_constant_root_tendsto_one :
    Tendsto (fun n : ℕ => Real.rpow (5 / 4 : ℝ) ((n : ℝ)⁻¹))
      atTop (nhds 1) := by
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hmul : Tendsto (fun n : ℕ => Real.log (5 / 4 : ℝ) * ((n : ℝ)⁻¹))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hinv
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hmul
  convert hexp using 1
  · funext n
    rw [Real.rpow_eq_pow, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 5 / 4)]
    rfl
  · simp

/-- Removing the fixed `5/4` rescaling preserves convergence of the root
sequence in the strictly-positive branch. -/
lemma apm_m94J02_root_tendsto_of_all_pos (a : ℕ → ℂ)
    (ha : apm_m94J02_mem a) (ha0 : a ≠ 0)
    (hpos : ∀ n, 0 < (5 / 4 : ℝ) *
      apm_m94J02_norm (apm_m94J02_pow a n)) :
    ∃ L : ℝ, Tendsto
      (fun n : ℕ => Real.rpow (apm_m94J02_norm (apm_m94J02_pow a n))
        ((n : ℝ)⁻¹)) atTop (nhds L) := by
  obtain ⟨L, hL⟩ := apm_m94J02_rescaled_root_tendsto a ha ha0 hpos
  refine ⟨L, ?_⟩
  have hdiv := hL.div apm_m94J02_algebra_constant_root_tendsto_one
    (by norm_num : (1 : ℝ) ≠ 0)
  have hdiv' : Tendsto
      ((fun n : ℕ => Real.rpow
          ((5 / 4 : ℝ) * apm_m94J02_norm (apm_m94J02_pow a n)) ((n : ℝ)⁻¹)) /
        (fun n : ℕ => Real.rpow (5 / 4 : ℝ) ((n : ℝ)⁻¹)))
      atTop (nhds L) := by simpa using hdiv
  apply hdiv'.congr'
  filter_upwards with n
  have hnorm : 0 ≤ apm_m94J02_norm (apm_m94J02_pow a n) :=
    apm_m94J02_norm_nonneg _
  change Real.rpow ((5 / 4 : ℝ) * apm_m94J02_norm (apm_m94J02_pow a n))
      ((n : ℝ)⁻¹) / Real.rpow (5 / 4 : ℝ) ((n : ℝ)⁻¹) =
    Real.rpow (apm_m94J02_norm (apm_m94J02_pow a n)) ((n : ℝ)⁻¹)
  rw [Real.rpow_eq_pow, Real.rpow_eq_pow, Real.rpow_eq_pow,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 5 / 4) hnorm]
  field_simp

/-- Once one power has zero norm, every later power has zero norm. -/
lemma apm_m94J02_norm_pow_eventually_zero (a : ℕ → ℂ)
    (ha : apm_m94J02_mem a) {m : ℕ}
    (hm : apm_m94J02_norm (apm_m94J02_pow a m) = 0) :
    ∀ n ≥ m, apm_m94J02_norm (apm_m94J02_pow a n) = 0 := by
  intro n hmn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  apply le_antisymm
  · calc
      apm_m94J02_norm (apm_m94J02_pow a (m + k)) ≤
          (5 / 4 : ℝ) * apm_m94J02_norm (apm_m94J02_pow a m) *
            apm_m94J02_norm (apm_m94J02_pow a k) :=
        apm_m94J02_norm_pow_add_le a ha m k
      _ = 0 := by rw [hm]; ring
  · exact apm_m94J02_norm_nonneg _

/-- The root sequence converges to zero in the branch where some power norm
vanishes. -/
lemma apm_m94J02_root_tendsto_zero_of_norm_pow_eq_zero (a : ℕ → ℂ)
    (ha : apm_m94J02_mem a) {m : ℕ}
    (hm : apm_m94J02_norm (apm_m94J02_pow a m) = 0) :
    Tendsto
      (fun n : ℕ ↦ Real.rpow (apm_m94J02_norm (apm_m94J02_pow a n))
        ((n : ℝ)⁻¹)) atTop (nhds 0) := by
  have heq :
    (fun n : ℕ ↦ Real.rpow (apm_m94J02_norm (apm_m94J02_pow a n))
      ((n : ℝ)⁻¹)) =ᶠ[atTop] (fun _ : ℕ => (0 : ℝ)) := by
    filter_upwards [eventually_ge_atTop (max m 1)] with n hn
    have hmn : m ≤ n := le_trans (Nat.le_max_left _ _) hn
    have hn1 : 1 ≤ n := le_trans (Nat.le_max_right _ _) hn
    rw [apm_m94J02_norm_pow_eventually_zero a ha hm n hmn]
    exact Real.zero_rpow (ne_of_gt (inv_pos.mpr
      (by exact_mod_cast (show 0 < n from zero_lt_one.trans_le hn1))))
  exact Filter.EventuallyEq.tendsto heq

/-- Every weighted-summable coefficient sequence has a convergent power-root
norm sequence. -/
lemma apm_m94J02_exists_root_limit (a : ℕ → ℂ) (ha : apm_m94J02_mem a) :
    ∃ L : ℝ, Tendsto
      (fun n : ℕ ↦ Real.rpow (apm_m94J02_norm (apm_m94J02_pow a n))
        ((n : ℝ)⁻¹)) atTop (nhds L) := by
  by_cases hz : ∃ m, apm_m94J02_norm (apm_m94J02_pow a m) = 0
  · obtain ⟨m, hm⟩ := hz
    exact ⟨0, apm_m94J02_root_tendsto_zero_of_norm_pow_eq_zero a ha hm⟩
  · have ha0 : a ≠ 0 := by
      intro ha_zero
      apply hz
      refine ⟨1, ?_⟩
      have hp : apm_m94J02_pow a 1 = 0 := by
        apply apm_m94J02_powerSeries_mk_injective
        rw [apm_m94J02_powerSeries_mk_pow, ha_zero]
        simp
      rw [hp]
      simp [apm_m94J02_norm]
    have hpos : ∀ n, 0 < (5 / 4 : ℝ) *
        apm_m94J02_norm (apm_m94J02_pow a n) := by
      intro n
      apply mul_pos (by norm_num)
      exact lt_of_le_of_ne (apm_m94J02_norm_nonneg _)
        (Ne.symm (not_exists.mp hz n))
    exact apm_m94J02_root_tendsto_of_all_pos a ha ha0 hpos

/-- Exact norm of a coordinate vector. -/
lemma apm_m94J02_norm_single (j : ℕ) (c : ℂ) :
    apm_m94J02_norm (fun n ↦ if n = j then c else 0) =
      ‖c‖ * ((j : ℝ) ^ 2 + 1) := by
  unfold apm_m94J02_norm
  rw [tsum_eq_single j]
  · simp
  · intro n hn
    simp [hn]

/-- Zero belongs to the custom spectrum: a bounded inverse would have to
undo diagonal factors `2⁻ʲ` on all coordinate vectors. -/
lemma apm_m94J02_zero_mem_spectrum :
    (0 : ℂ) ∈ apm_m94J02_spectrum := by
  intro hS
  rcases hS with ⟨S, hSmem, ⟨C, hC, hbound⟩, hleft, _⟩
  obtain ⟨j, hj⟩ : ∃ j : ℕ, C < (2 : ℝ) ^ j :=
    (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).eventually_gt_atTop C |>.exists
  let e : ℕ → ℂ := fun n ↦ if n = j then 1 else 0
  have he_mem : apm_m94J02_mem e := by
    unfold apm_m94J02_mem e
    apply summable_of_hasFiniteSupport
    exact (Set.finite_singleton j).subset (by
      intro n hn
      by_contra hnj
      apply hn
      have hne : n ≠ j := by simpa using hnj
      simp [hne])
  have hleft' : S (apm_m94J02_T e) = e := by
    simpa using hleft e he_mem
  have hTe : apm_m94J02_T e =
      (fun n ↦ if n = j then (2 : ℂ) ^ (-(j : ℤ)) else 0) := by
    funext n
    by_cases hnj : n = j
    · subst n
      simp [apm_m94J02_T, e]
    · simp [apm_m94J02_T, e, hnj]
  have hTe_mem : apm_m94J02_mem (apm_m94J02_T e) := by
    rw [hTe]
    unfold apm_m94J02_mem
    apply summable_of_hasFiniteSupport
    exact (Set.finite_singleton j).subset (by
      intro n hn
      by_contra hnj
      apply hn
      have hne : n ≠ j := by simpa using hnj
      simp [hne])
  have hineq := hbound (apm_m94J02_T e)
    hTe_mem
  rw [hleft', hTe, apm_m94J02_norm_single,
    apm_m94J02_norm_single] at hineq
  norm_num [norm_zpow] at hineq
  have hw : 0 < (j : ℝ) ^ 2 + 1 := by positivity
  have hpow : C * ((2 : ℝ) ^ j)⁻¹ < 1 := by
    rw [mul_inv_lt_iff₀ (by positivity)]
    simpa using hj
  nlinarith

/-- The proposed spectral set is contained in the custom spectrum. -/
lemma apm_m94J02_proposed_spectrum_subset :
    ({0} ∪ Set.range (fun n : ℕ ↦ (2 : ℂ) ^ (-(n : ℤ)))) ⊆
      apm_m94J02_spectrum := by
  intro z hz
  rcases hz with hz | hz
  · rcases hz with rfl
    exact apm_m94J02_zero_mem_spectrum
  · exact apm_m94J02_diagonal_range_subset_spectrum hz

/-- Outside zero and the diagonal range, coordinatewise division gives the
bounded two-sided inverse required by the custom spectrum definition. -/
lemma apm_m94J02_spectrum_subset_proposed :
    apm_m94J02_spectrum ⊆
      {0} ∪ Set.range (fun n : ℕ ↦ (2 : ℂ) ^ (-(n : ℤ))) := by
  intro z hzspec
  by_contra hzout
  have hz0 : z ≠ 0 := by
    intro hz
    apply hzout
    left
    simpa [hz]
  have hden (n : ℕ) : (2 : ℂ) ^ (-(n : ℤ)) - z ≠ 0 := by
    intro h
    apply hzout
    right
    refine ⟨n, ?_⟩
    exact sub_eq_zero.mp h
  let q : ℕ → ℂ := fun n ↦ ((2 : ℂ) ^ (-(n : ℤ)) - z)⁻¹
  have hd : Tendsto (fun n : ℕ ↦ (2 : ℂ) ^ (-(n : ℤ))) atTop (nhds 0) := by
    convert tendsto_pow_atTop_nhds_zero_of_norm_lt_one
      (x := (2 : ℂ)⁻¹) (by norm_num) using 1
    ext n
    simp [zpow_neg, inv_pow]
  have hq : Tendsto q atTop (nhds ((-z)⁻¹)) := by
    have hsub : Tendsto (fun n : ℕ ↦ (2 : ℂ) ^ (-(n : ℤ)) - z)
        atTop (nhds (0 - z)) := hd.sub tendsto_const_nhds
    simpa [q] using hsub.inv₀ (by simpa using hz0)
  have hbdd : BddAbove (Set.range fun n ↦ ‖q n‖) := hq.norm.bddAbove_range
  obtain ⟨C, hC⟩ := hbdd
  have hqC (n : ℕ) : ‖q n‖ ≤ C := hC ⟨n, rfl⟩
  have hC0 : 0 ≤ C := (norm_nonneg (q 0)).trans (hqC 0)
  let S : (ℕ → ℂ) → (ℕ → ℂ) := fun a n ↦ q n * a n
  have hSmem : ∀ a, apm_m94J02_mem a → apm_m94J02_mem (S a) := by
    intro a ha
    unfold apm_m94J02_mem at ha ⊢
    dsimp [S]
    refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun n ↦ ?_)
      (ha.mul_left C)
    rw [norm_mul]
    calc
      ‖q n‖ * ‖a n‖ * ((n : ℝ) ^ 2 + 1) ≤
          (C * ‖a n‖) * ((n : ℝ) ^ 2 + 1) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hqC n) (norm_nonneg (a n))) (by positivity)
      _ = C * (‖a n‖ * ((n : ℝ) ^ 2 + 1)) := by ring
  have hSbound : ∀ a, apm_m94J02_mem a →
      apm_m94J02_norm (S a) ≤ C * apm_m94J02_norm a := by
    intro a ha
    unfold apm_m94J02_norm
    dsimp [S]
    have hSa := hSmem a ha
    unfold apm_m94J02_mem at hSa ha
    calc
      ∑' n, ‖q n * a n‖ * ((n : ℝ) ^ 2 + 1) ≤
          ∑' n, C * (‖a n‖ * ((n : ℝ) ^ 2 + 1)) := by
        apply Summable.tsum_le_tsum
        · intro n
          rw [norm_mul]
          calc
            ‖q n‖ * ‖a n‖ * ((n : ℝ) ^ 2 + 1) ≤
                (C * ‖a n‖) * ((n : ℝ) ^ 2 + 1) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (hqC n) (norm_nonneg (a n))) (by positivity)
            _ = C * (‖a n‖ * ((n : ℝ) ^ 2 + 1)) := by ring
        · exact hSa
        · exact ha.mul_left C
      _ = C * ∑' n, ‖a n‖ * ((n : ℝ) ^ 2 + 1) := by rw [tsum_mul_left]
  apply hzspec
  refine ⟨S, hSmem, ⟨C, hC0, hSbound⟩, ?_, ?_⟩
  · intro a ha
    funext n
    dsimp [S, q, apm_m94J02_T]
    rw [← sub_mul, ← mul_assoc, inv_mul_cancel₀ (hden n)]
    simp
  · intro a ha
    funext n
    dsimp [S, q, apm_m94J02_T]
    rw [← sub_mul, ← mul_assoc, mul_inv_cancel₀ (hden n)]
    simp

/-- The weighted coefficient space is closed under addition. -/
lemma apm_m94J02_mem_add {a b : ℕ → ℂ}
    (ha : apm_m94J02_mem a) (hb : apm_m94J02_mem b) :
    apm_m94J02_mem (fun n ↦ a n + b n) := by
  unfold apm_m94J02_mem at ha hb ⊢
  refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun n ↦ ?_)
    (ha.add hb)
  calc
    ‖a n + b n‖ * ((n : ℝ) ^ 2 + 1)
        ≤ (‖a n‖ + ‖b n‖) * ((n : ℝ) ^ 2 + 1) :=
          mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)
    _ = ‖a n‖ * ((n : ℝ) ^ 2 + 1) + ‖b n‖ * ((n : ℝ) ^ 2 + 1) := by ring

/-- The weighted coefficient space is closed under complex scalar
multiplication. -/
lemma apm_m94J02_mem_smul (c : ℂ) {a : ℕ → ℂ} (ha : apm_m94J02_mem a) :
    apm_m94J02_mem (fun n ↦ c * a n) := by
  unfold apm_m94J02_mem at ha ⊢
  convert ha.mul_left ‖c‖ using 1
  funext n
  rw [norm_mul]
  ring

/-- The custom weighted norm is homogeneous for complex scalars. -/
lemma apm_m94J02_norm_smul (c : ℂ) (a : ℕ → ℂ) :
    apm_m94J02_norm (fun n ↦ c * a n) = ‖c‖ * apm_m94J02_norm a := by
  unfold apm_m94J02_norm
  show ∑' n, ‖c * a n‖ * ((n : ℝ) ^ 2 + 1) =
    ‖c‖ * ∑' n, ‖a n‖ * ((n : ℝ) ^ 2 + 1)
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [norm_mul]
  ring

/-- The triangle inequality for the custom weighted norm. -/
lemma apm_m94J02_norm_add_le {a b : ℕ → ℂ}
    (ha : apm_m94J02_mem a) (hb : apm_m94J02_mem b) :
    apm_m94J02_norm (fun n ↦ a n + b n) ≤
      apm_m94J02_norm a + apm_m94J02_norm b := by
  unfold apm_m94J02_norm
  have hab := apm_m94J02_mem_add ha hb
  unfold apm_m94J02_mem at hab ha hb
  rw [← Summable.tsum_add ha hb]
  exact Summable.tsum_le_tsum (fun n ↦ by
    calc
      ‖a n + b n‖ * ((n : ℝ) ^ 2 + 1)
          ≤ (‖a n‖ + ‖b n‖) * ((n : ℝ) ^ 2 + 1) :=
            mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)
      _ = ‖a n‖ * ((n : ℝ) ^ 2 + 1) + ‖b n‖ * ((n : ℝ) ^ 2 + 1) := by ring)
    hab (ha.add hb)

/-- On members of `X` the coefficient series is summable at every point of
the closed unit disk, so evaluation never uses a `tsum` junk value. -/
lemma apm_m94J02_summable_eval (a : ℕ → ℂ) (ha : apm_m94J02_mem a)
    (z : ℂ) (hz : z ∈ Metric.closedBall 0 1) :
    Summable (fun n ↦ a n * z ^ n) := by
  have hz1 : ‖z‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hz
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
    (apm_m94J02_summable_norm a ha)
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg _) hz1)

/-- The Cauchy product evaluates to the pointwise product of the represented
functions on the closed unit disk. -/
lemma apm_m94J02_eval_mul (a b : ℕ → ℂ)
    (ha : apm_m94J02_mem a) (hb : apm_m94J02_mem b)
    (z : ℂ) (hz : z ∈ Metric.closedBall 0 1) :
    apm_m94J02_eval (apm_m94J02_mul a b) z =
      apm_m94J02_eval a z * apm_m94J02_eval b z := by
  have hsa := (apm_m94J02_summable_eval a ha z hz).norm
  have hsb := (apm_m94J02_summable_eval b hb z hz).norm
  have hkey := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hsa hsb
  unfold apm_m94J02_eval
  rw [hkey]
  apply tsum_congr
  intro n
  unfold apm_m94J02_mul
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simpa [Finset.mem_range] using hk
  have hpow : z ^ n = z ^ k * z ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_of_le hkn]
  calc
    a k * b (n - k) * z ^ n = a k * b (n - k) * (z ^ k * z ^ (n - k)) := by
      rw [hpow]
    _ = a k * z ^ k * (b (n - k) * z ^ (n - k)) := by ring

/-- The coefficientwise dilation evaluates to the printed operator
`Tf(z) = f(z/2)` on the closed unit disk; both series are summable there. -/
lemma apm_m94J02_eval_T (a : ℕ → ℂ) (ha : apm_m94J02_mem a)
    (z : ℂ) (hz : z ∈ Metric.closedBall 0 1) :
    apm_m94J02_eval (apm_m94J02_T a) z = apm_m94J02_eval a (z / 2) := by
  have hz1 : ‖z‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hz
  have hz2 : z / 2 ∈ Metric.closedBall 0 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_div]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2]
    rw [div_le_one (by norm_num : (0 : ℝ) < 2)]
    exact hz1.trans (by norm_num)
  have hsa := apm_m94J02_summable_eval a ha (z / 2) hz2
  have hsTa : Summable (fun n ↦ apm_m94J02_T a n * z ^ n) := by
    apply Summable.of_norm
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
      (apm_m94J02_summable_norm a ha)
    simp only [apm_m94J02_T]
    rw [norm_mul, norm_mul, norm_zpow, norm_pow]
    have hs : ‖(2 : ℂ)‖ ^ (-(n : ℤ)) ≤ 1 := by
      have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [h2]
      exact zpow_le_one_of_nonpos₀ (by norm_num) (by simp)
    have h1 : ‖(2 : ℂ)‖ ^ (-(n : ℤ)) * ‖a n‖ ≤ 1 * ‖a n‖ :=
      mul_le_mul_of_nonneg_right hs (norm_nonneg _)
    have h2 : ‖z‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg _) hz1
    calc
      ‖(2 : ℂ)‖ ^ (-(n : ℤ)) * ‖a n‖ * ‖z‖ ^ n
          ≤ (1 * ‖a n‖) * ‖z‖ ^ n :=
            mul_le_mul_of_nonneg_right h1 (pow_nonneg (norm_nonneg _) _)
      _ ≤ (1 * ‖a n‖) * 1 :=
            mul_le_mul_of_nonneg_left h2
              (mul_nonneg zero_le_one (norm_nonneg _))
      _ = ‖a n‖ := by ring
  unfold apm_m94J02_eval
  apply tsum_congr
  intro n
  simp only [apm_m94J02_T]
  have h2 : (2 : ℂ) ^ (-(n : ℤ)) = (2⁻¹) ^ n := by
    rw [zpow_neg, zpow_natCast, inv_pow]
  rw [h2, div_eq_mul_inv, mul_pow]
  ring

theorem apm_m94j02 :
    (∀ a : ℕ → ℕ → ℂ,
        (∀ k, apm_m94J02_mem (a k)) →
        (∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
          apm_m94J02_norm (fun k ↦ a m k - a n k) < ε) →
        ∃ b, apm_m94J02_mem b ∧
          ∀ ε > 0, ∃ N, ∀ n ≥ N,
            apm_m94J02_norm (fun k ↦ a n k - b k) < ε) ∧
      (∀ a, apm_m94J02_mem a →
        ContinuousOn (apm_m94J02_eval a) (Metric.closedBall 0 1)) ∧
      (∀ a b, apm_m94J02_mem a → apm_m94J02_mem b →
        apm_m94J02_mem (apm_m94J02_mul a b) ∧
        apm_m94J02_norm (apm_m94J02_mul a b) ≤
          (5 / 4 : ℝ) * apm_m94J02_norm a * apm_m94J02_norm b) ∧
      (∀ a, apm_m94J02_mem a →
        ∃ L : ℝ, Tendsto
          (fun n : ℕ ↦ Real.rpow (apm_m94J02_norm (apm_m94J02_pow a n))
            ((n : ℝ)⁻¹)) atTop (nhds L)) ∧
      (∀ a, apm_m94J02_mem a → apm_m94J02_mem (apm_m94J02_T a)) ∧
      (∀ a : ℕ → ℕ → ℂ,
        (∀ k, apm_m94J02_mem (a k) ∧ apm_m94J02_norm (a k) ≤ 1) →
        ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ b, apm_m94J02_mem b ∧
          Tendsto (fun k ↦ apm_m94J02_norm
            (fun n ↦ apm_m94J02_T (a (σ k)) n - b n)) atTop (nhds 0)) ∧
      apm_m94J02_spectrum =
        {0} ∪ Set.range (fun n : ℕ ↦ (2 : ℂ) ^ (-(n : ℤ))) ∧
      (∀ a b : ℕ → ℂ, apm_m94J02_mem a → apm_m94J02_mem b →
        apm_m94J02_mem (fun n ↦ a n + b n)) ∧
      (∀ c : ℂ, ∀ a : ℕ → ℂ, apm_m94J02_mem a →
        apm_m94J02_mem (fun n ↦ c * a n)) ∧
      (∀ a : ℕ → ℂ, 0 ≤ apm_m94J02_norm a) ∧
      (∀ a : ℕ → ℂ, apm_m94J02_mem a →
        (apm_m94J02_norm a = 0 ↔ a = 0)) ∧
      (∀ c : ℂ, ∀ a : ℕ → ℂ,
        apm_m94J02_norm (fun n ↦ c * a n) = ‖c‖ * apm_m94J02_norm a) ∧
      (∀ a b : ℕ → ℂ, apm_m94J02_mem a → apm_m94J02_mem b →
        apm_m94J02_norm (fun n ↦ a n + b n) ≤
          apm_m94J02_norm a + apm_m94J02_norm b) ∧
      (∀ a b : ℕ → ℂ, apm_m94J02_mem a → apm_m94J02_mem b →
        ∀ z ∈ Metric.closedBall 0 1,
          apm_m94J02_eval (apm_m94J02_mul a b) z =
            apm_m94J02_eval a z * apm_m94J02_eval b z) ∧
      (∀ a : ℕ → ℂ, apm_m94J02_mem a →
        ∀ z ∈ Metric.closedBall 0 1,
          apm_m94J02_eval (apm_m94J02_T a) z =
            apm_m94J02_eval a (z / 2)) := by
  have hT_mem : ∀ a, apm_m94J02_mem a →
      apm_m94J02_mem (apm_m94J02_T a) := by
    intro a ha
    unfold apm_m94J02_mem at ha ⊢
    simp only [apm_m94J02_T]
    refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun n ↦ ?_) ha
    have hs : ‖(2 : ℂ) ^ (-(n : ℤ))‖ ≤ 1 := by
      rw [norm_zpow]
      exact zpow_le_one_of_nonpos₀ (by norm_num) (by simp)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_left (norm_nonneg (a n)) hs)
      (by positivity)
  /-
  Boundary: the remaining clauses require a full weighted-`ℓ¹` completeness
  proof, uniform convergence of the coefficient series on the closed disk,
  rearrangement of a nonnegative double series for the Cauchy product, and
  the sharp weight inequality with factor `5/4`. The power-limit clause then
  needs a Fekete/subadditivity argument that also handles zero powers.

  Compactness requires diagonal subsequence extraction for every unit-ball
  sequence and weighted tail control. The spectrum equality requires
  constructing bounded diagonal inverses away from the closed eigenvalue set,
  and exhibiting failure of surjectivity at zero in the statement's custom
  two-sided-inverse encoding. The local lemma
  `apm_m94J02_eigenvalue_mem_spectrum` now proves that every `2^(-n)` has no
  inverse, directly from the coordinate vector and the zero vector. I searched
  Mathlib's summability, Fekete, and diagonal operator APIs; no compiled
  sibling assembled these custom weighted-sequence arguments within this
  pass. The elementary dilation membership clause is proved above.

  Closer hop 2 additionally proves `apm_m94J02_norm_T_le`: the diagonal
  dilation is a contraction in the exact weighted norm.  This uses
  `Summable.tsum_le_tsum` with the coordinate estimate `‖2⁻ⁿ‖ ≤ 1` and
  supplies the quantitative input for both diagonal tail compactness and the
  bounded-inverse contradiction at zero.  Searches of `LEMMA-INDEX.md`, all
  closed artifacts, Mathlib diagonal-operator/summability sources, and the
  construction libraries found no packaged weighted-ℓ¹ compactness or custom
  spectrum theorem.  The remaining bridge therefore still requires the
  diagonal subsequence/tail construction and explicit reciprocal multiplier
  bounds away from `{0} ∪ range (2⁻ⁿ)`.

  Closer hop 3 packages the pointwise eigenvalue result into the set-level
  theorem `apm_m94J02_diagonal_range_subset_spectrum`. Consequently the
  diagonal-range half of the forward spectrum inclusion is complete. The
  point `0` still needs the bounded-inverse contradiction (coordinate vectors
  force inverse norms growing like `2^n`), while the reverse inclusion still
  needs uniform reciprocal bounds away from the closed diagonal set. Searches
  of Mathlib's zpow growth, diagonal multiplier, and spectrum APIs found no
  theorem matching this custom unbundled inverse encoding.
  -/
  have hremaining :
      (∀ a : ℕ → ℕ → ℂ,
          (∀ k, apm_m94J02_mem (a k)) →
          (∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
            apm_m94J02_norm (fun k ↦ a m k - a n k) < ε) →
          ∃ b, apm_m94J02_mem b ∧
            ∀ ε > 0, ∃ N, ∀ n ≥ N,
              apm_m94J02_norm (fun k ↦ a n k - b k) < ε) ∧
        (∀ a, apm_m94J02_mem a →
          ∃ L : ℝ, Tendsto
            (fun n : ℕ ↦ Real.rpow (apm_m94J02_norm (apm_m94J02_pow a n))
              ((n : ℝ)⁻¹)) atTop (nhds L)) ∧
        (∀ a : ℕ → ℕ → ℂ,
          (∀ k, apm_m94J02_mem (a k) ∧ apm_m94J02_norm (a k) ≤ 1) →
          ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ b, apm_m94J02_mem b ∧
            Tendsto (fun k ↦ apm_m94J02_norm
              (fun n ↦ apm_m94J02_T (a (σ k)) n - b n)) atTop (nhds 0)) := by
    have hcompact :
        ∀ a : ℕ → ℕ → ℂ,
          (∀ k, apm_m94J02_mem (a k) ∧ apm_m94J02_norm (a k) ≤ 1) →
          ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ b, apm_m94J02_mem b ∧
            Tendsto (fun k ↦ apm_m94J02_norm
              (fun n ↦ apm_m94J02_T (a (σ k)) n - b n)) atTop (nhds 0) := by
      intro a ha
      choose x hx hxn using fun k =>
        apm_m94J02_exists_weighted_lp (a k) (ha k).1
      have hxball (k : ℕ) : x k ∈ Metric.closedBall (0 :
          lp (fun _ : ℕ => ℂ) 1) 1 := by
        rw [Metric.mem_closedBall, dist_zero_right, hxn k]
        exact (ha k).2
      obtain ⟨K, hK, hDK⟩ :=
        apm_m94J02_diagonal_compact.image_closedBall_subset_compact 1
      have hseqK (k : ℕ) : apm_m94J02_diagonal (x k) ∈ K :=
        hDK ⟨x k, hxball k, rfl⟩
      obtain ⟨y, hyK, σ, hσ, hy⟩ := hK.tendsto_subseq hseqK
      let b : ℕ → ℂ := fun n =>
        (Complex.ofReal ((n : ℝ) ^ 2 + 1))⁻¹ * y n
      have hby (n : ℕ) :
          Complex.ofReal ((n : ℝ) ^ 2 + 1) * b n = y n := by
        dsimp [b]
        rw [← mul_assoc, mul_inv_cancel₀]
        · simp
        · exact Complex.ofReal_ne_zero.mpr (by positivity)
      have hb : apm_m94J02_mem b := by
        have hysum : Summable (fun n => ‖y n‖) := by
          have hys := (lp.memℓp y).summable (by norm_num)
          simpa using hys
        unfold apm_m94J02_mem
        convert hysum using 1
        funext n
        calc
          ‖b n‖ * ((n : ℝ) ^ 2 + 1) =
              ‖Complex.ofReal ((n : ℝ) ^ 2 + 1) * b n‖ := by
                rw [hby n]
                dsimp [b]
                rw [norm_mul, norm_inv, Complex.norm_real,
                  Real.norm_of_nonneg (by positivity)]
                field_simp
          _ = ‖y n‖ := by rw [hby n]
      have hTx (k n : ℕ) : apm_m94J02_diagonal (x k) n =
          Complex.ofReal ((n : ℝ) ^ 2 + 1) * apm_m94J02_T (a k) n := by
        rw [apm_m94J02_diagonal_apply, hx k n]
        simp only [apm_m94J02_T]
        ring
      refine ⟨σ, hσ, b, hb, ?_⟩
      have hynorm : Tendsto
          (fun k => ‖apm_m94J02_diagonal (x (σ k)) - y‖)
          atTop (nhds 0) := by
        rw [← tendsto_iff_norm_sub_tendsto_zero]
        simpa [Function.comp_def] using hy
      convert hynorm using 1
      funext k
      rw [apm_m94J02_weighted_lp_sub_norm
        (apm_m94J02_T (a (σ k))) b
        (apm_m94J02_diagonal (x (σ k))) y
        (hTx (σ k)) (fun n => (hby n).symm)]
    exact ⟨apm_m94J02_weighted_complete,
      apm_m94J02_exists_root_limit, hcompact⟩
  have hspectrum : apm_m94J02_spectrum =
      {0} ∪ Set.range (fun n : ℕ ↦ (2 : ℂ) ^ (-(n : ℤ))) :=
    Set.Subset.antisymm apm_m94J02_spectrum_subset_proposed
      apm_m94J02_proposed_spectrum_subset
  exact ⟨hremaining.1, apm_m94J02_eval_continuousOn,
    apm_m94J02_mul_mem_norm_le, hremaining.2.1, hT_mem,
    hremaining.2.2, hspectrum,
    fun _ _ ha hb ↦ apm_m94J02_mem_add ha hb,
    fun c _ ha ↦ apm_m94J02_mem_smul c ha,
    apm_m94J02_norm_nonneg,
    apm_m94J02_norm_eq_zero_iff,
    fun c a ↦ apm_m94J02_norm_smul c a,
    fun _ _ ha hb ↦ apm_m94J02_norm_add_le ha hb,
    apm_m94J02_eval_mul,
    apm_m94J02_eval_T⟩

