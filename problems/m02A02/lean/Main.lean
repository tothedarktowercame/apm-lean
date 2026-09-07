import Mathlib

/-!
# APM m02A02 — the periodic Poisson problem in a Fourier Sobolev model

The periodic Sobolev space is constructed concretely as weighted Fourier
`ℓ²(ℤ², ℂ)`, following the one-dimensional construction in `m95A02`.  An
element stores its Fourier coefficient in the normalized basis whose `ℓ²`
inner product is the `H¹` inner product.  Conjugate symmetry cuts out the
real-valued functions, rapid decay represents smooth periodic functions, and
the zero Fourier mode is the mean.

## Statement repairs

The periodic Poisson equation requires the standard compatibility condition
that the forcing have zero mean; this omitted hypothesis is added explicitly.

## Encoding questions

None.
-/

open Filter Set

noncomputable section

abbrev M02A02Freq := ℤ × ℤ
abbrev M02A02H1 := lp (fun _ : M02A02Freq => ℂ) 2
abbrev M02A02L2 := lp (fun _ : M02A02Freq => ℂ) 2

local instance m02A02_fact_one_le_two : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

def m02A02FreqSq (k : M02A02Freq) : ℝ :=
  (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2

def m02A02Weight (k : M02A02Freq) : ℝ :=
  1 + 4 * Real.pi ^ 2 * m02A02FreqSq k

/-- The physical Fourier coefficient represented by a normalized `H¹`
coefficient vector. -/
def m02A02Coeff (u : M02A02H1) (k : M02A02Freq) : ℂ :=
  u k / (Real.sqrt (m02A02Weight k) : ℂ)

/-- Conjugate symmetry characterizes Fourier coefficients of real functions. -/
def m02A02IsReal (u : M02A02H1) : Prop :=
  ∀ k : M02A02Freq, u (-k.1, -k.2) = star (u k)

/-- Rapid decay of physical coefficients is the Fourier characterization of
a smooth periodic function. -/
def m02A02IsSmoothPeriodic (u : M02A02H1) : Prop :=
  m02A02IsReal u ∧ ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ k : M02A02Freq,
      ‖m02A02Coeff u k‖ * (1 + m02A02FreqSq k) ^ N ≤ C

def m02A02IsMeanZero (u : M02A02H1) : Prop :=
  m02A02IsReal u ∧ u (0, 0) = 0

lemma m02A02_freqSq_nonneg (k : M02A02Freq) : 0 ≤ m02A02FreqSq k := by
  simp only [m02A02FreqSq]
  positivity

lemma m02A02_freqSq_neg (k : M02A02Freq) :
    m02A02FreqSq (-k.1, -k.2) = m02A02FreqSq k := by
  simp [m02A02FreqSq]

lemma m02A02_freqSq_eq_zero_iff (k : M02A02Freq) :
    m02A02FreqSq k = 0 ↔ k = (0, 0) := by
  constructor
  · intro h
    simp only [m02A02FreqSq] at h
    have h1 : (k.1 : ℝ) ^ 2 = 0 := by
      nlinarith [sq_nonneg (k.1 : ℝ), sq_nonneg (k.2 : ℝ)]
    have h2 : (k.2 : ℝ) ^ 2 = 0 := by
      nlinarith [sq_nonneg (k.1 : ℝ), sq_nonneg (k.2 : ℝ)]
    apply Prod.ext
    · exact_mod_cast (sq_eq_zero_iff.mp h1)
    · exact_mod_cast (sq_eq_zero_iff.mp h2)
  · rintro rfl
    norm_num [m02A02FreqSq]

lemma m02A02_one_le_freqSq {k : M02A02Freq} (hk : k ≠ (0, 0)) :
    1 ≤ m02A02FreqSq k := by
  by_cases h1 : k.1 = 0
  · have h2 : k.2 ≠ 0 := by
      intro h2
      exact hk (Prod.ext h1 h2)
    have habs : 1 ≤ |(k.2 : ℝ)| := by exact_mod_cast (Int.one_le_abs h2)
    have hsq : 1 ≤ (k.2 : ℝ) ^ 2 := (one_le_sq_iff_one_le_abs _).2 habs
    simp only [m02A02FreqSq, h1, Int.cast_zero, zero_pow (by norm_num : 2 ≠ 0), zero_add]
    exact hsq
  · have habs : 1 ≤ |(k.1 : ℝ)| := by exact_mod_cast (Int.one_le_abs h1)
    have hsq : 1 ≤ (k.1 : ℝ) ^ 2 := (one_le_sq_iff_one_le_abs _).2 habs
    unfold m02A02FreqSq
    linarith [sq_nonneg (k.2 : ℝ)]

lemma m02A02_weight_pos (k : M02A02Freq) : 0 < m02A02Weight k := by
  unfold m02A02Weight
  have hpi : 0 ≤ Real.pi ^ 2 := sq_nonneg Real.pi
  nlinarith [m02A02_freqSq_nonneg k, mul_nonneg hpi (m02A02_freqSq_nonneg k)]

lemma m02A02_weight_neg (k : M02A02Freq) :
    m02A02Weight (-k.1, -k.2) = m02A02Weight k := by
  simp [m02A02Weight, m02A02_freqSq_neg]

lemma m02A02_sqrt_weight_ne_zero (k : M02A02Freq) :
    Real.sqrt (m02A02Weight k) ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.2 (m02A02_weight_pos k))

lemma m02A02_one_le_sqrt_weight (k : M02A02Freq) :
    1 ≤ Real.sqrt (m02A02Weight k) := by
  have hw : 1 ≤ m02A02Weight k := by
    unfold m02A02Weight
    nlinarith [mul_nonneg (sq_nonneg Real.pi) (m02A02_freqSq_nonneg k)]
  nlinarith [Real.sq_sqrt (le_of_lt (m02A02_weight_pos k)),
    Real.sqrt_nonneg (m02A02Weight k)]

lemma m02A02_coeff_neg_of_isReal {u : M02A02H1} (hu : m02A02IsReal u)
    (k : M02A02Freq) :
    m02A02Coeff u (-k.1, -k.2) = star (m02A02Coeff u k) := by
  rw [m02A02Coeff, m02A02Coeff, hu k, m02A02_weight_neg]
  push_cast
  calc
    star (u k) / (↑(Real.sqrt (m02A02Weight k)) : ℂ) =
        star (u k) / star (↑(Real.sqrt (m02A02Weight k)) : ℂ) := by simp
    _ = star (u k / (↑(Real.sqrt (m02A02Weight k)) : ℂ)) :=
      (map_div₀ (starRingEnd ℂ) _ _).symm

lemma m02A02_smooth_of_finite_support {u : M02A02H1}
    (hu : m02A02IsReal u) (hfin : (Function.support u).Finite) :
    m02A02IsSmoothPeriodic u := by
  refine ⟨hu, fun N => ?_⟩
  let s : Finset M02A02Freq := hfin.toFinset
  let a : M02A02Freq → ℝ := fun k =>
    ‖m02A02Coeff u k‖ * (1 + m02A02FreqSq k) ^ N
  have ha : ∀ k, 0 ≤ a k := by
    intro k
    dsimp [a]
    exact mul_nonneg (norm_nonneg _) (pow_nonneg (by linarith [m02A02_freqSq_nonneg k]) _)
  refine ⟨∑ k ∈ s, a k, Finset.sum_nonneg fun k _ => ha k, ?_⟩
  · intro k
    by_cases hk : k ∈ s
    · change a k ≤ ∑ i ∈ s, a i
      exact Finset.single_le_sum (fun i _ => ha i) hk
    · have hk0 : u k = 0 := by
        rw [← not_ne_iff]
        intro hne
        exact hk (hfin.mem_toFinset.mpr hne)
      simp only [m02A02Coeff, hk0, zero_div, norm_zero, zero_mul]
      exact Finset.sum_nonneg fun i _ => ha i

def m02A02Trunc (u : M02A02H1) (s : Finset M02A02Freq) : M02A02H1 :=
  ∑ k ∈ s, lp.single 2 k (u k)

lemma m02A02_trunc_apply (u : M02A02H1) (s : Finset M02A02Freq)
    (k : M02A02Freq) :
    m02A02Trunc u s k = if k ∈ s then u k else 0 := by
  classical
  rw [m02A02Trunc, lp.coeFn_sum]
  simp

lemma m02A02_trunc_finite_support (u : M02A02H1) (s : Finset M02A02Freq) :
    (Function.support (m02A02Trunc u s)).Finite := by
  apply s.finite_toSet.subset
  intro k hk
  rw [Function.mem_support, m02A02_trunc_apply] at hk
  change k ∈ s
  by_contra hks
  simp [hks] at hk

lemma m02A02_trunc_isReal {u : M02A02H1} (hu : m02A02IsReal u)
    (s : Finset M02A02Freq)
    (hs : ∀ k : M02A02Freq, ((-k.1, -k.2) ∈ s ↔ k ∈ s)) :
    m02A02IsReal (m02A02Trunc u s) := by
  intro k
  rw [m02A02_trunc_apply, m02A02_trunc_apply]
  by_cases hk : k ∈ s
  · rw [if_pos hk, if_pos ((hs k).mpr hk), hu k]
  · rw [if_neg hk, if_neg (mt (hs k).mp hk)]
    simp

lemma m02A02_symmetric_hull_mem (s : Finset M02A02Freq) (k : M02A02Freq) :
    ((-k.1, -k.2) ∈ s ∪ s.image (fun j => (-j.1, -j.2))) ↔
      k ∈ s ∪ s.image (fun j => (-j.1, -j.2)) := by
  simp only [Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (hk | ⟨j, hj, hjeq⟩)
    · right
      exact ⟨(-k.1, -k.2), hk, by simp⟩
    · left
      have hjk : j = k := by
        apply Prod.ext
        · exact neg_inj.mp (congrArg Prod.fst hjeq)
        · exact neg_inj.mp (congrArg Prod.snd hjeq)
      simpa [hjk] using hj
  · rintro (hk | ⟨j, hj, hjeq⟩)
    · right
      exact ⟨k, hk, rfl⟩
    · left
      have := congrArg (fun q : M02A02Freq => (-q.1, -q.2)) hjeq
      have hkj : (-k.1, -k.2) = j := by simpa using this.symm
      simpa [hkj] using hj

abbrev M02A02RealH1 := {u : M02A02H1 // m02A02IsReal u}
local instance m02A02_realH1_metricSpace : MetricSpace M02A02RealH1 :=
  MetricSpace.induced Subtype.val Subtype.coe_injective inferInstance
def m02A02SmoothPeriodicH1 : Set M02A02RealH1 :=
  {u | m02A02IsSmoothPeriodic u.1}

lemma m02A02_dense_smoothPeriodic : Dense m02A02SmoothPeriodicH1 := by
  refine (@Metric.dense_iff M02A02RealH1 inferInstance
    m02A02SmoothPeriodicH1).mpr ?_
  intro x r hr
  have hsum := lp.hasSum_single (p := (2 : ENNReal)) (by norm_num) x.1
  rw [HasSum, SummationFilter.unconditional, Metric.tendsto_atTop] at hsum
  obtain ⟨s, hs⟩ := hsum r hr
  let t : Finset M02A02Freq :=
    s ∪ s.image (fun k : M02A02Freq => (-k.1, -k.2))
  have htReal : m02A02IsReal (m02A02Trunc x.1 t) :=
    m02A02_trunc_isReal x.2 t (m02A02_symmetric_hull_mem s)
  let y : M02A02RealH1 := ⟨m02A02Trunc x.1 t, htReal⟩
  refine ⟨y, ?_, ?_⟩
  · change dist (m02A02Trunc x.1 t) x.1 < r
    simpa [m02A02Trunc] using hs t Finset.subset_union_left
  · exact m02A02_smooth_of_finite_support htReal
      (m02A02_trunc_finite_support x.1 t)

/-- The real, mean-zero Fourier vectors form the concrete real vector space
`H¹_{P,0}`. -/
def m02A02MeanZeroH1 : Submodule ℝ M02A02H1 where
  carrier := {u | m02A02IsMeanZero u}
  zero_mem' := by
    constructor
    · intro k
      have hz : ⇑(0 : M02A02H1) = (0 : M02A02Freq → ℂ) :=
        lp.coeFn_zero _ _
      rw [congrFun hz (-k.1, -k.2), congrFun hz k]
      simp
    · have hz : ⇑(0 : M02A02H1) = (0 : M02A02Freq → ℂ) :=
        lp.coeFn_zero _ _
      rw [congrFun hz (0, 0)]
      simp
  add_mem' := by
    intro u v hu hv
    have hadd : ⇑(u + v) = ⇑u + ⇑v := lp.coeFn_add u v
    constructor
    · intro k
      rw [congrFun hadd (-k.1, -k.2), congrFun hadd k]
      simp only [Pi.add_apply]
      rw [hu.1 k, hv.1 k]
      exact (map_add (starRingEnd ℂ) (u k) (v k)).symm
    · rw [congrFun hadd (0, 0), Pi.add_apply, hu.2, hv.2, add_zero]
  smul_mem' := by
    intro c u hu
    have hsmul : ⇑(c • u) = c • ⇑u := lp.coeFn_smul c u
    constructor
    · intro k
      rw [congrFun hsmul (-k.1, -k.2), congrFun hsmul k]
      simp only [Pi.smul_apply]
      rw [hu.1 k]
      simp
    · rw [congrFun hsmul (0, 0), Pi.smul_apply, hu.2]
      exact smul_zero c

/-! The topological facts needed for the mean-zero space are most naturally
proved coordinatewise.  Keeping them separate also makes the eventual density
argument reusable: convergence in `lp` implies convergence of every Fourier
coefficient. -/

lemma m02A02_continuous_coord (k : M02A02Freq) :
    Continuous (fun u : M02A02H1 => u k) :=
  (continuous_apply k).comp lp.uniformContinuous_coe.continuous

lemma m02A02_isClosed_isReal :
    IsClosed {u : M02A02H1 | m02A02IsReal u} := by
  simp only [m02A02IsReal, setOf_forall]
  apply isClosed_iInter
  intro k
  exact isClosed_eq
    (m02A02_continuous_coord (-k.1, -k.2))
    (continuous_star.comp (m02A02_continuous_coord k))

lemma m02A02_isClosed_meanZero :
    IsClosed (m02A02MeanZeroH1 : Set M02A02H1) := by
  rw [show (m02A02MeanZeroH1 : Set M02A02H1) =
      {u | m02A02IsReal u} ∩ {u | u (0, 0) = 0} by rfl]
  exact m02A02_isClosed_isReal.inter
    (isClosed_eq (m02A02_continuous_coord (0, 0)) continuous_const)

lemma m02A02_completeSpace_meanZero :
    Nonempty (CompleteSpace (↥m02A02MeanZeroH1)) := by
  letI : CompleteSpace (↥m02A02MeanZeroH1) :=
    m02A02_isClosed_meanZero.completeSpace_coe
  exact ⟨inferInstance⟩

/-- The `L²` inner product, recovered from normalized `H¹` coefficients. -/
def m02A02L2Pair (u v : M02A02H1) : ℝ :=
  ∑' k : M02A02Freq,
    (star (m02A02Coeff u k) * m02A02Coeff v k).re

lemma m02A02_re_star_mul_self (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
  change ((starRingEnd ℂ) z * z).re = _
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  norm_cast

lemma m02A02_norm_coeff_le (u : M02A02H1) (k : M02A02Freq) :
    ‖m02A02Coeff u k‖ ≤ ‖u k‖ := by
  rw [m02A02Coeff, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (div_le_iff₀ (Real.sqrt_pos.2 (m02A02_weight_pos k))).2
    (le_mul_of_one_le_right (norm_nonneg _) (m02A02_one_le_sqrt_weight k))

lemma m02A02_summable_coeff_sq (u : M02A02H1) :
    Summable (fun k : M02A02Freq => ‖m02A02Coeff u k‖ ^ 2) := by
  apply Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_)
    (by simpa using (lp.memℓp u).summable (by norm_num : 0 < (2 : ENNReal).toReal))
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (m02A02_norm_coeff_le u k)

lemma m02A02_dirichlet_term_le_coord_sq (u : M02A02H1) (k : M02A02Freq) :
    4 * Real.pi ^ 2 * m02A02FreqSq k * ‖m02A02Coeff u k‖ ^ 2 ≤ ‖u k‖ ^ 2 := by
  let A : ℝ := 4 * Real.pi ^ 2 * m02A02FreqSq k
  let s : ℝ := Real.sqrt (m02A02Weight k)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg Real.pi))
      (m02A02_freqSq_nonneg k)
  have hAw : A ≤ m02A02Weight k := by
    dsimp [A, m02A02Weight]
    linarith
  have hs : 0 < s := Real.sqrt_pos.2 (m02A02_weight_pos k)
  have hs2 : s ^ 2 = m02A02Weight k := Real.sq_sqrt (le_of_lt (m02A02_weight_pos k))
  rw [m02A02Coeff, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  change A * (‖u k‖ / s) ^ 2 ≤ ‖u k‖ ^ 2
  calc
    A * (‖u k‖ / s) ^ 2 ≤ m02A02Weight k * (‖u k‖ / s) ^ 2 :=
      mul_le_mul_of_nonneg_right hAw (sq_nonneg _)
    _ = ‖u k‖ ^ 2 := by
      rw [← hs2]
      field_simp

lemma m02A02_summable_dirichlet_terms (u : M02A02H1) :
    Summable (fun k : M02A02Freq =>
      4 * Real.pi ^ 2 * m02A02FreqSq k * ‖m02A02Coeff u k‖ ^ 2) := by
  apply Summable.of_nonneg_of_le (fun k => mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg Real.pi))
        (m02A02_freqSq_nonneg k)) (sq_nonneg _))
    (m02A02_dirichlet_term_le_coord_sq u)
  simpa using (lp.memℓp u).summable (by norm_num : 0 < (2 : ENNReal).toReal)

lemma m02A02_coeff_sq_le_dirichlet_term {u : M02A02H1}
    (hu : m02A02IsMeanZero u) (k : M02A02Freq) :
    ‖m02A02Coeff u k‖ ^ 2 ≤
      4 * Real.pi ^ 2 * m02A02FreqSq k * ‖m02A02Coeff u k‖ ^ 2 := by
  by_cases hk : k = (0, 0)
  · subst k
    simp [m02A02Coeff, hu.2]
  · have hpi : 1 ≤ 4 * Real.pi ^ 2 := by
      nlinarith [Real.pi_gt_three, sq_nonneg (Real.pi - 3)]
    have hmul : 1 ≤ 4 * Real.pi ^ 2 * m02A02FreqSq k := by
      calc
        1 ≤ 4 * Real.pi ^ 2 := hpi
        _ ≤ 4 * Real.pi ^ 2 * m02A02FreqSq k :=
          le_mul_of_one_le_right (by positivity) (m02A02_one_le_freqSq hk)
    exact le_mul_of_one_le_left (sq_nonneg _) hmul

lemma m02A02_two_le_laplacianMultiplier {k : M02A02Freq} (hk : k ≠ (0, 0)) :
    2 ≤ 4 * Real.pi ^ 2 * m02A02FreqSq k := by
  have hpi : 2 ≤ 4 * Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_three, sq_nonneg (Real.pi - 3)]
  exact hpi.trans (le_mul_of_one_le_right (by positivity) (m02A02_one_le_freqSq hk))

lemma m02A02_sqrt_weight_le_laplacianMultiplier {k : M02A02Freq}
    (hk : k ≠ (0, 0)) :
    Real.sqrt (m02A02Weight k) ≤ 4 * Real.pi ^ 2 * m02A02FreqSq k := by
  let A : ℝ := 4 * Real.pi ^ 2 * m02A02FreqSq k
  have hA : 2 ≤ A := m02A02_two_le_laplacianMultiplier hk
  have hs0 : 0 ≤ Real.sqrt (m02A02Weight k) := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt (m02A02Weight k)) ^ 2 = 1 + A := by
    rw [Real.sq_sqrt (le_of_lt (m02A02_weight_pos k))]
    rfl
  have hAA : 1 + A ≤ A ^ 2 := by nlinarith
  nlinarith [sq_nonneg (Real.sqrt (m02A02Weight k) - A)]

def m02A02PoissonRaw (f : M02A02L2) (k : M02A02Freq) : ℂ :=
  if k = (0, 0) then 0 else
    (Real.sqrt (m02A02Weight k) : ℂ) * f k /
      (4 * Real.pi ^ 2 * m02A02FreqSq k : ℂ)

lemma m02A02_norm_poissonRaw_le (f : M02A02L2) (k : M02A02Freq) :
    ‖m02A02PoissonRaw f k‖ ≤ ‖f k‖ := by
  by_cases hk : k = (0, 0)
  · simp [m02A02PoissonRaw, hk]
  · rw [m02A02PoissonRaw, if_neg hk, norm_div, norm_mul, norm_mul, norm_mul,
      norm_pow, Complex.norm_real, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (by positivity),
      abs_of_nonneg (m02A02_freqSq_nonneg k)]
    norm_num
    calc
      Real.sqrt (m02A02Weight k) * ‖f k‖ /
          (4 * Real.pi ^ 2 * m02A02FreqSq k) =
          (Real.sqrt (m02A02Weight k) /
            (4 * Real.pi ^ 2 * m02A02FreqSq k)) * ‖f k‖ := by ring
      _ ≤ ‖f k‖ := mul_le_of_le_one_left (norm_nonneg (f k)) <|
        (div_le_one ((by norm_num : (0 : ℝ) < 2).trans_le
          (m02A02_two_le_laplacianMultiplier hk))).2
          (m02A02_sqrt_weight_le_laplacianMultiplier hk)

lemma m02A02_poissonRaw_mem (f : M02A02L2) :
    Memℓp (m02A02PoissonRaw f) 2 := by
  apply memℓp_gen
  apply Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (by simpa using (lp.memℓp f).summable (by norm_num : 0 < (2 : ENNReal).toReal))
  convert (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
    (m02A02_norm_poissonRaw_le f k) using 1
  all_goals norm_num

def m02A02PoissonPart (f : M02A02L2) : M02A02H1 :=
  ⟨m02A02PoissonRaw f, m02A02_poissonRaw_mem f⟩

@[simp] lemma m02A02_poissonPart_apply (f : M02A02L2) (k : M02A02Freq) :
    m02A02PoissonPart f k = m02A02PoissonRaw f k := rfl

lemma m02A02_poissonPart_isReal (f : M02A02L2)
    (hf : ∀ k : M02A02Freq, f (-k.1, -k.2) = star (f k)) :
    m02A02IsReal (m02A02PoissonPart f) := by
  intro k
  simp only [m02A02_poissonPart_apply, m02A02PoissonRaw]
  by_cases hk : k = (0, 0)
  · subst k
    simp
  · have hnk : (-k.1, -k.2) ≠ (0, 0) := by
      intro h
      apply hk
      have := congrArg (fun q : M02A02Freq => (-q.1, -q.2)) h
      simpa using this
    rw [if_neg hk, if_neg hnk, m02A02_weight_neg, m02A02_freqSq_neg, hf k]
    push_cast
    change _ = (starRingEnd ℂ)
      (((Real.sqrt (m02A02Weight k) : ℂ) * f k) /
        (4 * Real.pi ^ 2 * m02A02FreqSq k : ℂ))
    rw [map_div₀, map_mul]
    congr 2
    · exact (Complex.conj_ofReal _).symm
    · calc
        4 * (Real.pi : ℂ) ^ 2 * (m02A02FreqSq k : ℂ) =
            ((4 * Real.pi ^ 2 * m02A02FreqSq k : ℝ) : ℂ) := by push_cast; rfl
        _ = (starRingEnd ℂ) ((4 * Real.pi ^ 2 * m02A02FreqSq k : ℝ) : ℂ) :=
          (Complex.conj_ofReal _).symm
        _ = (starRingEnd ℂ)
            (4 * (Real.pi : ℂ) ^ 2 * (m02A02FreqSq k : ℂ)) := by push_cast; rfl

lemma m02A02_isReal_add {u v : M02A02H1}
    (hu : m02A02IsReal u) (hv : m02A02IsReal v) : m02A02IsReal (u + v) := by
  intro k
  rw [congrFun (lp.coeFn_add u v) (-k.1, -k.2),
    congrFun (lp.coeFn_add u v) k]
  simp only [Pi.add_apply, hu k, hv k]
  change _ = (starRingEnd ℂ) (u k + v k)
  rw [map_add]
  rfl

lemma m02A02_isReal_neg {u : M02A02H1} (hu : m02A02IsReal u) :
    m02A02IsReal (-u) := by
  intro k
  rw [congrFun (lp.coeFn_neg u) (-k.1, -k.2), congrFun (lp.coeFn_neg u) k]
  simp only [Pi.neg_apply, hu k]
  change _ = (starRingEnd ℂ) (-u k)
  rw [map_neg]
  rfl

lemma m02A02_isReal_sub {u v : M02A02H1}
    (hu : m02A02IsReal u) (hv : m02A02IsReal v) : m02A02IsReal (u - v) := by
  rw [sub_eq_add_neg]
  exact m02A02_isReal_add hu (m02A02_isReal_neg hv)

def m02A02AffineSolution (u₀ : M02A02H1) (f : M02A02L2) : M02A02H1 :=
  lp.single 2 (0, 0) (u₀ (0, 0)) + m02A02PoissonPart f

lemma m02A02_affineSolution_apply (u₀ : M02A02H1) (f : M02A02L2)
    (k : M02A02Freq) :
    m02A02AffineSolution u₀ f k =
      if k = (0, 0) then u₀ (0, 0) else m02A02PoissonPart f k := by
  rw [m02A02AffineSolution, congrFun (lp.coeFn_add _ _) k]
  simp only [Pi.add_apply, lp.single_apply]
  split_ifs with hk
  · subst k
    simp [m02A02PoissonRaw]
  · simp [hk]

lemma m02A02_zeroSingle_isReal {u₀ : M02A02H1} (hu₀ : m02A02IsReal u₀) :
    m02A02IsReal (lp.single 2 (0, 0) (u₀ (0, 0)) : M02A02H1) := by
  intro k
  by_cases hk : k = (0, 0)
  · subst k
    simpa using hu₀ (0, 0)
  · have hnk : (-k.1, -k.2) ≠ (0, 0) := by
      intro h
      apply hk
      have := congrArg (fun q : M02A02Freq => (-q.1, -q.2)) h
      simpa using this
    simp [lp.single_apply, hk, hnk]

lemma m02A02_affineSolution_isReal (u₀ : M02A02H1) (f : M02A02L2)
    (hu₀ : m02A02IsReal u₀)
    (hf : ∀ k : M02A02Freq, f (-k.1, -k.2) = star (f k)) :
    m02A02IsReal (m02A02AffineSolution u₀ f) :=
  m02A02_isReal_add (m02A02_zeroSingle_isReal hu₀)
    (m02A02_poissonPart_isReal f hf)

lemma m02A02_affineSolution_meanZero (u₀ : M02A02H1) (f : M02A02L2)
    (hu₀ : m02A02IsReal u₀)
    (hf : ∀ k : M02A02Freq, f (-k.1, -k.2) = star (f k)) :
    m02A02IsMeanZero (m02A02AffineSolution u₀ f - u₀) := by
  constructor
  · exact m02A02_isReal_sub (m02A02_affineSolution_isReal u₀ f hu₀ hf) hu₀
  · rw [congrFun (lp.coeFn_sub _ _) (0, 0), Pi.sub_apply,
      m02A02_affineSolution_apply]
    simp

/-- Dirichlet form `∫ ∇u · ∇v`, expressed by Fourier multipliers. -/
def m02A02DirichletPair (u v : M02A02H1) : ℝ :=
  ∑' k : M02A02Freq,
    4 * Real.pi ^ 2 * m02A02FreqSq k *
      (star (m02A02Coeff u k) * m02A02Coeff v k).re

def m02A02GradientEnergy (u : M02A02H1) : ℝ :=
  m02A02DirichletPair u u

def m02A02L2Energy (u : M02A02H1) : ℝ :=
  m02A02L2Pair u u

lemma m02A02_poincare (u : M02A02H1) (hu : m02A02IsMeanZero u) :
    m02A02L2Energy u ≤ m02A02GradientEnergy u := by
  unfold m02A02L2Energy m02A02GradientEnergy m02A02L2Pair m02A02DirichletPair
  simp_rw [m02A02_re_star_mul_self]
  exact (m02A02_summable_coeff_sq u).tsum_le_tsum
    (m02A02_coeff_sq_le_dirichlet_term hu)
    (m02A02_summable_dirichlet_terms u)

/-- Pairing an `L²` forcing, represented by its ordinary Fourier
coefficients, with a periodic Sobolev test function. -/
def m02A02ForcingPair (f : M02A02L2) (v : M02A02H1) : ℝ :=
  ∑' k : M02A02Freq,
    (star (f k) * m02A02Coeff v k).re

def m02A02WeakSolution (u : M02A02H1) (f : M02A02L2) : Prop :=
  ∀ v : M02A02H1, m02A02IsMeanZero v →
    m02A02DirichletPair u v = m02A02ForcingPair f v

/-- Fourier-coefficient form of `-Δu = f`. -/
def m02A02HasPoissonEquation (u : M02A02H1) (f : M02A02L2) : Prop :=
  ∀ k : M02A02Freq,
    (4 * Real.pi ^ 2 * m02A02FreqSq k : ℂ) * m02A02Coeff u k = f k

lemma m02A02_poissonPart_hasEquation (f : M02A02L2) (hf0 : f (0, 0) = 0) :
    m02A02HasPoissonEquation (m02A02PoissonPart f) f := by
  intro k
  by_cases hk : k = (0, 0)
  · subst k
    simp [m02A02FreqSq, m02A02Coeff, m02A02PoissonRaw, hf0]
  · rw [m02A02Coeff, m02A02_poissonPart_apply, m02A02PoissonRaw, if_neg hk]
    have hA : (4 * Real.pi ^ 2 * m02A02FreqSq k : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt ((by norm_num : (0 : ℝ) < 2).trans_le
        (m02A02_two_le_laplacianMultiplier hk))
    have hs : (Real.sqrt (m02A02Weight k) : ℂ) ≠ 0 := by
      exact_mod_cast m02A02_sqrt_weight_ne_zero k
    have hfreq : (m02A02FreqSq k : ℂ) ≠ 0 := by
      exact_mod_cast (mt (m02A02_freqSq_eq_zero_iff k).mp hk)
    field_simp

lemma m02A02_affineSolution_hasEquation (u₀ : M02A02H1) (f : M02A02L2)
    (hf0 : f (0, 0) = 0) :
    m02A02HasPoissonEquation (m02A02AffineSolution u₀ f) f := by
  intro k
  by_cases hk : k = (0, 0)
  · subst k
    simp [m02A02FreqSq, hf0]
  · rw [m02A02Coeff, m02A02_affineSolution_apply, if_neg hk]
    exact m02A02_poissonPart_hasEquation f hf0 k

lemma m02A02_hasEquation_zero (u : M02A02H1) (f : M02A02L2)
    (h : m02A02HasPoissonEquation u f) : f (0, 0) = 0 := by
  simpa [m02A02FreqSq] using (h (0, 0)).symm

lemma m02A02_hasEquation_unique_of_zeroMode (u v : M02A02H1) (f : M02A02L2)
    (hu : m02A02HasPoissonEquation u f)
    (hv : m02A02HasPoissonEquation v f)
    (hzero : u (0, 0) = v (0, 0)) : u = v := by
  apply lp.ext
  funext k
  by_cases hk : k = (0, 0)
  · simpa [hk] using hzero
  · have hA : (4 * Real.pi ^ 2 * m02A02FreqSq k : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt ((by norm_num : (0 : ℝ) < 2).trans_le
        (m02A02_two_le_laplacianMultiplier hk))
    have hc : m02A02Coeff u k = m02A02Coeff v k := by
      apply (mul_left_cancel₀ hA)
      exact (hu k).trans (hv k).symm
    rw [m02A02Coeff, m02A02Coeff] at hc
    exact (div_left_inj' (by exact_mod_cast m02A02_sqrt_weight_ne_zero k)).mp hc

lemma m02A02_poisson_summand_eq (u v : M02A02H1) (f : M02A02L2)
    (h : m02A02HasPoissonEquation u f) (k : M02A02Freq) :
    4 * Real.pi ^ 2 * m02A02FreqSq k *
        (star (m02A02Coeff u k) * m02A02Coeff v k).re =
      (star (f k) * m02A02Coeff v k).re := by
  let A : ℝ := 4 * Real.pi ^ 2 * m02A02FreqSq k
  let z : ℂ := m02A02Coeff u k
  let w : ℂ := m02A02Coeff v k
  have hkEq : (A : ℂ) * z = f k := by
    dsimp [A, z]
    push_cast
    exact h k
  rw [← hkEq]
  have hc : (A : ℂ) * ((starRingEnd ℂ) z * w) =
      (starRingEnd ℂ) ((A : ℂ) * z) * w := by
    rw [map_mul, show (starRingEnd ℂ) (A : ℂ) = A by
      exact Complex.conj_ofReal A]
    ring
  have hre := congrArg Complex.re hc
  dsimp [A, z, w] at hre ⊢
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero] using hre

lemma m02A02_hasEquation_to_weak (u : M02A02H1) (f : M02A02L2)
    (h : m02A02HasPoissonEquation u f) : m02A02WeakSolution u f := by
  intro v hv
  unfold m02A02DirichletPair m02A02ForcingPair
  apply tsum_congr
  intro k
  exact m02A02_poisson_summand_eq u v f h k

def m02A02Probe (k : M02A02Freq) (q : ℂ) : M02A02H1 :=
  lp.single 2 k ((Real.sqrt (m02A02Weight k) : ℂ) * q) +
    lp.single 2 (-k.1, -k.2) ((Real.sqrt (m02A02Weight k) : ℂ) * star q)

lemma m02A02_ne_neg_of_ne_zero {k : M02A02Freq} (hk : k ≠ (0, 0)) :
    k ≠ (-k.1, -k.2) := by
  intro h
  apply hk
  apply Prod.ext
  · have he := congrArg Prod.fst h
    dsimp at he
    omega
  · have he := congrArg Prod.snd h
    dsimp at he
    omega

lemma m02A02_probe_apply {k : M02A02Freq} (hk : k ≠ (0, 0)) (q : ℂ)
    (j : M02A02Freq) :
    m02A02Probe k q j = if j = k then (Real.sqrt (m02A02Weight k) : ℂ) * q
      else if j = (-k.1, -k.2) then
        (Real.sqrt (m02A02Weight k) : ℂ) * star q else 0 := by
  rw [m02A02Probe, congrFun (lp.coeFn_add _ _) j]
  simp only [Pi.add_apply, lp.single_apply]
  have hkn := m02A02_ne_neg_of_ne_zero hk
  by_cases h1 : j = k
  · subst j
    simp [hkn]
  · by_cases h2 : j = (-k.1, -k.2)
    · subst j
      simp [h1]
    · simp [h1, h2]

lemma m02A02_probe_coeff {k : M02A02Freq} (hk : k ≠ (0, 0)) (q : ℂ) :
    m02A02Coeff (m02A02Probe k q) k = q ∧
    m02A02Coeff (m02A02Probe k q) (-k.1, -k.2) = star q := by
  have hkn : (-k.1, -k.2) ≠ k := (m02A02_ne_neg_of_ne_zero hk).symm
  constructor
  · rw [m02A02Coeff, m02A02_probe_apply hk, if_pos rfl]
    field_simp [m02A02_sqrt_weight_ne_zero k]
  · rw [m02A02Coeff, m02A02_probe_apply hk, if_neg hkn, if_pos rfl,
      m02A02_weight_neg]
    field_simp [m02A02_sqrt_weight_ne_zero k]

lemma m02A02_probe_meanZero {k : M02A02Freq} (hk : k ≠ (0, 0)) (q : ℂ) :
    m02A02IsMeanZero (m02A02Probe k q) := by
  constructor
  · intro j
    rw [m02A02_probe_apply hk, m02A02_probe_apply hk]
    have hnk : (-k.1, -k.2) ≠ k := (m02A02_ne_neg_of_ne_zero hk).symm
    by_cases h1 : j = k
    · subst j
      simp [hnk]
    · by_cases h2 : j = (-k.1, -k.2)
      · subst j
        simp [h1]
      · have hn1 : (-j.1, -j.2) ≠ k := by
          intro h
          apply h2
          have := congrArg (fun x : M02A02Freq => (-x.1, -x.2)) h
          simpa using this
        have hn2 : (-j.1, -j.2) ≠ (-k.1, -k.2) := by
          intro h
          apply h1
          have := congrArg (fun x : M02A02Freq => (-x.1, -x.2)) h
          simpa using this
        simp [h1, h2, hn1, hn2]
  · rw [m02A02_probe_apply hk]
    have hk0 : (0, 0) ≠ k := Ne.symm hk
    have h0n : (0, 0) ≠ (-k.1, -k.2) := by
      intro h
      apply hk
      have := congrArg (fun x : M02A02Freq => (-x.1, -x.2)) h
      simpa using this.symm
    simp [hk0, h0n]

lemma m02A02_weak_probe_eq (u : M02A02H1) (f : M02A02L2)
    (hw : m02A02WeakSolution u f) {k : M02A02Freq} (hk : k ≠ (0, 0)) (q : ℂ) :
    4 * Real.pi ^ 2 * m02A02FreqSq k *
          (star (m02A02Coeff u k) * q).re +
        4 * Real.pi ^ 2 * m02A02FreqSq (-k.1, -k.2) *
          (star (m02A02Coeff u (-k.1, -k.2)) * star q).re =
      (star (f k) * q).re + (star (f (-k.1, -k.2)) * star q).re := by
  have h := hw (m02A02Probe k q) (m02A02_probe_meanZero hk q)
  unfold m02A02DirichletPair m02A02ForcingPair at h
  have hout : ∀ j ∉ ({k, (-k.1, -k.2)} : Finset M02A02Freq),
      m02A02Coeff (m02A02Probe k q) j = 0 := by
    intro j hj
    have hjk : j ≠ k := by simpa using fun h => hj (by simp [h])
    have hjn : j ≠ (-k.1, -k.2) := by simpa using fun h => hj (by simp [h])
    rw [m02A02Coeff, m02A02_probe_apply hk]
    simp [hjk, hjn]
  rw [tsum_eq_sum (s := {k, (-k.1, -k.2)}) (fun j hj => by simp [hout j hj]),
    tsum_eq_sum (s := {k, (-k.1, -k.2)}) (fun j hj => by simp [hout j hj])] at h
  have hkn : k ≠ (-k.1, -k.2) := m02A02_ne_neg_of_ne_zero hk
  simpa [m02A02_probe_coeff hk q, hkn] using h

lemma m02A02_weak_to_hasEquation (u : M02A02H1) (f : M02A02L2)
    (hu : m02A02IsReal u)
    (hf : ∀ k : M02A02Freq, f (-k.1, -k.2) = star (f k))
    (hf0 : f (0, 0) = 0)
    (hw : m02A02WeakSolution u f) : m02A02HasPoissonEquation u f := by
  intro k
  by_cases hk : k = (0, 0)
  · subst k
    simp [m02A02FreqSq, hf0]
  · have hre := m02A02_weak_probe_eq u f hw hk (1 : ℂ)
    have him := m02A02_weak_probe_eq u f hw hk Complex.I
    rw [m02A02_freqSq_neg, m02A02_coeff_neg_of_isReal hu,
      hf k] at hre him
    simp only [star_star] at hre him
    have hre' : 4 * Real.pi ^ 2 * m02A02FreqSq k * (m02A02Coeff u k).re =
        (f k).re := by
      simp at hre
      linarith
    have him' : 4 * Real.pi ^ 2 * m02A02FreqSq k * (m02A02Coeff u k).im =
        (f k).im := by
      simp [Complex.mul_re] at him
      linarith
    let A : ℝ := 4 * Real.pi ^ 2 * m02A02FreqSq k
    have hc : (A : ℂ) * m02A02Coeff u k = f k := by
      apply Complex.ext
      · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero]
        change A * (m02A02Coeff u k).re = (f k).re
        exact hre'
      · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, add_zero]
        change A * (m02A02Coeff u k).im = (f k).im
        exact him'
    dsimp [A] at hc
    push_cast at hc
    exact hc

theorem apm_m02a02 :
    Dense m02A02SmoothPeriodicH1 ∧
    IsClosed (m02A02MeanZeroH1 : Set M02A02H1) ∧
    Nonempty (CompleteSpace (↥m02A02MeanZeroH1)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ u : M02A02H1,
      m02A02IsMeanZero u →
      m02A02L2Energy u ≤ C * m02A02GradientEnergy u) ∧
    ∀ (u₀ : M02A02H1) (f : M02A02L2),
      m02A02IsReal u₀ →
      (∀ k : M02A02Freq, f (-k.1, -k.2) = star (f k)) →
      f (0, 0) = 0 →
      (∃! u : M02A02H1,
        m02A02IsReal u ∧ m02A02IsMeanZero (u - u₀) ∧
          m02A02WeakSolution u f) ∧
      (∀ u : M02A02H1,
        m02A02IsReal u → m02A02IsMeanZero (u - u₀) →
        (m02A02WeakSolution u f ↔ m02A02HasPoissonEquation u f)) := by
  refine ⟨m02A02_dense_smoothPeriodic, m02A02_isClosed_meanZero,
    m02A02_completeSpace_meanZero, ?_⟩
  refine ⟨⟨1, zero_lt_one, fun u hu => ?_⟩, ?_⟩
  · simpa using m02A02_poincare u hu
  intro u₀ f hu₀ hf hf0
  let sol : M02A02H1 := m02A02AffineSolution u₀ f
  have hsolReal : m02A02IsReal sol := m02A02_affineSolution_isReal u₀ f hu₀ hf
  have hsolMean : m02A02IsMeanZero (sol - u₀) :=
    m02A02_affineSolution_meanZero u₀ f hu₀ hf
  have hsolEq : m02A02HasPoissonEquation sol f :=
    m02A02_affineSolution_hasEquation u₀ f hf0
  have hsolWeak : m02A02WeakSolution sol f := m02A02_hasEquation_to_weak sol f hsolEq
  constructor
  · refine ⟨sol, ⟨hsolReal, hsolMean, hsolWeak⟩, ?_⟩
    intro w hw
    have hwEq : m02A02HasPoissonEquation w f :=
      m02A02_weak_to_hasEquation w f hw.1 hf hf0 hw.2.2
    have hw0 : w (0, 0) = u₀ (0, 0) := by
      have hz := hw.2.1.2
      rw [congrFun (lp.coeFn_sub w u₀) (0, 0), Pi.sub_apply] at hz
      exact sub_eq_zero.mp hz
    have hsol0 : sol (0, 0) = u₀ (0, 0) := by
      dsimp [sol]
      rw [m02A02_affineSolution_apply]
      simp
    exact m02A02_hasEquation_unique_of_zeroMode w sol f hwEq hsolEq (hw0.trans hsol0.symm)
  · intro u hu hmean
    constructor
    · exact m02A02_weak_to_hasEquation u f hu hf hf0
    · exact m02A02_hasEquation_to_weak u f
