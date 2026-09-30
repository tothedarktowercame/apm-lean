import Mathlib

/-! # APM m95A02: the periodic Sobolev space `H¹`

## Statement repairs

None.

## Encoding note

Mathlib does not bundle periodic `W^{1,2}`.  We use its exact weighted-Fourier
realization: an element of `m95A02H = ℓ²(ℤ, ℂ)` stores the coefficient in the
normalized basis `exp (inx) / √(2π(n²+1))`.  Consequently its `ℓ²` inner product
is precisely the Sobolev inner product printed in the question.
-/

open Filter Set

noncomputable section

abbrev m95A02H := lp (fun _ : ℤ => ℂ) 2

def m95A02BasisFunction (n : ℤ) (x : ℝ) : ℂ :=
  Complex.exp ((n : ℂ) * Complex.I * (x : ℂ)) /
    (Real.sqrt (2 * Real.pi * ((n : ℝ) ^ 2 + 1)) : ℂ)

def m95A02Value (f : m95A02H) (x : ℝ) : ℂ :=
  ∑' n : ℤ, f n * m95A02BasisFunction n x

def m95A02MaxDist (f g : m95A02H) : ℝ :=
  sSup {r : ℝ | ∃ x ∈ Icc (0 : ℝ) (2 * Real.pi),
    r = dist (m95A02Value f x) (m95A02Value g x)}

/-- The Fourier-series realization sends the zero coefficient vector to the
zero function. -/
lemma m95A02Value_zero (x : ℝ) : m95A02Value (0 : m95A02H) x = 0 := by
  unfold m95A02Value
  have hz : ⇑(0 : m95A02H) = (0 : ℤ → ℂ) := by
    exact lp.coeFn_zero _ _
  rw [show (fun n : ℤ => (0 : m95A02H) n * m95A02BasisFunction n x) =
      (fun _ : ℤ => 0) by funext n; rw [show (0 : m95A02H) n = 0 from congrFun hz n]; simp]
  exact tsum_zero

/-- Evaluation of a coordinate vector is the corresponding normalized Fourier
mode.  This is the finite-coordinate core needed by the weak-convergence
route. -/
lemma m95A02Value_single (n : ℤ) (x : ℝ) :
    m95A02Value (lp.single 2 n 1 : m95A02H) x = m95A02BasisFunction n x := by
  unfold m95A02Value
  rw [tsum_eq_single n]
  · simp
  · intro j hj
    simp [hj]

/-- The custom maximum-distance encoding vanishes on the diagonal. -/
lemma m95A02MaxDist_self (f : m95A02H) : m95A02MaxDist f f = 0 := by
  have hset :
      {r : ℝ | ∃ x ∈ Icc (0 : ℝ) (2 * Real.pi),
        r = dist (m95A02Value f x) (m95A02Value f x)} = {0} := by
    ext r
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp
    · intro hr
      have hr0 : r = 0 := Set.mem_singleton_iff.mp hr
      subst r
      exact ⟨0, ⟨le_rfl, by positivity⟩, by simp⟩
  rw [m95A02MaxDist, hset]
  simp

/-- A uniform pointwise evaluation bound passes directly through the custom
set-valued supremum encoding. -/
lemma m95A02MaxDist_le_of_forall
    (f g : m95A02H) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x ∈ Icc (0 : ℝ) (2 * Real.pi),
      dist (m95A02Value f x) (m95A02Value g x) ≤ C) :
    m95A02MaxDist f g ≤ C := by
  unfold m95A02MaxDist
  apply Real.sSup_le _ hC
  intro r hr
  obtain ⟨x, hx, rfl⟩ := hr
  exact h x hx

/-- Weak convergence in the Fourier realization implies convergence of every
individual coefficient. -/
lemma m95A02_tendsto_coord_of_weak
    (f : ℕ → m95A02H) (g : m95A02H)
    (h : Tendsto (fun n ↦ toWeakSpace ℂ m95A02H (f n)) atTop
      (nhds (toWeakSpace ℂ m95A02H g))) (j : ℤ) :
    Tendsto (fun n ↦ f n j) atTop (nhds (g j)) := by
  have hall := (WeakBilin.tendsto_iff_forall_eval_tendsto
    (B := (topDualPairing ℂ m95A02H).flip)
    (separatingDual_iff_injective.mp inferInstance)).1 h
  have hj := hall ((InnerProductSpace.toDual ℂ m95A02H)
    (lp.single 2 j 1 : m95A02H))
  convert hj using 1
  · funext n
    change f n j = (InnerProductSpace.toDual ℂ m95A02H)
      (lp.single 2 j 1 : m95A02H) (f n)
    rw [InnerProductSpace.toDual_apply_apply, lp.inner_single_left]
    simp
  · congr 1
    change g j = (InnerProductSpace.toDual ℂ m95A02H)
      (lp.single 2 j 1 : m95A02H) g
    rw [InnerProductSpace.toDual_apply_apply, lp.inner_single_left]
    simp

/-- A weakly convergent sequence in the Fourier Hilbert realization is
uniformly bounded in its Hilbert norm. -/
lemma m95A02_bounded_of_weak_convergence
    (f : ℕ → m95A02H) (g : m95A02H)
    (h : Tendsto (fun n ↦ toWeakSpace ℂ m95A02H (f n)) atTop
      (nhds (toWeakSpace ℂ m95A02H g))) :
    ∃ C : ℝ, ∀ n : ℕ, ‖f n‖ ≤ C := by
  have hall := (WeakBilin.tendsto_iff_forall_eval_tendsto
    (B := (topDualPairing ℂ m95A02H).flip)
    (separatingDual_iff_injective.mp inferInstance)).1 h
  let F : ℕ → m95A02H →L[ℂ] ℂ := fun n ↦
    (InnerProductSpace.toDual ℂ m95A02H) (f n)
  have hpoint : ∀ x : m95A02H, ∃ C : ℝ, ∀ n : ℕ, ‖F n x‖ ≤ C := by
    intro x
    have hx := hall ((InnerProductSpace.toDual ℂ m95A02H) x)
    obtain ⟨C, hC⟩ := hx.norm.bddAbove_range
    refine ⟨C, fun n ↦ ?_⟩
    have hn := hC ⟨n, rfl⟩
    change ‖inner ℂ x (f n)‖ ≤ C at hn
    change ‖inner ℂ (f n) x‖ ≤ C
    rw [norm_inner_symm]
    exact hn
  obtain ⟨C, hC⟩ := banach_steinhaus (g := F) hpoint
  refine ⟨C, fun n ↦ ?_⟩
  simpa [F] using hC n

/-- Exact size of a normalized Fourier mode. -/
lemma m95A02_norm_basisFunction (n : ℤ) (x : ℝ) :
    ‖m95A02BasisFunction n x‖ =
      (Real.sqrt (2 * Real.pi * ((n : ℝ) ^ 2 + 1)))⁻¹ := by
  unfold m95A02BasisFunction
  rw [norm_div, Complex.norm_exp]
  have hs : 0 < Real.sqrt (2 * Real.pi * ((n : ℝ) ^ 2 + 1)) := by
    positivity
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  rw [show (((n : ℂ) * Complex.I * (x : ℂ)).re) = 0 by simp]
  simp

/-- The squared point-evaluation kernel is summable over the bilateral
integer frequencies. -/
lemma m95A02_summable_sq_norm_basisFunction (x : ℝ) :
    Summable (fun n : ℤ ↦ ‖m95A02BasisFunction n x‖ ^ 2) := by
  have hp : Summable (fun n : ℤ ↦ |(n : ℝ)| ^ (-(2 : ℝ))) :=
    Real.summable_abs_int_rpow (by norm_num)
  let q : ℤ → ℝ := fun n ↦
    |(n : ℝ)| ^ (-(2 : ℝ)) + if n = 0 then 1 else 0
  have hsingle : Summable (fun n : ℤ ↦ if n = 0 then (1 : ℝ) else 0) := by
    apply summable_of_hasFiniteSupport
    exact (Set.finite_singleton 0).subset (by
      intro n hn
      by_contra hne
      apply hn
      have : n ≠ 0 := by simpa using hne
      simp [this])
  have hq : Summable q := hp.add hsingle
  refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun n ↦ ?_) hq
  rw [m95A02_norm_basisFunction]
  by_cases hn : n = 0
  · subst n
    simp [q]
    have hp3 := Real.pi_gt_three
    have hpi : 1 ≤ Real.sqrt Real.pi := by
      exact Real.one_le_sqrt.mpr (by linarith)
    have htwo : 1 ≤ Real.sqrt 2 := by norm_num
    have hi1 : (Real.sqrt Real.pi)⁻¹ ≤ 1 :=
      (inv_le_one₀ (by positivity)).mpr hpi
    have hi2 : (Real.sqrt 2)⁻¹ ≤ 1 :=
      (inv_le_one₀ (by positivity)).mpr htwo
    have hp0 : 0 ≤ (Real.sqrt Real.pi)⁻¹ := by positivity
    have ht0 : 0 ≤ (Real.sqrt 2)⁻¹ := by positivity
    have hprod := mul_le_mul hi1 hi2 ht0 (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith [mul_nonneg hp0 ht0]
  · have hnabs : (1 : ℝ) ≤ |(n : ℝ)| := by
      exact_mod_cast Int.one_le_abs hn
    have hpi : 0 < Real.pi := Real.pi_pos
    simp only [q, if_neg hn]
    rw [inv_pow]
    have hden : 0 < Real.sqrt (2 * Real.pi * ((n : ℝ) ^ 2 + 1)) := by
      positivity
    rw [Real.rpow_neg (abs_nonneg (n : ℝ)), Real.rpow_two]
    rw [← one_div, ← one_div]
    simp only [add_zero]
    apply one_div_le_one_div_of_le
    · positivity
    · rw [Real.sq_sqrt (by positivity)]
      have hn_sq : |(n : ℝ)| ^ 2 = (n : ℝ) ^ 2 := sq_abs _
      rw [hn_sq]
      nlinarith [show 3 < 2 * Real.pi by linarith [Real.pi_gt_three]]

/-- The squared norm of a Fourier mode is independent of the evaluation
point; this is the uniform scalar kernel used in the tail argument. -/
lemma m95A02_sq_norm_basisFunction (n : ℤ) (x : ℝ) :
    ‖m95A02BasisFunction n x‖ ^ 2 =
      1 / (2 * Real.pi * ((n : ℝ) ^ 2 + 1)) := by
  rw [m95A02_norm_basisFunction, inv_pow]
  have h : 0 ≤ 2 * Real.pi * ((n : ℝ) ^ 2 + 1) := by positivity
  rw [Real.sq_sqrt h]
  ring

lemma m95A02_summable_uniform_kernel :
    Summable (fun n : ℤ =>
      1 / (2 * Real.pi * ((n : ℝ) ^ 2 + 1))) := by
  simpa [m95A02_sq_norm_basisFunction] using
    m95A02_summable_sq_norm_basisFunction 0

/-- The uniform point-evaluation kernel has arbitrarily small tails outside
a finite set of frequencies. -/
lemma m95A02_exists_finset_kernel_tail (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset ℤ,
      (∑' n : ℤ, if n ∈ s then 0 else
        1 / (2 * Real.pi * ((n : ℝ) ^ 2 + 1))) ≤ ε := by
  let w : ℤ → ℝ := fun n => 1 / (2 * Real.pi * ((n : ℝ) ^ 2 + 1))
  have hw : Summable w := m95A02_summable_uniform_kernel
  obtain ⟨s, hs⟩ := (summable_iff_vanishing.mp hw) (Iio ε) (Iio_mem_nhds hε)
  refine ⟨s, ?_⟩
  have htail : Summable (fun n : ℤ => if n ∈ s then 0 else w n) := by
    convert hw.indicator (s : Set ℤ)ᶜ using 1
    funext n
    simp [Set.indicator]
  apply htail.tsum_le_of_sum_le
  intro t
  have hdis : Disjoint (t \ s) s := Finset.disjoint_left.mpr (by
    intro n hn
    exact (Finset.mem_sdiff.mp hn).2)
  have hlt := hs (t \ s) hdis
  change ∑ n ∈ t \ s, w n < ε at hlt
  calc
    ∑ n ∈ t, (if n ∈ s then 0 else w n) = ∑ n ∈ t \ s, w n := by
      rw [Finset.sum_ite]
      simp only [Finset.sum_const_zero, zero_add]
      congr 1
      ext n
      simp
    _ ≤ ε := hlt.le

/-- Coordinate convergence controls every fixed finite block of Fourier
coefficients, uniformly in the evaluation point after inserting the exact
mode norms. -/
lemma m95A02_tendsto_finset_head
    (f : ℕ → m95A02H) (g : m95A02H)
    (hcoord : ∀ j : ℤ, Tendsto (fun n ↦ f n j) atTop (nhds (g j)))
    (s : Finset ℤ) :
    Tendsto (fun n => ∑ j ∈ s,
      ‖f n j - g j‖ *
        (Real.sqrt (2 * Real.pi * ((j : ℝ) ^ 2 + 1)))⁻¹)
      atTop (nhds 0) := by
  convert tendsto_finset_sum s (fun j hj => by
    have hj0 : Tendsto (fun n => ‖f n j - g j‖) atTop (nhds 0) := by
      simpa using (hcoord j).sub_const (g j) |>.norm
    simpa using hj0.mul_const
      (Real.sqrt (2 * Real.pi * ((j : ℝ) ^ 2 + 1)))⁻¹) using 1 <;> simp

lemma m95A02_summable_evaluation (f : m95A02H) (x : ℝ) :
    Summable (fun j : ℤ => f j * m95A02BasisFunction j x) := by
  have hA : Summable (fun j : ℤ => ‖f j‖ ^ (2 : ℝ)) := by
    simpa using (lp.memℓp f).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  have hB : Summable (fun j : ℤ => ‖m95A02BasisFunction j x‖ ^ (2 : ℝ)) := by
    simpa [Real.rpow_two] using m95A02_summable_sq_norm_basisFunction x
  have hh := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    (p := (2 : ℝ)) (q := (2 : ℝ)) (by
      exact { inv_add_inv_eq_inv := by norm_num
              left_pos := by norm_num
              right_pos := by norm_num })
    (fun j => norm_nonneg (f j))
    (fun j => norm_nonneg (m95A02BasisFunction j x)) hA hB
  rw [← summable_norm_iff]
  simpa [norm_mul] using hh.1

lemma m95A02Value_sub (f g : m95A02H) (x : ℝ) :
    m95A02Value f x - m95A02Value g x =
      ∑' j : ℤ, (f j - g j) * m95A02BasisFunction j x := by
  rw [m95A02Value, m95A02Value,
    ← (m95A02_summable_evaluation f x).tsum_sub
      (m95A02_summable_evaluation g x)]
  congr 1
  funext j
  ring

lemma m95A02_tail_eval_le (d : m95A02H) (s : Finset ℤ) (x : ℝ) :
    ‖∑' j : ℤ, if j ∈ s then 0 else
        d j * m95A02BasisFunction j x‖ ≤
      ‖d‖ * (∑' j : ℤ, if j ∈ s then 0 else
        1 / (2 * Real.pi * ((j : ℝ) ^ 2 + 1))) ^ (1 / 2 : ℝ) := by
  let A : ℤ → ℝ := fun j => ‖d j‖
  let B : ℤ → ℝ := fun j => if j ∈ s then 0 else
    ‖m95A02BasisFunction j x‖
  have hA : Summable (fun j => A j ^ (2 : ℝ)) := by
    simpa [A] using (lp.memℓp d).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  have hB : Summable (fun j => B j ^ (2 : ℝ)) := by
    have hs := m95A02_summable_uniform_kernel.indicator (s : Set ℤ)ᶜ
    convert hs using 1
    funext j
    by_cases hj : j ∈ s
    · simp [B, hj, Set.indicator]
    · simp [B, hj, Set.indicator, m95A02_sq_norm_basisFunction]
  have hh := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    (p := (2 : ℝ)) (q := (2 : ℝ)) (by
      exact { inv_add_inv_eq_inv := by norm_num
              left_pos := by norm_num
              right_pos := by norm_num })
    (fun j => norm_nonneg (d j)) (fun j => by dsimp [B]; positivity) hA hB
  have hnorm : Summable (fun j : ℤ =>
      ‖if j ∈ s then (0 : ℂ) else d j * m95A02BasisFunction j x‖) := by
    rw [← summable_norm_iff]
    simpa [A, B, norm_mul, apply_ite] using hh.1
  calc
    ‖∑' j : ℤ, if j ∈ s then 0 else d j * m95A02BasisFunction j x‖
        ≤ ∑' j : ℤ,
          ‖if j ∈ s then (0 : ℂ) else d j * m95A02BasisFunction j x‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ = ∑' j : ℤ, A j * B j := by
      congr 1
      funext j
      by_cases hj : j ∈ s <;> simp [A, B, hj, norm_mul]
    _ ≤ (∑' j : ℤ, A j ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
        (∑' j : ℤ, B j ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hh.2
    _ = ‖d‖ * (∑' j : ℤ, if j ∈ s then 0 else
        1 / (2 * Real.pi * ((j : ℝ) ^ 2 + 1))) ^ (1 / 2 : ℝ) := by
      congr 1
      · simpa [A] using (lp.norm_eq_tsum_rpow (by norm_num) d).symm
      · apply congrArg (fun z : ℝ => z ^ (1 / 2 : ℝ))
        apply tsum_congr
        intro j
        by_cases hj : j ∈ s
        · simp [B, hj]
        · simp [B, hj, Real.rpow_two, m95A02_sq_norm_basisFunction]

lemma m95A02_eval_dist_le_head_add_tail
    (f g : m95A02H) (s : Finset ℤ) (x : ℝ) :
    dist (m95A02Value f x) (m95A02Value g x) ≤
      (∑ j ∈ s, ‖f j - g j‖ *
        (Real.sqrt (2 * Real.pi * ((j : ℝ) ^ 2 + 1)))⁻¹) +
      ‖f - g‖ * (∑' j : ℤ, if j ∈ s then 0 else
        1 / (2 * Real.pi * ((j : ℝ) ^ 2 + 1))) ^ (1 / 2 : ℝ) := by
  let u : ℤ → ℂ := fun j => (f j - g j) * m95A02BasisFunction j x
  let uh : ℤ → ℂ := fun j => if j ∈ s then u j else 0
  let ut : ℤ → ℂ := fun j => if j ∈ s then 0 else u j
  have hu : Summable u := by
    simpa [u] using m95A02_summable_evaluation (f - g) x
  have huh : Summable uh := by
    apply summable_of_hasFiniteSupport
    exact s.finite_toSet.subset (by
      intro j hj
      have : j ∈ s := by
        by_contra hjs
        exact hj (by simp [uh, hjs])
      exact this)
  have hut : Summable ut := by
    convert hu.indicator (s : Set ℤ)ᶜ using 1
    funext j
    simp [ut, Set.indicator]
  rw [dist_eq_norm, m95A02Value_sub]
  have hsplit : (∑' j, u j) = (∑' j, uh j) + ∑' j, ut j := by
    rw [← huh.tsum_add hut]
    apply tsum_congr
    intro j
    simp only [u, uh, ut]
    by_cases hj : j ∈ s <;> simp [hj]
  change ‖∑' j, u j‖ ≤ _
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ (m95A02_tail_eval_le (f - g) s x))
  calc
    ‖∑' j, uh j‖ ≤ ∑' j, ‖uh j‖ := norm_tsum_le_tsum_norm (by
      rw [summable_norm_iff]
      exact huh)
    _ = ∑ j ∈ s, ‖f j - g j‖ *
        (Real.sqrt (2 * Real.pi * ((j : ℝ) ^ 2 + 1)))⁻¹ := by
      rw [tsum_eq_sum' (s := s) (by
        intro j hj
        have : j ∈ s := by
          by_contra hjs
          exact hj (by simp [uh, hjs])
        exact this)]
      · apply Finset.sum_congr rfl
        intro j hj
        simp [uh, u, hj, norm_mul, m95A02_norm_basisFunction]

lemma m95A02MaxDist_nonneg (f g : m95A02H) :
    0 ≤ m95A02MaxDist f g := by
  let C : ℝ := ‖f - g‖ *
    (∑' j : ℤ, 1 / (2 * Real.pi * ((j : ℝ) ^ 2 + 1))) ^ (1 / 2 : ℝ)
  have hpoint : ∀ x : ℝ,
      dist (m95A02Value f x) (m95A02Value g x) ≤ C := by
    intro x
    simpa [C] using m95A02_eval_dist_le_head_add_tail f g ∅ x
  have hbdd : BddAbove {r : ℝ | ∃ x ∈ Icc (0 : ℝ) (2 * Real.pi),
      r = dist (m95A02Value f x) (m95A02Value g x)} := by
    refine ⟨C, fun r hr => ?_⟩
    obtain ⟨x, hx, rfl⟩ := hr
    exact hpoint x
  have hmem : dist (m95A02Value f 0) (m95A02Value g 0) ∈
      {r : ℝ | ∃ x ∈ Icc (0 : ℝ) (2 * Real.pi),
        r = dist (m95A02Value f x) (m95A02Value g x)} :=
    ⟨0, ⟨le_rfl, by positivity⟩, rfl⟩
  unfold m95A02MaxDist
  exact dist_nonneg.trans (le_csSup hbdd hmem)

/-- The classical quadratic cosine series, in the normalization needed by
the kernel comparison. -/
lemma m95A02_hasSum_nat_one_sub_cos_div_sq
    {t : ℝ} (h0 : 0 ≤ t) (h2 : t ≤ 2 * Real.pi) :
    HasSum (fun n : ℕ => (1 - Real.cos (n * t)) / (n : ℝ) ^ 2)
      (Real.pi * t / 2 - t ^ 2 / 4) := by
  let u := t / (2 * Real.pi)
  have hu : u ∈ Icc (0 : ℝ) 1 := by
    constructor <;> dsimp [u]
    · positivity
    · apply div_le_one_of_le₀
      · exact h2
      · positivity
  have h1 := hasSum_zeta_nat (k := 1) (by norm_num)
  have hc := hasSum_one_div_nat_pow_mul_cos (k := 1) (by norm_num) hu
  have hh := h1.sub hc
  convert hh using 1
  · funext n
    dsimp [u]
    rw [show 2 * Real.pi * (n : ℝ) * (t / (2 * Real.pi)) = n * t by
      field_simp]
    ring
  · rw [bernoulli_two]
    norm_num [Polynomial.bernoulli, bernoulli_zero, bernoulli_one,
      bernoulli_two, Finset.sum_range_succ, u]
    field_simp
    ring

set_option maxHeartbeats 800000 in
lemma m95A02_tsum_int_one_sub_cos_div_sq
    {t : ℝ} (h0 : 0 ≤ t) (h2 : t ≤ 2 * Real.pi) :
    ∑' n : ℤ, (1 - Real.cos (n * t)) / (n : ℝ) ^ 2 =
      Real.pi * t - t ^ 2 / 2 := by
  let a : ℕ → ℝ := fun n => (1 - Real.cos (n * t)) / (n : ℝ) ^ 2
  let F : ℤ → ℝ := fun n => (1 - Real.cos (n * t)) / (n : ℝ) ^ 2
  have ha := m95A02_hasSum_nat_one_sub_cos_div_sq h0 h2
  have has : Summable a := by simpa [a] using ha.summable
  have hshift : Summable (fun n : ℕ => a (n + 1)) :=
    (summable_nat_add_iff 1).2 has
  have hFa (n : ℕ) : F (-(n + 1)) = a (n + 1) := by
    dsimp [F, a]
    have hc : (((-(n + 1 : ℤ) : ℤ) : ℝ)) = -((n + 1 : ℕ) : ℝ) := by
      norm_num
    rw [hc, neg_mul, Real.cos_neg]
    rw [neg_sq]
  have hneg : Summable (fun n : ℕ => F (-(n + 1))) := by
    apply hshift.congr
    intro n
    exact (hFa n).symm
  rw [tsum_of_nat_of_neg_add_one has hneg]
  have hfirst : (∑' n : ℕ, F n) = Real.pi * t / 2 - t ^ 2 / 4 := by
    simpa [F] using ha.tsum_eq
  have hsecond : (∑' n : ℕ, F (-(n + 1))) =
      Real.pi * t / 2 - t ^ 2 / 4 := by
    calc
      (∑' n : ℕ, F (-(n + 1))) = ∑' n : ℕ, a (n + 1) := by
        apply tsum_congr
        exact hFa
      _ = ∑' n : ℕ, a n := by
        have h := has.sum_add_tsum_nat_add 1
        simpa [a] using h
      _ = Real.pi * t / 2 - t ^ 2 / 4 := ha.tsum_eq
  rw [hfirst, hsecond]
  ring

set_option maxHeartbeats 800000 in
lemma m95A02_summable_int_one_sub_cos_div_sq
    {t : ℝ} (h0 : 0 ≤ t) (h2 : t ≤ 2 * Real.pi) :
    Summable (fun n : ℤ => (1 - Real.cos (n * t)) / (n : ℝ) ^ 2) := by
  let a : ℕ → ℝ := fun n => (1 - Real.cos (n * t)) / (n : ℝ) ^ 2
  let F : ℤ → ℝ := fun n => (1 - Real.cos (n * t)) / (n : ℝ) ^ 2
  have ha : Summable a :=
    (m95A02_hasSum_nat_one_sub_cos_div_sq h0 h2).summable
  apply Summable.of_nat_of_neg_add_one ha
  have hshift : Summable (fun n : ℕ => a (n + 1)) :=
    (summable_nat_add_iff 1).2 ha
  apply hshift.congr
  intro n
  dsimp [F, a]
  have hc : (((-(n + 1 : ℤ) : ℤ) : ℝ)) = -((n + 1 : ℕ) : ℝ) := by
    norm_num
  rw [hc, neg_mul, Real.cos_neg, neg_sq]

lemma m95A02_sq_norm_basisFunction_sub (n : ℤ) (x y : ℝ) :
    ‖m95A02BasisFunction n x - m95A02BasisFunction n y‖ ^ 2 =
      (1 - Real.cos ((n : ℝ) * (x - y))) /
        (Real.pi * ((n : ℝ) ^ 2 + 1)) := by
  unfold m95A02BasisFunction
  rw [← sub_div, norm_div, div_pow]
  have hfact :
      Complex.exp ((n : ℂ) * Complex.I * (x : ℂ)) -
          Complex.exp ((n : ℂ) * Complex.I * (y : ℂ)) =
        Complex.exp ((n : ℂ) * Complex.I * (y : ℂ)) *
          (Complex.exp (Complex.I * (((n : ℝ) * (x - y) : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hfact, norm_mul, Complex.norm_exp]
  have hre : (((n : ℂ) * Complex.I * (y : ℂ)).re) = 0 := by simp
  rw [hre, Real.exp_zero, one_mul,
    Complex.norm_exp_I_mul_ofReal_sub_one]
  have hden : 0 ≤ 2 * Real.pi * ((n : ℝ) ^ 2 + 1) := by positivity
  simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hden]
  rw [show |2 * Real.sin (((n : ℝ) * (x - y)) / 2)| ^ 2 =
      4 * Real.sin (((n : ℝ) * (x - y)) / 2) ^ 2 by
        rw [sq_abs]
        ring]
  have htrig : 2 * Real.sin (((n : ℝ) * (x - y)) / 2) ^ 2 =
      1 - Real.cos ((n : ℝ) * (x - y)) := by
    have hc := Real.cos_two_mul (((n : ℝ) * (x - y)) / 2)
    rw [show 2 * (((n : ℝ) * (x - y)) / 2) = (n : ℝ) * (x - y) by ring] at hc
    nlinarith [Real.sin_sq_add_cos_sq (((n : ℝ) * (x - y)) / 2)]
  rw [show 4 * Real.sin (((n : ℝ) * (x - y)) / 2) ^ 2 =
      2 * (1 - Real.cos ((n : ℝ) * (x - y))) by linarith]
  field_simp [Real.pi_ne_zero]

set_option maxHeartbeats 800000 in
lemma m95A02_summable_int_inv_sq :
    Summable (fun n : ℤ => 1 / (n : ℝ) ^ 2) := by
  have hn : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    (hasSum_zeta_nat (k := 1) (by norm_num)).summable
  apply Summable.of_nat_of_neg_add_one hn
  have hs : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff 1).2 hn
  apply hs.congr
  intro n
  congr 1
  push_cast
  ring

set_option maxHeartbeats 800000 in
lemma m95A02_tsum_int_inv_sq :
    ∑' n : ℤ, 1 / (n : ℝ) ^ 2 = Real.pi ^ 2 / 3 := by
  let a : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ 2
  let F : ℤ → ℝ := fun n => 1 / (n : ℝ) ^ 2
  have ha := hasSum_zeta_nat (k := 1) (by norm_num)
  have has : Summable a := by simpa [a] using ha.summable
  have hshift : Summable (fun n : ℕ => a (n + 1)) :=
    (summable_nat_add_iff 1).2 has
  have hFa (n : ℕ) : F (-(n + 1)) = a (n + 1) := by
    dsimp [F, a]
    congr 1
    push_cast
    ring
  have hneg : Summable (fun n : ℕ => F (-(n + 1))) :=
    hshift.congr (fun n => (hFa n).symm)
  rw [tsum_of_nat_of_neg_add_one has hneg]
  have hnat : (∑' n : ℕ, a n) = Real.pi ^ 2 / 6 := by
    rw [ha.tsum_eq]
    rw [bernoulli_two]
    norm_num
    ring
  have hneg' : (∑' n : ℕ, F (-(n + 1))) = Real.pi ^ 2 / 6 := by
    calc
      (∑' n : ℕ, F (-(n + 1))) = ∑' n : ℕ, a (n + 1) :=
        tsum_congr hFa
      _ = ∑' n : ℕ, a n := by
        simpa [a] using has.sum_add_tsum_nat_add 1
      _ = Real.pi ^ 2 / 6 := hnat
  rw [show (∑' n : ℕ, F n) = Real.pi ^ 2 / 6 by
        change (∑' n : ℕ, a n) = _
        exact hnat,
    hneg']
  ring

/-- Why this unblocks `apm_m95a02`: this is the sharp normalized Fourier-kernel
estimate whose square root, combined with Cauchy--Schwarz, gives the frozen
Hölder bound for `m95A02Value`. -/
theorem apm_m95A02_bridge_1 (x y : ℝ) :
    ∑' n : ℤ,
        ‖m95A02BasisFunction n x - m95A02BasisFunction n y‖ ^ 2 ≤
      |x - y| := by
  let t := |x - y|
  have ht0 : 0 ≤ t := abs_nonneg _
  have hcos (n : ℤ) :
      Real.cos ((n : ℝ) * (x - y)) = Real.cos ((n : ℝ) * t) := by
    dsimp [t]
    by_cases h : 0 ≤ x - y
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos (le_of_not_ge h), mul_neg, Real.cos_neg]
  have hL : Summable (fun n : ℤ =>
      ‖m95A02BasisFunction n x - m95A02BasisFunction n y‖ ^ 2) := by
    have hx := m95A02_summable_sq_norm_basisFunction x
    have hy := m95A02_summable_sq_norm_basisFunction y
    refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
      (fun n => ?_) ((hx.mul_left 2).add (hy.mul_left 2))
    have hs := norm_sub_le (m95A02BasisFunction n x) (m95A02BasisFunction n y)
    have hs2 := ((sq_le_sq₀ (norm_nonneg _)
      (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 hs)
    nlinarith [two_mul_le_add_sq ‖m95A02BasisFunction n x‖
      ‖m95A02BasisFunction n y‖]
  by_cases ht : t ≤ 2 * Real.pi
  · have hR := m95A02_summable_int_one_sub_cos_div_sq ht0 ht
    have hcmp := Summable.tsum_le_tsum (f := fun n : ℤ =>
        ‖m95A02BasisFunction n x - m95A02BasisFunction n y‖ ^ 2)
      (g := fun n : ℤ => (1 / Real.pi) *
        ((1 - Real.cos ((n : ℝ) * t)) / (n : ℝ) ^ 2))
      (fun n => by
        simp only
        rw [m95A02_sq_norm_basisFunction_sub, hcos]
        by_cases hn : n = 0
        · subst n
          simp
        · have hn2 : 0 < (n : ℝ) ^ 2 := sq_pos_of_ne_zero (by exact_mod_cast hn)
          have hnum : 0 ≤ 1 - Real.cos ((n : ℝ) * t) := sub_nonneg.mpr (Real.cos_le_one _)
          rw [one_div, inv_mul_eq_div]
          rw [show (1 - Real.cos ((n : ℝ) * t)) / (n : ℝ) ^ 2 / Real.pi =
              (1 - Real.cos ((n : ℝ) * t)) /
                (Real.pi * (n : ℝ) ^ 2) by ring]
          apply div_le_div_of_nonneg_left hnum
            (mul_pos Real.pi_pos hn2)
          exact mul_le_mul_of_nonneg_left (by linarith) Real.pi_nonneg)
      hL (hR.mul_left (1 / Real.pi))
    rw [tsum_mul_left, m95A02_tsum_int_one_sub_cos_div_sq ht0 ht] at hcmp
    dsimp [t] at hcmp ⊢
    have hp : 0 < Real.pi := Real.pi_pos
    calc
      _ ≤ (1 / Real.pi) * (Real.pi * |x - y| - |x - y| ^ 2 / 2) := hcmp
      _ ≤ |x - y| := by
        field_simp
        nlinarith [sq_nonneg |x - y|]
  · have hR := m95A02_summable_int_inv_sq.mul_left (2 / Real.pi)
    have hcmp := Summable.tsum_le_tsum (f := fun n : ℤ =>
        ‖m95A02BasisFunction n x - m95A02BasisFunction n y‖ ^ 2)
      (g := fun n : ℤ => (2 / Real.pi) * (1 / (n : ℝ) ^ 2))
      (fun n => by
        simp only
        rw [m95A02_sq_norm_basisFunction_sub, hcos]
        by_cases hn : n = 0
        · subst n
          simp
        · have hn2 : 0 < (n : ℝ) ^ 2 := sq_pos_of_ne_zero (by exact_mod_cast hn)
          have hnum : 0 ≤ 1 - Real.cos ((n : ℝ) * t) := sub_nonneg.mpr (Real.cos_le_one _)
          have hnum2 : 1 - Real.cos ((n : ℝ) * t) ≤ 2 := by
            linarith [Real.neg_one_le_cos ((n : ℝ) * t)]
          rw [one_div]
          apply (div_le_div_of_nonneg_right hnum2
            (mul_nonneg Real.pi_nonneg (by positivity))).trans
          rw [show 2 / Real.pi * ((n : ℝ) ^ 2)⁻¹ =
              2 / (Real.pi * (n : ℝ) ^ 2) by ring]
          apply div_le_div_of_nonneg_left (by norm_num)
            (mul_pos Real.pi_pos hn2)
          exact mul_le_mul_of_nonneg_left (by linarith) Real.pi_nonneg)
      hL hR
    rw [tsum_mul_left, m95A02_tsum_int_inv_sq] at hcmp
    dsimp [t] at ht ⊢
    exact le_of_lt (calc
      _ ≤ (2 / Real.pi) * (Real.pi ^ 2 / 3) := hcmp
      _ < 2 * Real.pi := by
        have hp := Real.pi_pos
        field_simp
        nlinarith
      _ < |x - y| := lt_of_not_ge ht)

/-- Cauchy--Schwarz turns the sharp kernel estimate into the frozen Hölder
estimate for every coefficient vector. -/
lemma m95A02_value_dist_le (f : m95A02H) (x y : ℝ) :
    dist (m95A02Value f x) (m95A02Value f y) ≤
      |x - y| ^ (1 / 2 : ℝ) * ‖f‖ := by
  let A : ℤ → ℝ := fun n ↦ ‖f n‖
  let B : ℤ → ℝ := fun n ↦
    ‖m95A02BasisFunction n x - m95A02BasisFunction n y‖
  have hA : Summable (fun n ↦ A n ^ (2 : ℝ)) := by
    simpa [A] using (lp.memℓp f).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  have hB : Summable (fun n ↦ B n ^ (2 : ℝ)) := by
    have hx := m95A02_summable_sq_norm_basisFunction x
    have hy := m95A02_summable_sq_norm_basisFunction y
    refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun n ↦ ?_)
      ((hx.mul_left 2).add (hy.mul_left 2))
    dsimp [B]
    rw [Real.rpow_two]
    have ht := norm_sub_le (m95A02BasisFunction n x) (m95A02BasisFunction n y)
    have ht2 := ((sq_le_sq₀ (norm_nonneg _)
      (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 ht)
    have hcross := two_mul_le_add_sq
      ‖m95A02BasisFunction n x‖ ‖m95A02BasisFunction n y‖
    calc
      ‖m95A02BasisFunction n x - m95A02BasisFunction n y‖ ^ 2
          ≤ (‖m95A02BasisFunction n x‖ +
              ‖m95A02BasisFunction n y‖) ^ 2 := ht2
      _ = ‖m95A02BasisFunction n x‖ ^ 2 +
            2 * ‖m95A02BasisFunction n x‖ * ‖m95A02BasisFunction n y‖ +
            ‖m95A02BasisFunction n y‖ ^ 2 := by ring
      _ ≤ 2 * ‖m95A02BasisFunction n x‖ ^ 2 +
            2 * ‖m95A02BasisFunction n y‖ ^ 2 := by linarith
  have hholder := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    (p := (2 : ℝ)) (q := (2 : ℝ)) (by
      exact { inv_add_inv_eq_inv := by norm_num
              left_pos := by norm_num
              right_pos := by norm_num })
    (fun n ↦ norm_nonneg (f n))
    (fun n ↦ norm_nonneg (m95A02BasisFunction n x - m95A02BasisFunction n y))
    hA hB
  have hu_norm : Summable (fun n : ℤ ↦
      ‖f n * (m95A02BasisFunction n x - m95A02BasisFunction n y)‖) := by
    simpa [A, B, norm_mul] using hholder.1
  have heval (z : ℝ) : Summable (fun n : ℤ ↦
      f n * m95A02BasisFunction n z) := by
    have hBz := m95A02_summable_sq_norm_basisFunction z
    have hh := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
      (p := (2 : ℝ)) (q := (2 : ℝ)) (by
        exact { inv_add_inv_eq_inv := by norm_num
                left_pos := by norm_num
                right_pos := by norm_num })
      (fun n ↦ norm_nonneg (f n))
      (fun n ↦ norm_nonneg (m95A02BasisFunction n z)) hA (by
        simpa [Real.rpow_two] using hBz)
    rw [← summable_norm_iff]
    simpa [A, norm_mul] using hh.1
  rw [dist_eq_norm, m95A02Value, m95A02Value,
    ← (heval x).tsum_sub (heval y)]
  simp_rw [← mul_sub]
  calc
    ‖∑' n : ℤ, f n * (m95A02BasisFunction n x - m95A02BasisFunction n y)‖
        ≤ ∑' n : ℤ,
          ‖f n * (m95A02BasisFunction n x - m95A02BasisFunction n y)‖ :=
      norm_tsum_le_tsum_norm hu_norm
    _ = ∑' n : ℤ, A n * B n := by simp [A, B, norm_mul]
    _ ≤ (∑' n : ℤ, A n ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
        (∑' n : ℤ, B n ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hholder.2
    _ ≤ ‖f‖ * |x - y| ^ (1 / 2 : ℝ) := by
      rw [show (∑' n : ℤ, A n ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = ‖f‖ by
        simpa [A] using (lp.norm_eq_tsum_rpow (by norm_num) f).symm]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg f)
      exact Real.rpow_le_rpow (by positivity)
        (by simpa [B, Real.rpow_two] using apm_m95A02_bridge_1 x y) (by norm_num)
    _ = |x - y| ^ (1 / 2 : ℝ) * ‖f‖ := by ring

/-- Why this unblocks `apm_m95a02`: it packages the missing bilateral weighted
tail argument: bounded ℓ² vectors converging in every coordinate have Fourier
realizations converging uniformly in the custom maximum distance. -/
theorem apm_m95A02_bridge_2
    (f : ℕ → m95A02H) (g : m95A02H)
    (hcoord : ∀ j : ℤ, Tendsto (fun n ↦ f n j) atTop (nhds (g j)))
    (hbounded : ∃ C : ℝ, ∀ n : ℕ, ‖f n‖ ≤ C) :
    Tendsto (fun n => m95A02MaxDist (f n) g) atTop (nhds 0) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards with n
    exact ha.trans_le (m95A02MaxDist_nonneg (f n) g)
  · intro ε hε
    obtain ⟨C, hC⟩ := hbounded
    have hC0 : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
    let M : ℝ := C + ‖g‖
    have hM0 : 0 ≤ M := by dsimp [M]; positivity
    let q : ℝ := ε / (2 * (M + 1))
    have hq : 0 < q := by
      dsimp [q]
      positivity
    obtain ⟨s, hs⟩ := m95A02_exists_finset_kernel_tail (q ^ 2) (sq_pos_of_pos hq)
    have hhead := (m95A02_tendsto_finset_head f g hcoord s).eventually
      (eventually_lt_nhds (by linarith : 0 < ε / 2))
    filter_upwards [hhead] with n hn
    have hdn : ‖f n - g‖ ≤ M := by
      calc
        ‖f n - g‖ ≤ ‖f n‖ + ‖g‖ := norm_sub_le _ _
        _ ≤ C + ‖g‖ := add_le_add (hC n) le_rfl
        _ = M := rfl
    have hsqrt :
        (∑' j : ℤ, if j ∈ s then 0 else
          1 / (2 * Real.pi * ((j : ℝ) ^ 2 + 1))) ^ (1 / 2 : ℝ) ≤ q := by
      rw [← Real.sqrt_eq_rpow]
      calc
        √(∑' j : ℤ, if j ∈ s then 0 else
            1 / (2 * Real.pi * ((j : ℝ) ^ 2 + 1))) ≤ √(q ^ 2) :=
          Real.sqrt_le_sqrt hs
        _ = q := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hq]
    have htail : ‖f n - g‖ *
        (∑' j : ℤ, if j ∈ s then 0 else
          1 / (2 * Real.pi * ((j : ℝ) ^ 2 + 1))) ^ (1 / 2 : ℝ) < ε / 2 := by
      calc
        _ ≤ M * q := mul_le_mul hdn hsqrt (by positivity) hM0
        _ < ε / 2 := by
          dsimp [q]
          have hden : 0 < M + 1 := by positivity
          field_simp
          nlinarith
    let D : ℝ := (∑ j ∈ s, ‖f n j - g j‖ *
        (Real.sqrt (2 * Real.pi * ((j : ℝ) ^ 2 + 1)))⁻¹) +
      ‖f n - g‖ * (∑' j : ℤ, if j ∈ s then 0 else
        1 / (2 * Real.pi * ((j : ℝ) ^ 2 + 1))) ^ (1 / 2 : ℝ)
    have hD0 : 0 ≤ D := by
      dsimp [D]
      positivity
    have hDε : D < ε := by
      dsimp [D]
      linarith
    exact (m95A02MaxDist_le_of_forall (f n) g D hD0 (by
      intro x hx
      exact m95A02_eval_dist_le_head_add_tail (f n) g s x)).trans_lt hDε

theorem apm_m95a02 :
    (∃ b : HilbertBasis ℤ ℂ m95A02H,
      ∀ n : ℤ, b n = lp.single 2 n 1 ∧
        ∀ x : ℝ, m95A02Value (b n) x = m95A02BasisFunction n x) ∧
    (∀ (f : m95A02H) (x y : ℝ),
      dist (m95A02Value f x) (m95A02Value f y) ≤
        |x - y| ^ (1 / 2 : ℝ) * ‖f‖) ∧
    (∀ (f : ℕ → m95A02H) (g : m95A02H),
      Tendsto (fun n => toWeakSpace ℂ m95A02H (f n)) atTop
        (nhds (toWeakSpace ℂ m95A02H g)) →
      Tendsto (fun n => m95A02MaxDist (f n) g) atTop (nhds 0)) := by
  refine ⟨?_, ?_⟩
  · let b : HilbertBasis ℤ ℂ m95A02H :=
      HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ m95A02H)
    refine ⟨b, ?_⟩
    intro n
    have hbn : b n = lp.single 2 n 1 := by
      simpa [b] using (b.repr_symm_single n).symm
    constructor
    · exact hbn
    · intro x
      rw [hbn]
      exact m95A02Value_single n x
  · /-
    PASS-1 boundary (Codex): the canonical Hilbert basis clause is proved,
    and `m95A02Value_zero` plus `m95A02MaxDist_self` now formally verify the
    zero evaluation and diagonal behavior of the custom supremum encoding.

    The remaining Hölder estimate reduces by Cauchy–Schwarz to
    the sharp Fourier-kernel bound
    `∑ n : ℤ, |exp (n*I*x) - exp (n*I*y)|² /
      (2π (n²+1)) ≤ |x-y|`.
    I searched Mathlib and the repository for this periodic Sobolev kernel
    estimate, the equivalent bilateral-series identity for
    `∑ n : ℤ, cos (n*d) / (n²+1)`,
    `ArzelaAscoli.isCompact_of_equicontinuous`, weak-topology evaluation
    criteria, and `HilbertBasis`/`lp.single` infrastructure. Mathlib supplies
    `Real.summable_abs_int_rpow` and Poisson summation, but no compiled
    artifact supplies the sharp kernel inequality. `ConstructionTargets.LusinN`
    proves an FTC distance estimate for actual absolutely continuous
    functions, but it cannot apply before constructing an AC representative
    of this sequence-defined Fourier realization.

    After that inequality, the final clause still requires boundedness of a
    weakly convergent sequence, continuity of every evaluation functional,
    Arzelà–Ascoli on `[0,2π]`, and conversion of uniform convergence to the
    custom `sSup` expression `m95A02MaxDist`. I also tried a direct spectral
    route: weak convergence gives convergence of every finite set of Fourier
    coordinates, while Cauchy--Schwarz and the summable weights
    `1 / (n²+1)` should control the remaining evaluation tail uniformly in
    `x`. Mathlib has `lp.single`, weak-space evaluation criteria, and generic
    `tsum` Cauchy--Schwarz machinery, but no assembled lemma connecting them
    to this bilateral weighted Fourier series. Sibling `m02A01` confirms that
    even weak convergence of the `lp.single` sequence still lacks a packaged
    coordinate/Riesz bridge in this corpus. Searches of all 170 closed
    artifacts, `ConstructionTargets/`, `YoungL2.lean`, boundary comments, and
    git history found no stronger route. Those analytic and order-theory
    bridges were not completed within this pass.

    Closer hop 1 extracted `m95A02Value_single`, so evaluation of every basis
    coordinate is now available independently of the bundled basis proof. A
    renewed Mathlib source search also found `lp.inner_single_right`, which
    supplies the previously missing algebraic Riesz-coordinate identity
    `⟪f, single j 1⟫ = ⟪f j, 1⟫`. Thus weak convergence can in principle be
    specialized to coordinate convergence without constructing a new Riesz
    theorem. The still-open bridge is applying the weak-space filter criterion
    with these inner-product functionals and then proving a uniform bilateral
    tail estimate strong enough for `m95A02MaxDist`; no corpus artifact
    packages that analytic sum.

    Closer hop 2 closes the weak-to-coordinate bridge as
    `m95A02_tendsto_coord_of_weak`.  It applies
    `WeakBilin.tendsto_iff_forall_eval_tendsto` to the Riesz functional of
    `lp.single 2 j 1`, then uses `InnerProductSpace.toDual_apply_apply` and
    `lp.inner_single_left` to identify the pairing with the `j`th coefficient.
    Searches of Mathlib's bilateral `ℤ` summability, Cauchy--Schwarz, tsum-tail,
    and integer-rpow sources, along with the closed corpus and construction
    libraries, still found no uniform estimate for the normalized Fourier
    tail.  Thus the remaining bridge is now exactly: combine finite-coordinate
    convergence with weak boundedness and the summable weights
    `1 / (n²+1)`, then transport the resulting uniform evaluation bound through
    the set-valued `sSup` in `m95A02MaxDist`.

    Closer hop 3 closes that final order-theory transport as
    `m95A02MaxDist_le_of_forall`: any nonnegative constant bounding all
    pointwise evaluation distances on `[0,2π]` also bounds the custom real
    `sSup`.  It uses `Real.sSup_le`, so no boundedness or nonemptiness
    bookkeeping remains at the call site.  The remaining boundary is now
    purely analytic: obtain a uniform pointwise bound tending to zero from
    finite-coordinate convergence and bounded ℓ² norms.  Source searches
    found generic `Summable` cofinite-tail and Cauchy--Schwarz APIs, but no
    theorem assembling the bilateral integer weights or the normalized
    exponential evaluation map; this weighted tail estimate still must be
    developed locally.
    -/
    refine ⟨?_, ?_⟩
    · exact m95A02_value_dist_le
    · intro f g hweak
      apply apm_m95A02_bridge_2 f g
      · intro j
        exact m95A02_tendsto_coord_of_weak f g hweak j
      · exact m95A02_bounded_of_weak_convergence f g hweak
