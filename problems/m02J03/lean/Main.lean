import Mathlib

/-!
# APM m02J03

## Statement repairs

None.

## Encoding notes

The source indices start at one.  Lean's sequence starts at zero, so the
`n`th convex combination is indexed by `Fin (n + 1)` and uses exactly
`x 0, …, x n`.  The coefficients remain real, strictly positive, and sum to
one as required.
-/

open Filter InnerProductSpace
open scoped BigOperators Topology

/- Strong convergence gives the easy direction of the Radon--Riesz
equivalence.  Keeping it separate isolates the genuinely Hilbertian reverse
direction, which must additionally use `hweak`. -/
lemma apm_m02j03_norm_tendsto_of_tendsto
    {H : Type*} [NormedAddCommGroup H]
    {x : ℕ → H} {x₀ : H}
    (h : Tendsto x atTop (nhds x₀)) :
    Tendsto (fun n ↦ ‖x n‖) atTop (nhds ‖x₀‖) :=
  (continuous_norm.tendsto x₀).comp h

/-- The Hilbertian reverse Radon--Riesz implication. The weak hypothesis is
complex-valued; taking real parts gives the norm-square expansion. -/
lemma apm_m02j03_tendsto_of_weak_and_norm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {x : ℕ → H} {x₀ : H}
    (hweak : ∀ y : H,
      Tendsto (fun n ↦ inner ℂ (x n) y) atTop (nhds (inner ℂ x₀ y)))
    (hnorm : Tendsto (fun n ↦ ‖x n‖) atTop (nhds ‖x₀‖)) :
    Tendsto x atTop (nhds x₀) := by
  have h_inner : Tendsto (fun n => Complex.re (inner ℂ (x n) x₀)) atTop
      (𝓝 (‖x₀‖ ^ 2)) := by
    have hre := Complex.continuous_re.tendsto (inner ℂ x₀ x₀) |>.comp (hweak x₀)
    have heq : Complex.re (inner ℂ x₀ x₀) = ‖x₀‖ ^ 2 := by
      exact @inner_self_eq_norm_sq ℂ _ _ _ _ x₀
    rw [heq] at hre
    exact hre
  have h_norm_sq : Tendsto (fun n => ‖x n‖ ^ 2) atTop (𝓝 (‖x₀‖ ^ 2)) :=
    hnorm.pow 2
  have h_rhs : Tendsto
      (fun n => ‖x n‖ ^ 2 - 2 * Complex.re (inner ℂ (x n) x₀) + ‖x₀‖ ^ 2)
      atTop (𝓝 0) := by
    have h2 : Tendsto (fun n => 2 * Complex.re (inner ℂ (x n) x₀)) atTop
        (𝓝 (2 * ‖x₀‖ ^ 2)) := tendsto_const_nhds.mul h_inner
    have hsub := Tendsto.sub h_norm_sq h2
    have hzero : ‖x₀‖ ^ 2 - 2 * ‖x₀‖ ^ 2 + ‖x₀‖ ^ 2 = (0 : ℝ) := by ring
    rw [← hzero]
    exact Tendsto.add hsub tendsto_const_nhds
  have hsq : Tendsto (fun n => ‖x n - x₀‖ ^ 2) atTop (𝓝 0) :=
    Tendsto.congr (fun n => (norm_sub_sq (𝕜 := ℂ) _ _).symm) h_rhs
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  rw [Real.sqrt_zero] at hsqrt
  have hnorm_sub : Tendsto (fun n => ‖x n - x₀‖) atTop (𝓝 0) :=
    hsqrt.congr (fun n => Real.sqrt_sq (norm_nonneg _))
  simpa [tendsto_iff_norm_sub_tendsto_zero] using hnorm_sub

/-- Why this unblocks the first conjunct of `apm_m02j03`: this is the
uniform-boundedness consequence of pointwise convergence of the inner-product
functionals associated to a weakly convergent sequence. -/
theorem apm_m02J03_bridge_1
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (x : ℕ → H) (x₀ : H)
    (hweak : ∀ y : H,
      Tendsto (fun n ↦ inner ℂ (x n) y) atTop (nhds (inner ℂ x₀ y))) :
    ∃ C : ℝ, ∀ n : ℕ, ‖x n‖ ≤ C := by
  let g : ℕ → H →SL[RingHom.id ℂ] ℂ := fun n => innerSL ℂ (x n)
  have hg : ∀ y : H, ∃ C : ℝ, ∀ n : ℕ, ‖g n y‖ ≤ C := by
    intro y
    have hb : BddAbove (Set.range (fun n => ‖inner ℂ (x n) y‖)) :=
      ((hweak y).norm).bddAbove_range
    rcases hb with ⟨C, hC⟩
    exact ⟨C, fun n => by
      simpa [g, innerSL_apply_apply] using hC ⟨n, rfl⟩⟩
  rcases banach_steinhaus hg with ⟨C, hC⟩
  exact ⟨C, fun n => by simpa [g, innerSL_apply_norm] using hC n⟩

lemma apm_m02J03_mem_closure_convexHull
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (x : ℕ → H) (x₀ : H)
    (hweak : ∀ y : H,
      Tendsto (fun n ↦ inner ℂ (x n) y) atTop (nhds (inner ℂ x₀ y))) :
    x₀ ∈ closure (convexHull ℝ (Set.range x)) := by
  letI : Module ℝ H := Module.complexToReal H
  letI : IsScalarTower ℝ ℂ H :=
    ⟨fun r z v => by
      rw [← Complex.coe_smul]
      exact smul_assoc (r : ℂ) z v⟩
  have hw : Tendsto (fun n => toWeakSpace ℂ H (x n)) atTop
      (nhds (toWeakSpace ℂ H x₀)) := by
    have hinj : Function.Injective (topDualPairing ℂ H).flip := by
      intro a b hab
      have hz : ∀ f : StrongDual ℂ H, f (a - b) = 0 := by
        intro f
        rw [map_sub, sub_eq_zero]
        exact DFunLike.congr_fun hab f
      have hs := hz (innerSL ℂ (a - b))
      rw [innerSL_apply_apply, inner_self_eq_zero] at hs
      exact sub_eq_zero.mp hs
    apply (WeakBilin.tendsto_iff_forall_eval_tendsto _ hinj).2
    intro f
    let y : H := (InnerProductSpace.toDual ℂ H).symm f
    change Tendsto (fun n => f (x n)) atTop (nhds (f x₀))
    have hc := Complex.continuous_conj.tendsto (inner ℂ x₀ y) |>.comp (hweak y)
    have hval (v : H) : starRingEnd ℂ (inner ℂ v y) = f v := by
      rw [inner_conj_symm]
      have hy : InnerProductSpace.toDual ℂ H y = f := by
        exact (InnerProductSpace.toDual ℂ H).apply_symm_apply f
      exact DFunLike.congr_fun hy v
    rw [hval x₀] at hc
    apply hc.congr'
    exact Filter.Eventually.of_forall fun n => hval (x n)
  have hr : toWeakSpace ℂ H x₀ ∈
      closure (toWeakSpace ℂ H '' Set.range x) := by
    apply mem_closure_of_tendsto hw
    exact Eventually.of_forall fun n => ⟨x n, ⟨n, rfl⟩, rfl⟩
  have hc : toWeakSpace ℂ H x₀ ∈
      closure (toWeakSpace ℂ H '' convexHull ℝ (Set.range x)) :=
    closure_mono (Set.image_mono (subset_convexHull ℝ _)) hr
  rw [← (convex_convexHull ℝ (Set.range x)).toWeakSpace_closure ℂ] at hc
  rcases hc with ⟨z, hz, heq⟩
  with_reducible_and_instances
    apply_fun (toWeakSpace ℂ H).symm at heq
    have hzx : z = x₀ := by simpa using heq
    exact hzx ▸ hz

lemma apm_m02J03_exists_finite_convex_approx
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (x : ℕ → H) (x₀ : H)
    (hweak : ∀ y : H,
      Tendsto (fun n ↦ inner ℂ (x n) y) atTop (nhds (inner ℂ x₀ y)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (q : ι → ℕ),
      (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
      ‖(∑ i, (w i : ℂ) • x (q i)) - x₀‖ < ε := by
  have hcl := apm_m02J03_mem_closure_convexHull x x₀ hweak
  rcases (Metric.mem_closure_iff.1 hcl) ε hε with ⟨z, hz, hdist⟩
  rcases mem_convexHull_iff_exists_fintype.1 hz with
    ⟨ι, inst, w, v, hw, hsum, hv, hvsum⟩
  letI : Fintype ι := inst
  choose q hq using fun i => hv i
  refine ⟨ι, inst, w, q, hw, hsum, ?_⟩
  have heq : ∑ i, (w i : ℂ) • x (q i) = z := by
    rw [← hvsum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hq i, Complex.coe_smul]
  rw [heq, norm_sub_rev]
  simpa [dist_eq_norm] using hdist

lemma apm_m02J03_exists_finsupp_convex_approx
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (x : ℕ → H) (x₀ : H)
    (hweak : ∀ y : H,
      Tendsto (fun n ↦ inner ℂ (x n) y) atTop (nhds (inner ℂ x₀ y)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℕ →₀ ℝ, (∀ j, 0 ≤ a j) ∧ a.sum (fun _ c => c) = 1 ∧
      ‖a.sum (fun j c => (c : ℂ) • x j) - x₀‖ < ε := by
  classical
  rcases apm_m02J03_exists_finite_convex_approx x x₀ hweak hε with
    ⟨ι, inst, w, q, hw, hsum, happ⟩
  letI : Fintype ι := inst
  let a : ℕ →₀ ℝ := ∑ i, Finsupp.single (q i) (w i)
  refine ⟨a, ?_, ?_, ?_⟩
  · intro j
    simp only [a, Finsupp.finset_sum_apply, Finsupp.single_apply]
    exact Finset.sum_nonneg fun i hi => by
      split_ifs
      · exact hw i
      · exact le_rfl
  · change (∑ i, Finsupp.single (q i) (w i)).sum (fun _ c => c) = 1
    rw [← Finsupp.sum_finset_sum_index (fun _ => rfl) (fun _ _ _ => rfl)]
    simpa using hsum
  · convert happ using 1
    change ‖(∑ i, Finsupp.single (q i) (w i)).sum
        (fun j c => (c : ℂ) • x j) - x₀‖ = _
    rw [← Finsupp.sum_finset_sum_index (fun _ => by simp)
      (fun _ _ _ => by simp [add_smul])]
    simp [Complex.coe_smul]

lemma apm_m02J03_findGreatest_available_tendsto (B : ℕ → ℕ) :
    Tendsto (fun n => Nat.findGreatest (fun k => B k ≤ n) n) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro k
  refine ⟨max k (B k), fun n hn => ?_⟩
  apply Nat.le_findGreatest
  · exact le_trans (le_max_left _ _) hn
  · exact le_trans (le_max_right _ _) hn

lemma apm_m02J03_exists_finsupp_approximating_sequence
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (x : ℕ → H) (x₀ : H)
    (hweak : ∀ y : H,
      Tendsto (fun n ↦ inner ℂ (x n) y) atTop (nhds (inner ℂ x₀ y))) :
    ∃ a : ℕ → ℕ →₀ ℝ,
      (∀ k j, 0 ≤ a k j) ∧
      (∀ k, (a k).sum (fun _ c => c) = 1) ∧
      Tendsto (fun k => (a k).sum (fun j c => (c : ℂ) • x j)) atTop (nhds x₀) := by
  have hex (k : ℕ) := apm_m02J03_exists_finsupp_convex_approx x x₀ hweak
    (show (0 : ℝ) < 1 / (k + 1) by positivity)
  choose a ha using hex
  refine ⟨a, fun k => (ha k).1, fun k => (ha k).2.1, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_one_div_lt hε
  refine ⟨K, fun n hn => ?_⟩
  rw [dist_eq_norm]
  have hdiv : (1 : ℝ) / (n + 1 : ℕ) ≤ 1 / (K + 1 : ℕ) := by
    apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (K + 1 : ℕ))
    exact_mod_cast Nat.add_le_add_right hn 1
  exact lt_trans (lt_of_lt_of_le (ha n).2.2 (by simpa using hdiv)) hK

lemma apm_m02J03_support_lt_sup_add_one (a : ℕ →₀ ℝ) {j : ℕ}
    (hj : j ∈ a.support) : j < a.support.sup id + 1 := by
  exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hj)

lemma apm_m02J03_finsupp_sum_eq_fin_sum (a : ℕ →₀ ℝ) (N : ℕ)
    (hN : ∀ j ∈ a.support, j < N) :
    ∑ i : Fin N, a i.val = a.sum (fun _ c => c) := by
  classical
  rw [Finsupp.sum]
  rw [Fin.sum_univ_eq_sum_range]
  symm
  apply Finset.sum_subset
  · intro j hj
    exact Finset.mem_range.mpr (hN j hj)
  · intro j hjRange hjSupport
    have : a j = 0 := by simpa [Finsupp.mem_support_iff] using hjSupport
    simp [this]

lemma apm_m02J03_finsupp_vsum_eq_fin_sum
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x : ℕ → H) (a : ℕ →₀ ℝ) (N : ℕ)
    (hN : ∀ j ∈ a.support, j < N) :
    ∑ i : Fin N, (a i.val : ℂ) • x i.val =
      a.sum (fun j c => (c : ℂ) • x j) := by
  classical
  rw [Finsupp.sum]
  rw [show (∑ i : Fin N, (a i.val : ℂ) • x i.val) =
      (∑ j ∈ Finset.range N, (a j : ℂ) • x j) by
        exact Fin.sum_univ_eq_sum_range (fun j => (a j : ℂ) • x j) N]
  symm
  apply Finset.sum_subset
  · intro j hj
    exact Finset.mem_range.mpr (hN j hj)
  · intro j hjRange hjSupport
    have : a j = 0 := by simpa [Finsupp.mem_support_iff] using hjSupport
    simp [this]

lemma apm_m02J03_findGreatest_eventually_available (B : ℕ → ℕ) :
    ∀ᶠ n in atTop,
      B (Nat.findGreatest (fun k => B k ≤ n + 1) n) ≤ n + 1 := by
  filter_upwards [eventually_ge_atTop (B 0)] with n hn
  apply Nat.findGreatest_spec (P := fun k => B k ≤ n + 1) (Nat.zero_le n)
  exact hn.trans (Nat.le_add_right n 1)

def apm_m02J03_supportBound (a : ℕ → ℕ →₀ ℝ) (k : ℕ) : ℕ :=
  (a k).support.sup id + 1

def apm_m02J03_schedule (a : ℕ → ℕ →₀ ℝ) (n : ℕ) : ℕ :=
  Nat.findGreatest (fun k => apm_m02J03_supportBound a k ≤ n + 1) n

lemma apm_m02J03_schedule_tendsto (a : ℕ → ℕ →₀ ℝ) :
    Tendsto (apm_m02J03_schedule a) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro k
  refine ⟨max k (apm_m02J03_supportBound a k), fun n hn => ?_⟩
  unfold apm_m02J03_schedule
  apply Nat.le_findGreatest
  · exact le_trans (le_max_left _ _) hn
  · exact (le_trans (le_max_right _ _) hn).trans (Nat.le_add_right n 1)

noncomputable def apm_m02J03_paddedCoeff
    (a : ℕ → ℕ →₀ ℝ) (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  if apm_m02J03_supportBound a (apm_m02J03_schedule a n) ≤ n + 1 then
    a (apm_m02J03_schedule a n) i.val
  else 1 / (n + 1 : ℕ)

noncomputable def apm_m02J03_strictCoeff
    (a : ℕ → ℕ →₀ ℝ) (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  let δ : ℝ := 1 / (n + 2 : ℕ)
  (1 - δ) * apm_m02J03_paddedCoeff a n i + δ / (n + 1 : ℕ)

lemma apm_m02J03_paddedCoeff_nonneg
    (a : ℕ → ℕ →₀ ℝ) (ha : ∀ k j, 0 ≤ a k j) (n : ℕ) (i : Fin (n + 1)) :
    0 ≤ apm_m02J03_paddedCoeff a n i := by
  unfold apm_m02J03_paddedCoeff
  split_ifs
  · exact ha _ _
  · positivity

lemma apm_m02J03_paddedCoeff_sum
    (a : ℕ → ℕ →₀ ℝ) (ha : ∀ k, (a k).sum (fun _ c => c) = 1) (n : ℕ) :
    ∑ i : Fin (n + 1), apm_m02J03_paddedCoeff a n i = 1 := by
  classical
  unfold apm_m02J03_paddedCoeff
  split_ifs with hgood
  · rw [apm_m02J03_finsupp_sum_eq_fin_sum]
    · exact ha _
    · intro j hj
      exact (apm_m02J03_support_lt_sup_add_one _ hj).trans_le hgood
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp

lemma apm_m02J03_strictCoeff_pos_sum
    (a : ℕ → ℕ →₀ ℝ) (ha0 : ∀ k j, 0 ≤ a k j)
    (ha1 : ∀ k, (a k).sum (fun _ c => c) = 1) (n : ℕ) :
    (∀ i : Fin (n + 1), 0 < apm_m02J03_strictCoeff a n i) ∧
      ∑ i : Fin (n + 1), apm_m02J03_strictCoeff a n i = 1 := by
  classical
  let δ : ℝ := 1 / (n + 2 : ℕ)
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hδle : δ ≤ 1 := by
    dsimp [δ]
    apply (div_le_one (by positivity)).2
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    norm_num at ⊢
    linarith
  constructor
  · intro i
    unfold apm_m02J03_strictCoeff
    dsimp only
    have hb := apm_m02J03_paddedCoeff_nonneg a ha0 n i
    have hu : 0 < δ / (n + 1 : ℕ) := by positivity
    exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hδle) hb) hu
  · unfold apm_m02J03_strictCoeff
    rw [Finset.sum_add_distrib, ← Finset.mul_sum,
      apm_m02J03_paddedCoeff_sum a ha1 n]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring

/-- The remaining convergence estimate for the scheduled, padded and
strictly-positive perturbation of a `Finsupp` convex approximation. -/
theorem apm_m02J03_strictCoeff_tendsto
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x : ℕ → H) (x₀ : H) (a : ℕ → ℕ →₀ ℝ)
    (ha0 : ∀ k j, 0 ≤ a k j)
    (ha1 : ∀ k, (a k).sum (fun _ c => c) = 1)
    (hconv : Tendsto (fun k => (a k).sum (fun j c => (c : ℂ) • x j))
      atTop (nhds x₀))
    (hbound : ∃ C : ℝ, ∀ n : ℕ, ‖x n‖ ≤ C) :
    Tendsto
      (fun n => ∑ i : Fin (n + 1),
        (apm_m02J03_strictCoeff a n i : ℂ) • x i.val)
      atTop (nhds x₀) := by
  classical
  let S : ℕ → H := fun k => (a k).sum (fun j c => (c : ℂ) • x j)
  let P : ℕ → H := fun n => ∑ i : Fin (n + 1),
    (apm_m02J03_paddedCoeff a n i : ℂ) • x i.val
  let U : ℕ → H := fun n => ∑ i : Fin (n + 1),
    (((1 : ℝ) / (n + 1 : ℕ) : ℝ) : ℂ) • x i.val
  have hSK : Tendsto (fun n => S (apm_m02J03_schedule a n)) atTop (nhds x₀) :=
    hconv.comp (apm_m02J03_schedule_tendsto a)
  have hPS : ∀ᶠ n in atTop, P n = S (apm_m02J03_schedule a n) := by
    filter_upwards [apm_m02J03_findGreatest_eventually_available
      (apm_m02J03_supportBound a)] with n hgood
    change apm_m02J03_supportBound a (apm_m02J03_schedule a n) ≤ n + 1 at hgood
    simp only [P, S]
    rw [show (∑ i : Fin (n + 1),
        (apm_m02J03_paddedCoeff a n i : ℂ) • x i.val) =
        ∑ i : Fin (n + 1),
          (a (apm_m02J03_schedule a n) i.val : ℂ) • x i.val by
      apply Finset.sum_congr rfl
      intro i hi
      rw [apm_m02J03_paddedCoeff, if_pos hgood]]
    apply apm_m02J03_finsupp_vsum_eq_fin_sum
    intro j hj
    exact (apm_m02J03_support_lt_sup_add_one _ hj).trans_le hgood
  have hP : Tendsto P atTop (nhds x₀) :=
    hSK.congr' (hPS.mono fun n hn => hn.symm)
  obtain ⟨C, hC⟩ := hbound
  have hC0 : 0 ≤ C := (norm_nonneg (x 0)).trans (hC 0)
  have hPbound : ∀ n, ‖P n‖ ≤ C := by
    intro n
    rw [show P n = ∑ i : Fin (n + 1),
      (apm_m02J03_paddedCoeff a n i : ℂ) • x i.val by rfl]
    calc
      ‖∑ i : Fin (n + 1), (apm_m02J03_paddedCoeff a n i : ℂ) • x i.val‖ ≤
          ∑ i : Fin (n + 1),
            ‖(apm_m02J03_paddedCoeff a n i : ℂ) • x i.val‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin (n + 1), apm_m02J03_paddedCoeff a n i * C := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (apm_m02J03_paddedCoeff_nonneg a ha0 n i)]
        exact mul_le_mul_of_nonneg_left (hC i.val)
          (apm_m02J03_paddedCoeff_nonneg a ha0 n i)
      _ = C := by
        rw [← Finset.sum_mul, apm_m02J03_paddedCoeff_sum a ha1 n, one_mul]
  have hUbound : ∀ n, ‖U n‖ ≤ C := by
    intro n
    rw [show U n = ∑ i : Fin (n + 1),
      ((((1 : ℝ) / (n + 1 : ℕ)) : ℝ) : ℂ) • x i.val by rfl]
    calc
      ‖∑ i : Fin (n + 1), ((((1 : ℝ) / (n + 1 : ℕ)) : ℝ) : ℂ) • x i.val‖ ≤
          ∑ i : Fin (n + 1),
            ‖((((1 : ℝ) / (n + 1 : ℕ)) : ℝ) : ℂ) • x i.val‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin (n + 1), ((1 : ℝ) / (n + 1 : ℕ)) * C := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (n + 1 : ℕ))]
        exact mul_le_mul_of_nonneg_left (hC i.val) (by positivity)
      _ = C := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        field_simp
  let δ : ℕ → ℝ := fun n => 1 / (n + 2 : ℕ)
  let Q : ℕ → H := fun n => ∑ i : Fin (n + 1),
    (apm_m02J03_strictCoeff a n i : ℂ) • x i.val
  have hQ_formula : ∀ n, Q n =
      ((1 - δ n : ℝ) : ℂ) • P n + ((δ n : ℝ) : ℂ) • U n := by
    intro n
    simp only [Q, P, U, apm_m02J03_strictCoeff, δ]
    rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [smul_smul]
    congr 1
    push_cast
    module
  have hδ : Tendsto δ atTop (nhds 0) := by
    exact (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
      (tendsto_add_atTop_nat 2)
  have hδU : Tendsto (fun n => ((δ n : ℝ) : ℂ) • U n) atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (hδ.mul_const C)) ε hε
    refine ⟨N, fun n hn => ?_⟩
    have hn' := hN n hn
    have hδn : 0 ≤ δ n := by unfold δ; positivity
    have hn'' : δ n * C < ε := by
      simpa only [zero_mul, dist_zero_right, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg hδn, abs_of_nonneg hC0] using hn'
    rw [dist_zero_right, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hδn]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hUbound n)
      hδn) hn''
  have hOneSub : Tendsto (fun n => ((1 - δ n : ℝ) : ℂ)) atTop (nhds 1) := by
    have hr : Tendsto (fun n => 1 - δ n) atTop (nhds (1 : ℝ)) := by
      simpa using hδ.const_sub 1
    have hc := (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp hr
    convert hc using 1
  have hQ : Tendsto Q atTop (nhds x₀) := by
    have ht := (hOneSub.smul hP).add hδU
    simpa using ht.congr' (Filter.Eventually.of_forall fun n => (hQ_formula n).symm)
  exact hQ

/-- Why this unblocks the final conjunct of `apm_m02j03`: this is the
strictly-positive triangular form of Mazur's theorem. Unlike an ordinary
finite convex-hull witness, every coefficient on the full initial segment
`0,…,n` is positive while the resulting combinations converge strongly. -/
theorem apm_m02J03_bridge_2
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (x : ℕ → H) (x₀ : H)
    (hweak : ∀ y : H,
      Tendsto (fun n ↦ inner ℂ (x n) y) atTop (nhds (inner ℂ x₀ y))) :
    ∃ α : ∀ n : ℕ, Fin (n + 1) → ℝ,
      (∀ n : ℕ, (∀ i : Fin (n + 1), 0 < α n i) ∧ ∑ i, α n i = 1) ∧
      Tendsto (fun n ↦ ∑ i : Fin (n + 1), (α n i : ℂ) • x i.val)
        atTop (nhds x₀) := by
  obtain ⟨a, ha0, ha1, hconv⟩ :=
    apm_m02J03_exists_finsupp_approximating_sequence x x₀ hweak
  refine ⟨apm_m02J03_strictCoeff a, ?_, ?_⟩
  · exact fun n => apm_m02J03_strictCoeff_pos_sum a ha0 ha1 n
  · exact apm_m02J03_strictCoeff_tendsto x x₀ a ha0 ha1 hconv
      (apm_m02J03_bridge_1 x x₀ hweak)

theorem apm_m02j03
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (x : ℕ → H) (x₀ : H)
    (hweak : ∀ y : H,
      Tendsto (fun n ↦ inner ℂ (x n) y) atTop (nhds (inner ℂ x₀ y))) :
    (∃ C : ℝ, ∀ n : ℕ, ‖x n‖ ≤ C) ∧
    (Tendsto x atTop (nhds x₀) ↔
      Tendsto (fun n ↦ ‖x n‖) atTop (nhds ‖x₀‖)) ∧
    ∃ α : ∀ n : ℕ, Fin (n + 1) → ℝ,
      (∀ n : ℕ, (∀ i : Fin (n + 1), 0 < α n i) ∧ ∑ i, α n i = 1) ∧
      Tendsto (fun n ↦ ∑ i : Fin (n + 1), (α n i : ℂ) • x i.val)
        atTop (nhds x₀) := by
  refine ⟨apm_m02J03_bridge_1 x x₀ hweak, ?_,
    apm_m02J03_bridge_2 x x₀ hweak⟩
  constructor
  · exact apm_m02j03_norm_tendsto_of_tendsto
  · exact apm_m02j03_tendsto_of_weak_and_norm hweak
