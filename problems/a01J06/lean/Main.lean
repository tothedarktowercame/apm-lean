import Mathlib

/-!
# APM a01J06 — summability of zeros of an entire function of exponential type

## Statement repairs

The nonzero hypothesis `f ≠ 0` is made explicit. The identically zero function
satisfies the stated growth estimate but does not have a discrete sequence of
zeros with finite multiplicities, so the source's phrase “zeros listed with
appropriate multiplicity” implicitly excludes it.

The zero sequence is tied to `f` by requiring the finite fiber over every
point to have cardinality equal to Mathlib's analytic order of vanishing.
Thus neither the zero set nor its multiplicities are fabricated.
-/

open Complex

noncomputable section

def apm_a01J06_ExpTypeBound (f : ℂ → ℂ) (A B : ℝ) : Prop :=
  ∀ z : ℂ, ‖f z‖ ≤ B * Real.exp (A * ‖z‖)

def apm_a01J06_EnumeratesZeros (f : ℂ → ℂ) (ω : ℕ → ℂ) : Prop :=
  ∀ z : ℂ,
    Finite {n : ℕ // ω n = z} ∧
      Nat.card {n : ℕ // ω n = z} = analyticOrderNatAt f z

/-- The repaired fiber-cardinality encoding really does enumerate only zeros.
This is the first transport step needed to compare `ω` with the divisor in
Mathlib's Jensen formula. -/
lemma apm_a01J06_apply_eq_zero_of_enumeratesZeros
    {f : ℂ → ℂ} {ω : ℕ → ℂ}
    (hω : apm_a01J06_EnumeratesZeros f ω) (n : ℕ) :
    f (ω n) = 0 := by
  have hfinite := (hω (ω n)).1
  let i : {m : ℕ // ω m = ω n} := ⟨n, rfl⟩
  have hcard : 0 < Nat.card {m : ℕ // ω m = ω n} := by
    letI := Fintype.ofFinite {m : ℕ // ω m = ω n}
    letI : Nonempty {m : ℕ // ω m = ω n} := ⟨i⟩
    exact Nat.card_pos
  apply apply_eq_zero_of_analyticOrderNatAt_ne_zero
  rw [← (hω (ω n)).2]
  exact Nat.ne_of_gt hcard

/-- A multiplicity-preserving enumeration has only finitely many indices over
any finite set of values. This is the finite-union step needed to compare
ordinary disk counts with divisor mass. -/
lemma apm_a01J06_finite_preimage_of_enumeratesZeros
    {f : ℂ → ℂ} {ω : ℕ → ℂ}
    (hω : apm_a01J06_EnumeratesZeros f ω)
    {s : Set ℂ} (hs : s.Finite) :
    {n : ℕ | ω n ∈ s}.Finite := by
  have heq : {n : ℕ | ω n ∈ s} = ⋃ z ∈ s, {n : ℕ | ω n = z} := by
    ext n
    simp
  rw [heq]
  exact hs.biUnion fun z _ => Set.finite_coe_iff.mp (hω z).1

/-- On a finite set of values, the enumeration count is exactly the sum of
the analytic multiplicities. -/
lemma apm_a01J06_card_preimage_eq_finsum_analyticOrder
    {f : ℂ → ℂ} {ω : ℕ → ℂ}
    (hω : apm_a01J06_EnumeratesZeros f ω)
    {s : Set ℂ} (hs : s.Finite) :
    Nat.card {n : ℕ // ω n ∈ s} =
      ∑ᶠ z ∈ s, analyticOrderNatAt f z := by
  have heq : {n : ℕ | ω n ∈ s} = ⋃ z ∈ s, {n : ℕ | ω n = z} := by
    ext n
    simp
  change {n : ℕ | ω n ∈ s}.ncard = _
  rw [heq]
  have hc : (⋃ z ∈ s, {n : ℕ | ω n = z}).ncard =
      ∑ᶠ z ∈ s, ({n : ℕ | ω n = z}).ncard := hs.ncard_biUnion
    (fun z _ => Set.finite_coe_iff.mp (hω z).1) (by
      intro z hz w hw hne
      dsimp only [Function.onFun]
      rw [Set.disjoint_left]
      intro n hnz hnw
      exact hne (hnz.symm.trans hnw))
  rw [hc]
  apply finsum_mem_congr rfl
  intro z hz
  simpa only [Nat.card_coe_set_eq] using (hω z).2

/-- An entire nonzero function has only finitely many enumerated zeros in
each closed disk.  This connects the fiber-cardinality invariant in
`apm_a01J06_EnumeratesZeros` to Mathlib's locally finite meromorphic divisor. -/
lemma apm_a01J06_finite_closedDisk_indices
    {f : ℂ → ℂ} {ω : ℕ → ℂ}
    (hf_entire : Differentiable ℂ f) (hf_nonzero : f ≠ 0)
    (hω : apm_a01J06_EnumeratesZeros f ω) (R : ℝ) :
    Set.Finite {n : ℕ | ‖ω n‖ ≤ R} := by
  have han : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) := by
    intro z hz
    exact hf_entire.analyticAt z
  have hmer : MeromorphicOn f (Set.univ : Set ℂ) := han.meromorphicOn
  obtain ⟨z, hz⟩ : ∃ z : ℂ, f z ≠ 0 := by
    simpa only [not_forall, Classical.not_not] using
      (Function.ne_iff.mp hf_nonzero)
  have hzorder : meromorphicOrderAt f z ≠ ⊤ := by
    have hz0 : meromorphicOrderAt f z = 0 :=
      (han z (Set.mem_univ z)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hz
    simp [hz0]
  have hord : ∀ u : (Set.univ : Set ℂ), meromorphicOrderAt f u ≠ ⊤ :=
    (hmer.exists_meromorphicOrderAt_ne_top_iff_forall
      (isConnected_univ : IsConnected (Set.univ : Set ℂ))).1
      ⟨⟨z, Set.mem_univ z⟩, hzorder⟩
  let D := MeromorphicOn.divisor f (Set.univ : Set ℂ)
  have hzeros : (Set.univ : Set ℂ) ∩ f ⁻¹' {0} = D.support :=
    han.meromorphicNFOn.zero_set_eq_divisor_support hord
  let s : Set ℂ := Metric.closedBall 0 R ∩ f ⁻¹' {0}
  have hs : s.Finite := by
    have hD : LocallyFiniteSupport (D : ℂ → ℤ) :=
      Function.locallyFinsupp.locallyFiniteSupport D
    have hfin := hD.finite_inter_support_of_isCompact
      (isCompact_closedBall (0 : ℂ) R)
    simpa [s, ← hzeros] using hfin
  have heq : {n : ℕ | ‖ω n‖ ≤ R} = {n : ℕ | ω n ∈ s} := by
    ext n
    simp only [Set.mem_setOf_eq, s, Set.mem_inter_iff, Metric.mem_closedBall,
      dist_zero_right, Set.mem_preimage, Set.mem_singleton_iff]
    exact (and_iff_left (apm_a01J06_apply_eq_zero_of_enumeratesZeros hω n)).symm
  rw [heq]
  exact apm_a01J06_finite_preimage_of_enumeratesZeros hω hs


/-! ## Contract 1: the linear zero-count via log-counting -/

/-- The ordinary zero-counting function attached to an enumeration. -/
def apm_a01J06_zeroCount (ω : ℕ → ℂ) (R : ℝ) : ℕ :=
  {n : ℕ | ‖ω n‖ ≤ R}.ncard

lemma apm_a01J06_zeroCount_eq_card
    {ω : ℕ → ℂ} (R : ℝ) :
    apm_a01J06_zeroCount ω R = Nat.card {n : ℕ // ‖ω n‖ ≤ R} :=
  (Nat.card_coe_set_eq {n : ℕ | ‖ω n‖ ≤ R}).symm

/-- For a nonzero entire function, Mathlib's meromorphic divisor agrees
pointwise with the natural analytic order of vanishing. -/
lemma apm_a01J06_divisor_eq_analyticOrderNatAt
    {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f) (hf_nonzero : f ≠ 0)
    (z : ℂ) :
    MeromorphicOn.divisor f (Set.univ : Set ℂ) z =
      (analyticOrderNatAt f z : ℤ) := by
  have han : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) := fun w _ ↦ hf_entire.analyticAt w
  have hmer : MeromorphicOn f (Set.univ : Set ℂ) := han.meromorphicOn
  obtain ⟨w, hw⟩ : ∃ w : ℂ, f w ≠ 0 := by
    simpa only [not_forall, Classical.not_not] using Function.ne_iff.mp hf_nonzero
  have hworder : meromorphicOrderAt f w ≠ ⊤ := by
    rw [(han w (Set.mem_univ w)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hw]
    simp
  have hzorder : meromorphicOrderAt f z ≠ ⊤ :=
    (hmer.exists_meromorphicOrderAt_ne_top_iff_forall
      (isConnected_univ : IsConnected (Set.univ : Set ℂ))).1
      ⟨⟨w, Set.mem_univ w⟩, hworder⟩ ⟨z, Set.mem_univ z⟩
  rw [MeromorphicOn.divisor_apply hmer (Set.mem_univ z),
    (han z (Set.mem_univ z)).meromorphicOrderAt_eq]
  rw [← Nat.cast_analyticOrderNatAt]
  · simp
  · simpa [(han z (Set.mem_univ z)).meromorphicOrderAt_eq] using hzorder

/-- Consequently, the divisor of a nonzero entire function is nonnegative. -/
lemma apm_a01J06_divisor_nonneg
    {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f) (hf_nonzero : f ≠ 0) :
    0 ≤ MeromorphicOn.divisor f (Set.univ : Set ℂ) := by
  intro z
  change (0 : ℤ) ≤ MeromorphicOn.divisor f (Set.univ : Set ℂ) z
  rw [apm_a01J06_divisor_eq_analyticOrderNatAt hf_entire hf_nonzero]
  exact Int.natCast_nonneg _

/-- Entire functions have no pole-counting contribution. -/
lemma apm_a01J06_logCounting_top_eq_zero
    {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f) (hf_nonzero : f ≠ 0) :
    ValueDistribution.logCounting f ⊤ = 0 := by
  rw [ValueDistribution.logCounting_top]
  have hD := apm_a01J06_divisor_nonneg hf_entire hf_nonzero
  rw [negPart_eq_zero.mpr hD]
  simp

/-- For an entire nonzero function, zero log-counting uses the divisor
itself rather than an additional positive-part wrapper. -/
lemma apm_a01J06_logCounting_zero_eq_divisor_logCounting
    {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f) (hf_nonzero : f ≠ 0) :
    ValueDistribution.logCounting f 0 =
      Function.locallyFinsuppWithin.logCounting
        (MeromorphicOn.divisor f (Set.univ : Set ℂ)) := by
  rw [ValueDistribution.logCounting_zero,
    posPart_eq_self.mpr (apm_a01J06_divisor_nonneg hf_entire hf_nonzero)]

/-- The exponential-type estimate gives a linear upper bound for the
Nevanlinna proximity term. -/
lemma apm_a01J06_proximity_top_le
    {f : ℂ → ℂ} {A B R : ℝ}
    (hf_entire : Differentiable ℂ f) (hA : 0 ≤ A)
    (hR : 0 ≤ R) (hf_bound : apm_a01J06_ExpTypeBound f A B) :
    ValueDistribution.proximity f ⊤ R ≤ Real.posLog B + A * R := by
  rw [ValueDistribution.proximity_top]
  calc
    Real.circleAverage (fun z ↦ Real.posLog ‖f z‖) 0 R ≤
        Real.circleAverage (fun _ : ℂ ↦ Real.posLog B + A * R) 0 R := by
      apply Real.circleAverage_mono
      · have han : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) :=
          fun z _ ↦ hf_entire.analyticAt z
        exact circleIntegrable_posLog_norm_meromorphicOn
          (fun z _ ↦ han.meromorphicOn z (Set.mem_univ z))
      · exact circleIntegrable_const _ _ _
      · intro z hz
        have hnorm : ‖z‖ = R := by
          simpa [Metric.mem_sphere, abs_of_nonneg hR] using hz
        calc
          Real.posLog ‖f z‖ ≤ Real.posLog (B * Real.exp (A * ‖z‖)) :=
            Real.posLog_le_posLog (norm_nonneg _) (hf_bound z)
          _ ≤ Real.posLog B + Real.posLog (Real.exp (A * ‖z‖)) := Real.posLog_mul
          _ = Real.posLog B + A * R := by
            rw [hnorm]
            simp [Real.posLog, Real.log_exp, mul_nonneg hA hR]
    _ = Real.posLog B + A * R := Real.circleAverage_const _ _ _

/-- Jensen's first main theorem and the growth bound give a linear-plus-
constant upper bound for logarithmic zero counting. -/
lemma apm_a01J06_logCounting_zero_le_linear_add_const
    {f : ℂ → ℂ} {A B R : ℝ}
    (hf_entire : Differentiable ℂ f) (hf_nonzero : f ≠ 0)
    (hA : 0 ≤ A) (hR : 1 ≤ R)
    (hf_bound : apm_a01J06_ExpTypeBound f A B) :
    ValueDistribution.logCounting f 0 R ≤ Real.posLog B + A * R +
      |Real.log ‖meromorphicTrailingCoeffAt f 0‖| := by
  have hmer : Meromorphic f := fun x ↦ (hf_entire.analyticAt x).meromorphicAt
  have hRpos : R ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hR)
  have hFMT := ValueDistribution.characteristic_sub_characteristic_inv_of_ne_zero
    hmer hRpos
  have hchar : ValueDistribution.characteristic f ⊤ R
      = ValueDistribution.proximity f ⊤ R := by
    have htop := apm_a01J06_logCounting_top_eq_zero hf_entire hf_nonzero
    simp [ValueDistribution.characteristic, htop]
  have hstep : ValueDistribution.characteristic f⁻¹ ⊤ R
      = ValueDistribution.characteristic f ⊤ R
        - Real.log ‖meromorphicTrailingCoeffAt f 0‖ := by linarith
  have hinvle : ValueDistribution.logCounting f 0 R
      ≤ ValueDistribution.characteristic f⁻¹ ⊤ R := by
    rw [ValueDistribution.characteristic, ValueDistribution.logCounting_inv]
    exact le_add_of_nonneg_left (ValueDistribution.proximity_nonneg R)
  rw [hstep] at hinvle
  rw [hchar] at hinvle
  have hprox := apm_a01J06_proximity_top_le hf_entire hA
    (le_of_lt (lt_of_lt_of_le zero_lt_one hR)) hf_bound
  have habs := abs_nonneg (Real.log ‖meromorphicTrailingCoeffAt f 0‖)
  have hLab := neg_le_abs (Real.log ‖meromorphicTrailingCoeffAt f 0‖)
  linarith

/-- Each point of the `R`-disk contributes weight at least `log 2` to the
log-counting function evaluated at radius `2 * R`. -/
lemma apm_a01J06_log_two_le_log_two_mul_sub_log_norm {z : ℂ} {R : ℝ}
    (hR : 1 ≤ R) (hz : ‖z‖ ≤ R) :
    Real.log 2 ≤ Real.log (2 * R) - Real.log ‖z‖ := by
  by_cases hz0 : z = 0
  · subst hz0
    have h0 : ‖(0 : ℂ)‖ = 0 := by simp
    have hRpos : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
    have hlogR : Real.log 2 ≤ Real.log (2 * R) := by
      apply Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      nlinarith
    rw [h0, Real.log_zero, sub_zero]
    exact hlogR
  · have hnz : ‖z‖ ≠ 0 := by simpa using hz0
    have hpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnz)
    have hRpos : (0 : ℝ) < R := lt_of_lt_of_le hpos hz
    have h2R : (0 : ℝ) < 2 * R := by nlinarith
    have hsplit : Real.log 2 + Real.log ‖z‖ = Real.log (2 * ‖z‖) := by
      rw [Real.log_mul (by norm_num) hnz]
    have hkey : Real.log 2 + Real.log ‖z‖ ≤ Real.log (2 * R) := by
      rw [hsplit]
      apply Real.log_le_log (by nlinarith)
      exact mul_le_mul_of_nonneg_left hz (by norm_num)
    have hlogz : Real.log ‖z‖ = Real.log ‖z‖ := rfl
    linarith

/-- The zero-count is bounded below in terms of logarithmic zero counting:
each counted zero contributes weight `log 2` at twice the radius. -/
lemma apm_a01J06_zeroCount_mul_log_two_le_logCounting
    {f : ℂ → ℂ} {ω : ℕ → ℂ} {R : ℝ}
    (hf_entire : Differentiable ℂ f) (hf_nonzero : f ≠ 0)
    (hω : apm_a01J06_EnumeratesZeros f ω) (hR : 1 ≤ R) :
    (Nat.card {n : ℕ // ‖ω n‖ ≤ R} : ℝ) * Real.log 2 ≤
      ValueDistribution.logCounting f 0 (2 * R) := by
  classical
  set D := MeromorphicOn.divisor f (Set.univ : Set ℂ) with hDdef
  set s : Set ℂ := Metric.closedBall (0 : ℂ) R ∩ f ⁻¹' {0} with hsdef
  have hfin : s.Finite := by
    have han : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) := fun z _ ↦ hf_entire.analyticAt z
    have hmer : MeromorphicOn f (Set.univ : Set ℂ) := han.meromorphicOn
    obtain ⟨z, hz⟩ : ∃ z : ℂ, f z ≠ 0 := by
      simpa only [not_forall, Classical.not_not] using Function.ne_iff.mp hf_nonzero
    have hzorder : meromorphicOrderAt f z ≠ ⊤ := by
      rw [(han z (Set.mem_univ z)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hz]
      simp
    have hord : ∀ u : (Set.univ : Set ℂ), meromorphicOrderAt f u ≠ ⊤ :=
      (hmer.exists_meromorphicOrderAt_ne_top_iff_forall
        (isConnected_univ : IsConnected (Set.univ : Set ℂ))).1
        ⟨⟨z, Set.mem_univ z⟩, hzorder⟩
    have hzeros : (Set.univ : Set ℂ) ∩ f ⁻¹' {0} = D.support :=
      han.meromorphicNFOn.zero_set_eq_divisor_support hord
    have hlf : LocallyFiniteSupport (D : ℂ → ℤ) :=
      Function.locallyFinsupp.locallyFiniteSupport D
    have hfin2 := hlf.finite_inter_support_of_isCompact
      (isCompact_closedBall (0 : ℂ) R)
    simpa [s, ← hzeros] using hfin2
  set t := hfin.toFinset with htdef
  have hsmem : ∀ z ∈ t, ‖z‖ ≤ R ∧ f z = 0 := by
    intro z hz
    have := hfin.mem_toFinset.1 hz
    simpa [s, Metric.mem_closedBall, dist_zero_right, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_singleton_iff] using this
  -- the count equals the sum of analytic multiplicities over the disk
  have hcounteq : (Nat.card {n : ℕ // ‖ω n‖ ≤ R} : ℝ)
      = ∑ z ∈ t, (analyticOrderNatAt f z : ℝ) := by
    have heq : {n : ℕ | ‖ω n‖ ≤ R} = {n : ℕ | ω n ∈ s} := by
      ext n
      simp only [Set.mem_setOf_eq, s, Set.mem_inter_iff, Metric.mem_closedBall,
        dist_zero_right, Set.mem_preimage, Set.mem_singleton_iff]
      exact (and_iff_left (apm_a01J06_apply_eq_zero_of_enumeratesZeros hω n)).symm
    have key := apm_a01J06_card_preimage_eq_finsum_analyticOrder hω hfin
    have h4 : (∑ᶠ z ∈ s, analyticOrderNatAt f z : ℕ) = ∑ z ∈ t, analyticOrderNatAt f z :=
      finsum_mem_eq_finite_toFinset_sum _ hfin
    have h5 : (∑ z ∈ t, analyticOrderNatAt f z : ℕ) = ∑ z ∈ t, (analyticOrderNatAt f z : ℝ) := by
      push_cast
      rfl
    have e2 : Nat.card {n : ℕ // ‖ω n‖ ≤ R} = Nat.card {n : ℕ // ω n ∈ s} :=
      Nat.card_congr
        ⟨fun ⟨n, hn⟩ ↦ ⟨n, heq.subset (Set.mem_setOf_eq.mpr hn)⟩,
         fun ⟨n, hn⟩ ↦ ⟨n, heq.symm.subset (Set.mem_setOf_eq.mpr hn)⟩,
         fun _ ↦ rfl, fun _ ↦ rfl⟩
    rw [e2, key, h4]
    exact_mod_cast h5
  -- the finsum of singles is a pointwise lower bound of the divisor
  set D₁ : Function.locallyFinsupp ℂ ℤ :=
    ∑ z ∈ t, Function.locallyFinsuppWithin.single z (D z) with hD₁def
  have hval : ∀ w : ℂ, D₁ w = if w ∈ t then D w else 0 := by
    intro w
    have hcoe : D₁ w = ∑ z ∈ t, (Function.locallyFinsuppWithin.single z (D z) w) := by
      rw [hD₁def]
      induction t using Finset.induction with
      | empty => simp
      | insert x s hx ih =>
          rw [Finset.sum_insert hx, Finset.sum_insert hx]
          simp only [Function.locallyFinsuppWithin.coe_add, Pi.add_apply]
          rw [ih]
    by_cases hwt : w ∈ t
    · rw [hcoe, if_pos hwt]
      rw [Finset.sum_eq_single w (fun b _ hb ↦ by
          rw [Function.locallyFinsuppWithin.single_apply]
          split
          · next hh => exact absurd hh.symm hb
          · rfl) (by simp [hwt])]
      simp [Function.locallyFinsuppWithin.single_apply]
    · rw [hcoe, if_neg hwt]
      refine Finset.sum_eq_zero fun z hz ↦ ?_
      have hwz : ¬(w = z) := fun h ↦ hwt (h ▸ hz)
      simp [Function.locallyFinsuppWithin.single_apply, hwz]
  have hmono : D₁ ≤ D := by
    rw [Function.locallyFinsuppWithin.le_def]
    intro w
    rw [hval w]
    by_cases hwt : w ∈ t
    · rw [if_pos hwt]
    · rw [if_neg hwt]
      exact apm_a01J06_divisor_nonneg hf_entire hf_nonzero w
  -- transport to logCounting
  have h12 : (1 : ℝ) ≤ 2 * R := by linarith
  have hle := Function.locallyFinsuppWithin.logCounting_le (f₁ := D₁) (f₂ := D) hmono h12
  have hzero : ValueDistribution.logCounting f 0 (2 * R)
      = Function.locallyFinsuppWithin.logCounting D (2 * R) := by
    rw [apm_a01J06_logCounting_zero_eq_divisor_logCounting hf_entire hf_nonzero]
  -- evaluate the finsum side
  have hmap : Function.locallyFinsuppWithin.logCounting D₁ (2 * R)
      = ∑ z ∈ t, (D z : ℝ) * (Real.log (2 * R) - Real.log ‖z‖) := by
    have hcoe : D₁ = ∑ z ∈ t, Function.locallyFinsuppWithin.single z (D z) := rfl
    rw [hcoe, map_sum]
    simp only [Finset.sum_apply]
    refine Finset.sum_congr rfl fun z hz ↦ ?_
    have hzR : ‖z‖ ≤ 2 * R := ((hsmem z hz).1).trans (by linarith)
    rw [Function.locallyFinsuppWithin.logCounting_single_eq_log_sub_const hzR]
  -- each multiplicity contributes at least log 2
  have hterm : ∀ z ∈ t, (analyticOrderNatAt f z : ℝ) * Real.log 2
      ≤ (D z : ℝ) * (Real.log (2 * R) - Real.log ‖z‖) := by
    intro z hz
    have hzR : ‖z‖ ≤ R := (hsmem z hz).1
    have hDz : (D z : ℝ) = (analyticOrderNatAt f z : ℝ) := by
      rw [apm_a01J06_divisor_eq_analyticOrderNatAt hf_entire hf_nonzero z]
      push_cast
      rfl
    rw [hDz]
    have hlog2 := apm_a01J06_log_two_le_log_two_mul_sub_log_norm hR hzR
    have hn : (0 : ℝ) ≤ (analyticOrderNatAt f z : ℝ) := by
      have := Nat.zero_le (analyticOrderNatAt f z)
      exact_mod_cast this
    nlinarith
  -- chain the inequalities
  calc (Nat.card {n : ℕ // ‖ω n‖ ≤ R} : ℝ) * Real.log 2
      = (∑ z ∈ t, (analyticOrderNatAt f z : ℝ)) * Real.log 2 := by rw [hcounteq]
    _ = ∑ z ∈ t, (analyticOrderNatAt f z : ℝ) * Real.log 2 := Finset.sum_mul _ _ _
    _ ≤ ∑ z ∈ t, (D z : ℝ) * (Real.log (2 * R) - Real.log ‖z‖) :=
        Finset.sum_le_sum hterm
    _ = Function.locallyFinsuppWithin.logCounting D₁ (2 * R) := hmap.symm
    _ ≤ Function.locallyFinsuppWithin.logCounting D (2 * R) := hle
    _ = ValueDistribution.logCounting f 0 (2 * R) := hzero.symm

/-- Every real number `≥ 1` lies in a unique dyadic shell. -/
lemma apm_a01J06_existsUnique_dyadic (t : ℝ) (ht : 1 ≤ t) :
    ∃! k : ℕ, (2 : ℝ) ^ (k : ℕ) ≤ t ∧ t < (2 : ℝ) ^ ((k : ℕ) + 1) := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have ht1 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  set u : ℝ := Real.log t / Real.log 2 with hu
  have htu : (0 : ℝ) ≤ u := div_nonneg (Real.log_nonneg ht) h2.le
  have hnn : 0 ≤ Int.floor u := Int.floor_nonneg.2 htu
  have h1 : ((Int.floor u).toNat : ℤ) = Int.floor u := Int.toNat_of_nonneg hnn
  have hfloor1 : ((Int.floor u).toNat : ℝ) ≤ u := by
    have h3 : ((Int.floor u : ℤ) : ℝ) = ((Int.floor u).toNat : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg hnn).symm
    have h4 : ((Int.floor u : ℤ) : ℝ) ≤ u := Int.floor_le u
    rw [← h3]; exact h4
  have hfloor2 : u < ((Int.floor u).toNat : ℝ) + 1 := by
    have h3 : ((Int.floor u : ℤ) : ℝ) = ((Int.floor u).toNat : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg hnn).symm
    have h5 : u < ((Int.floor u : ℤ) : ℝ) + 1 := by
      have := Int.lt_floor_add_one u
      push_cast at this
      linarith [Int.floor_le u]
    rw [← h3]; linarith
  have hmul : u * Real.log 2 = Real.log t := by rw [hu]; field_simp
  have hlower' : Real.log ((2 : ℝ) ^ ((Int.floor u).toNat : ℕ)) ≤ Real.log t := by
    rw [Real.log_pow 2]
    have h5 : ((Int.floor u).toNat : ℝ) * Real.log 2 ≤ u * Real.log 2 :=
      mul_le_mul_of_nonneg_right hfloor1 h2.le
    linarith
  have hupper : Real.log t < Real.log ((2 : ℝ) ^ ((Int.floor u).toNat + 1)) := by
    rw [Real.log_pow 2]
    have h5 : u * Real.log 2 < (((Int.floor u).toNat : ℝ) + 1) * Real.log 2 :=
      mul_lt_mul_of_pos_right hfloor2 h2
    push_cast
    linarith
  have hlowd : (2 : ℝ) ^ ((Int.floor u).toNat : ℕ) ≤ t :=
    (Real.log_le_log_iff (pow_pos (by norm_num) _) ht1).mp hlower'
  have hupd : t < (2 : ℝ) ^ ((Int.floor u).toNat + 1) :=
    (Real.log_lt_log_iff ht1 (pow_pos (by norm_num) _)).mp hupper
  refine ⟨(Int.floor u).toNat, ⟨hlowd, hupd⟩, ?_⟩
  intro j ⟨hj1, hj2⟩
  have hjlog1 : (j : ℝ) * Real.log 2 ≤ Real.log t := by
    have h : Real.log ((2 : ℝ) ^ j) ≤ Real.log t :=
      (Real.log_le_log_iff (x := (2 : ℝ) ^ j) (y := t) (by norm_num) ht1).mpr hj1
    rw [Real.log_pow 2] at h
    exact h
  have hjlog2 : Real.log t < ((j : ℝ) + 1) * Real.log 2 := by
    have h : Real.log t < Real.log ((2 : ℝ) ^ (j + 1)) :=
      (Real.log_lt_log_iff (x := t) (y := (2 : ℝ) ^ (j + 1)) ht1 (by norm_num)).mpr hj2
    rw [Real.log_pow 2, Nat.cast_add, Nat.cast_one] at h
    exact h
  have hju1 : (j : ℝ) ≤ u := by nlinarith
  have hju2 : u < (j : ℝ) + 1 := by nlinarith
  have hjeq : (j : ℤ) = ((Int.floor u).toNat : ℤ) := by
    have hle1 : (j : ℤ) ≤ Int.floor u := Int.le_floor.2 hju1
    have hle2 : Int.floor u ≤ (j : ℤ) := by
      by_contra hcon
      have hjlt : (j : ℤ) + 1 ≤ Int.floor u := by omega
      have hjlt' : ((j : ℤ) + 1 : ℝ) ≤ ((Int.floor u : ℤ) : ℝ) := by exact_mod_cast hjlt
      have hfl : ((Int.floor u : ℤ) : ℝ) ≤ u := Int.floor_le u
      have hcast : ((j : ℤ) + 1 : ℝ) = ((j : ℝ) : ℝ) + 1 := by push_cast; ring
      rw [hcast] at hjlt'
      linarith
    omega
  exact_mod_cast hjeq


/-- The quantitative Jensen step: an entire function of exponential type has
a linearly growing zero count. -/
theorem apm_a01J06_linear_zero_count
    (f : ℂ → ℂ) (omega : ℕ → ℂ) (A B : ℝ)
    (hf_entire : Differentiable ℂ f)
    (hf_nonzero : f ≠ 0)
    (hA : 0 < A)
    (hB : 0 < B)
    (hf_bound : apm_a01J06_ExpTypeBound f A B)
    (homega : apm_a01J06_EnumeratesZeros f omega) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
      Finite {n : ℕ // ‖omega n‖ ≤ R} ∧
      ((Nat.card {n : ℕ // ‖omega n‖ ≤ R} : ℝ) ≤ C * R) := by
  classical
  set P : ℝ := Real.posLog B + |Real.log ‖meromorphicTrailingCoeffAt f 0‖| with hP
  have hPnn : (0 : ℝ) ≤ P := by
    have := Real.posLog_nonneg (x := B)
    have := abs_nonneg (Real.log ‖meromorphicTrailingCoeffAt f 0‖)
    linarith
  refine ⟨(P + 2 * A) / Real.log 2, ?_, ?_⟩
  · exact div_nonneg (by linarith) ((Real.log_pos (show (1 : ℝ) < 2 by norm_num)).le)
  · intro R hR
    have hfinset : Set.Finite {n : ℕ | ‖omega n‖ ≤ R} :=
      apm_a01J06_finite_closedDisk_indices hf_entire hf_nonzero homega R
    have hsub : Finite {n : ℕ // ‖omega n‖ ≤ R} := Set.finite_coe_iff.mp hfinset
    refine ⟨hsub, ?_⟩
    have hG := apm_a01J06_zeroCount_mul_log_two_le_logCounting hf_entire hf_nonzero
      homega hR
    have hE := apm_a01J06_logCounting_zero_le_linear_add_const hf_entire hf_nonzero
      hA.le (by linarith : (1 : ℝ) ≤ 2 * R) hf_bound
    have key := hG.trans hE
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hdiv : (Nat.card {n : ℕ // ‖omega n‖ ≤ R} : ℝ) ≤ (P + 2 * A * R) / Real.log 2 :=
      (le_div_iff₀ hlog2).mpr (by linarith)
    have hC : (P + 2 * A * R) / Real.log 2 ≤ ((P + 2 * A) / Real.log 2) * R := by
      have e : ((P + 2 * A) / Real.log 2) * R = (P + 2 * A) * R / Real.log 2 := by ring
      rw [e, div_le_div_iff₀ hlog2 hlog2]
      have hPR : (0 : ℝ) ≤ P * (R - 1) := mul_nonneg hPnn (by linarith)
      nlinarith
    exact hdiv.trans hC

/-! ## Contract 2: dyadic-shell summability -/

/-- `2^(1-α) < 1` exactly when `α > 1`. -/
lemma apm_a01J06_rpow_two_one_sub_lt_one {α : ℝ} (hα : 1 < α) :
    Real.rpow 2 (1 - α) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hα)

/-- The shell majorant `(C·2^(k+1))·(2^k)^(-α)` is the geometric term
`(2C)·(2^(1-α))^k`. -/
lemma apm_a01J06_shell_majorant_eq_geometric (C α : ℝ) (k : ℕ) :
    (C * (2 : ℝ) ^ (k + 1)) * Real.rpow ((2 : ℝ) ^ k) (-α) =
      (2 * C) * (Real.rpow 2 (1 - α)) ^ k := by
  have hpow : (2 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [pow_succ, Real.rpow_eq_pow, Real.rpow_eq_pow,
    Real.rpow_def_of_pos (pow_pos (by norm_num) k),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.log_pow, ← Real.exp_nat_mul, hpow]
  calc
    _ = (2 * C) * (Real.exp ((k : ℝ) * Real.log 2) *
        Real.exp (-((k : ℝ) * Real.log 2 * α))) := by ring_nf
    _ = (2 * C) * Real.exp ((k : ℝ) * Real.log 2 + -((k : ℝ) * Real.log 2 * α)) := by
          rw [Real.exp_add]
    _ = _ := by congr 2; ring_nf

lemma apm_a01J06_summable_shell_majorant (C : ℝ) {α : ℝ} (hα : 1 < α) :
    Summable (fun k : ℕ ↦ (C * (2 : ℝ) ^ (k + 1)) * Real.rpow ((2 : ℝ) ^ k) (-α)) := by
  have hg : Summable (fun k : ℕ ↦ (Real.rpow 2 (1 - α)) ^ k) :=
    summable_geometric_of_lt_one (Real.rpow_pos_of_pos (by norm_num) _).le
      (apm_a01J06_rpow_two_one_sub_lt_one hα)
  have hEq : (fun k : ℕ ↦ (C * (2 : ℝ) ^ (k + 1)) * Real.rpow ((2 : ℝ) ^ k) (-α))
      = fun k ↦ (2 * C) * (Real.rpow 2 (1 - α)) ^ k :=
    funext fun k ↦ apm_a01J06_shell_majorant_eq_geometric C α k
  rw [hEq]
  exact hg.mul_left (2 * C)

/-- The dyadic comparison: a linearly bounded count implies summability of
the `rpow` series for `α > 1`. -/
theorem apm_a01J06_summable_of_linear_count
    (omega : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ R : ℝ, 1 ≤ R → Finite {n : ℕ // ‖omega n‖ ≤ R} ∧
      ((Nat.card {n : ℕ // ‖omega n‖ ≤ R} : ℝ) ≤ C * R))
    (α : ℝ) (hα : 1 < α) :
    Summable (fun n : ℕ ↦ Real.rpow (1 + ‖omega n‖) (-α)) := by
  classical
  set f : ℕ → ℝ := fun n ↦ Real.rpow (1 + ‖omega n‖) (-α) with hfdef
  have hf0 : 0 ≤ f := fun n ↦ Real.rpow_nonneg (by positivity) _
  set s : ℕ → Set ℕ := fun k ↦ {n : ℕ | (2 : ℝ) ^ k ≤ 1 + ‖omega n‖
    ∧ 1 + ‖omega n‖ < (2 : ℝ) ^ (k + 1)} with hsdef
  have hs : ∀ i, ∃! j, i ∈ s j := by
    intro i
    obtain ⟨k, hk⟩ := apm_a01J06_existsUnique_dyadic (1 + ‖omega i‖)
      (by linarith [norm_nonneg (omega i)])
    exact ⟨k, hk.1, fun j hj => hk.2 j hj⟩
  have hRpow : ∀ (k : ℕ), (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih => rw [pow_succ]; linarith
  have hsub : ∀ (k : ℕ) (n : ℕ), n ∈ s k → ‖omega n‖ ≤ (2 : ℝ) ^ (k + 1) := by
    intro k n hn
    simp only [hsdef, Set.mem_setOf_eq] at hn
    have hnn := norm_nonneg (omega n)
    linarith
  have hfs : ∀ k, (s k).Finite := by
    intro k
    have hfin : {n : ℕ | ‖omega n‖ ≤ (2 : ℝ) ^ (k + 1)}.Finite :=
      Set.finite_coe_iff.mp ((hcount _ (hRpow k)).1)
    exact hfin.subset (fun n hn ↦ hsub k n hn)
  have hle : ∀ (k : ℕ) (n : ℕ), n ∈ s k →
      (1 + ‖omega n‖) ^ (-α) ≤ ((2 : ℝ) ^ k) ^ (-α) := by
    intro k n hn
    simp only [hsdef, Set.mem_setOf_eq] at hn
    have h1 : (0 : ℝ) < 1 + ‖omega n‖ := by positivity
    have h2 : (0 : ℝ) < (2 : ℝ) ^ k := pow_pos (by norm_num) k
    have hmono : ((2 : ℝ) ^ k) ^ α ≤ (1 + ‖omega n‖) ^ α :=
      Real.rpow_le_rpow h2.le hn.1 (by linarith)
    rw [Real.rpow_neg h1.le α, Real.rpow_neg h2.le α]
    exact (inv_le_inv₀ (Real.rpow_pos_of_pos h1 _) (Real.rpow_pos_of_pos h2 _)).mpr hmono
  have hcard : ∀ k, ((s k).ncard : ℝ) ≤ C * (2 : ℝ) ^ (k + 1) := by
    intro k
    have h2' := (hcount _ (hRpow k)).2
    have hB : (({n : ℕ | ‖omega n‖ ≤ (2 : ℝ) ^ (k + 1)}).ncard : ℝ)
        = (Nat.card {n : ℕ // ‖omega n‖ ≤ (2 : ℝ) ^ (k + 1)} : ℝ) := by
      exact_mod_cast (Nat.card_coe_set_eq
        {n : ℕ | ‖omega n‖ ≤ (2 : ℝ) ^ (k + 1)}).symm
    rw [← hB] at h2'
    have h1 : ((s k).ncard : ℝ)
        ≤ (({n : ℕ | ‖omega n‖ ≤ (2 : ℝ) ^ (k + 1)}).ncard : ℝ) := by
      exact_mod_cast Set.ncard_le_ncard
        (ht := Set.finite_coe_iff.mp (hcount _ (hRpow k)).1)
        (fun n hn ↦ hsub k n hn)
    exact h1.trans h2'
  have hMnonneg : ∀ k, (0 : ℝ) ≤ Real.rpow ((2 : ℝ) ^ k) (-α) :=
    fun k ↦ Real.rpow_nonneg (pow_nonneg (by norm_num) k) _
  rw [summable_partition hf0 hs]
  refine ⟨fun k ↦ ?_, ?_⟩
  · classical
    haveI : Finite ↥(s k) := hfs k
    haveI : Fintype ↥(s k) := Fintype.ofFinite _
    exact (hasSum_fintype _).summable
  · refine (apm_a01J06_summable_shell_majorant C hα).of_nonneg_of_le
      (fun k ↦ tsum_nonneg fun i ↦ hf0 i) ?_
    intro k
    classical
    haveI : Finite ↥(s k) := hfs k
    haveI : Fintype ↥(s k) := Fintype.ofFinite _
    have htsum : ∑' i : ↥(s k), f ↑i = ∑ i : ↥(s k), f ↑i :=
      tsum_fintype (fun i : ↥(s k) ↦ f ↑i)
    have hbound : ∑ i : ↥(s k), f ↑i
        ≤ ((s k).ncard : ℝ) * Real.rpow ((2 : ℝ) ^ k) (-α) := by
      have hstep : ∑ i : ↥(s k), f ↑i
          ≤ ∑ _i : ↥(s k), Real.rpow ((2 : ℝ) ^ k) (-α) :=
        Finset.sum_le_sum fun i _ ↦ (hle k _ i.2 :
          (1 + ‖omega ↑i‖) ^ (-α) ≤ ((2 : ℝ) ^ k) ^ (-α))
      have hcard' : (∑ _i : ↥(s k), Real.rpow ((2 : ℝ) ^ k) (-α))
          = (Fintype.card ↥(s k) : ℝ) * Real.rpow ((2 : ℝ) ^ k) (-α) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hnc : (Fintype.card ↥(s k) : ℝ) = ((s k).ncard : ℝ) := by
        have h := Nat.card_coe_set_eq (s k)
        rw [Nat.card_eq_fintype_card] at h
        exact_mod_cast h
      rw [hcard'] at hstep
      rw [hnc] at hstep
      exact hstep
    calc ∑' i : ↥(s k), f ↑i = ∑ i : ↥(s k), f ↑i := htsum
      _ ≤ ((s k).ncard : ℝ) * Real.rpow ((2 : ℝ) ^ k) (-α) := hbound
      _ ≤ (C * (2 : ℝ) ^ (k + 1)) * Real.rpow ((2 : ℝ) ^ k) (-α) :=
          mul_le_mul_of_nonneg_right (hcard k) (hMnonneg k)

theorem apm_a01j06 (f : ℂ → ℂ) (ω : ℕ → ℂ) (A B : ℝ)
    (hf_entire : Differentiable ℂ f)
    (hf_nonzero : f ≠ 0)
    (hA : 0 < A)
    (hB : 0 < B)
    (hf_bound : apm_a01J06_ExpTypeBound f A B)
    (hω : apm_a01J06_EnumeratesZeros f ω) :
    ∀ α : ℝ, 1 < α →
      Summable (fun n : ℕ => Real.rpow (1 + ‖ω n‖) (-α)) := by
  /-
  CLOSER HOP 3 boundary. Going beyond the pointwise zero result, this hop
  compiles the finite multiplicity aggregation needed to compare the sequence
  with Mathlib's divisor. `apm_a01J06_finite_preimage_of_enumeratesZeros`
  proves that the indices mapping into any finite value set form a finite set,
  by expressing the preimage as a finite union of the fibers supplied by
  `hω`. `apm_a01J06_card_preimage_eq_finsum_analyticOrder` then applies
  `Set.Finite.ncard_biUnion` to the pairwise-disjoint fibers and proves the
  exact identity
  `card {n | ω n ∈ s} = ∑ z∈s, analyticOrderNatAt f z`.

  Renewed searches consulted `LEMMA-INDEX.md`, all `ConstructionTargets/`
  modules (especially `Rouche`), the historical defective zero-count artifact,
  Mathlib's Jensen/log-counting, locally-finite divisor, set-cardinality,
  finite-union, geometric-series, and summability sources, related zero-count
  problems, and git history. The finite-union and `ncard_biUnion` APIs were
  used above. No packaged theorem bounds ordinary divisor mass linearly from
  the logarithmic Jensen identity, nor converts that bound directly to this
  indexed `Real.rpow` series.

  This pass closes the qualitative disk-finiteness step:
  `apm_a01J06_finite_closedDisk_indices` identifies the zero set with the
  support of Mathlib's locally finite meromorphic divisor, intersects it with
  the compact closed disk, and transports finiteness through the enumerating
  fibers. The remaining bridge is quantitative: apply the compiled aggregation
  identity, derive an `O(r)` count from Jensen and the exponential bound, and
  complete the dyadic-shell geometric comparison for `α > 1`. No statement
  defect was found.

  HOP 4 isolates the absent library-level content as the following two exact
  contracts (not introduced as declarations, since neither was proved):

    theorem apm_a01J06_linear_zero_count
        (f : ℂ → ℂ) (omega : ℕ → ℂ) (A B : ℝ)
        (hf_entire : Differentiable ℂ f) (hf_nonzero : f ≠ 0)
        (hA : 0 < A) (hB : 0 < B)
        (hf_bound : apm_a01J06_ExpTypeBound f A B)
        (homega : apm_a01J06_EnumeratesZeros f omega) :
        ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
          Finite {n : ℕ // ‖omega n‖ ≤ R} ∧
          (Nat.card {n : ℕ // ‖omega n‖ ≤ R} : ℝ) ≤ C * R

    theorem apm_a01J06_summable_of_linear_count
        (omega : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
        (hcount : ∀ R : ℝ, 1 ≤ R →
          Finite {n : ℕ // ‖omega n‖ ≤ R} ∧
          (Nat.card {n : ℕ // ‖omega n‖ ≤ R} : ℝ) ≤ C * R)
        (α : ℝ) (hα : 1 < α) :
        Summable (fun n : ℕ ↦ Real.rpow (1 + ‖omega n‖) (-α))

  The first is exactly Jensen plus finite divisor aggregation; the second is
  the dyadic-shell geometric comparison. Their composition closes the frozen
  theorem. Searches of `JensenFormula`, value-distribution log counting,
  locally finite divisors, and summability/comparison APIs found the
  ingredients but no declarations proving either contract in this encoding.
  -/
  intro α hα
  obtain ⟨C, hC, hcount⟩ := apm_a01J06_linear_zero_count f ω A B hf_entire hf_nonzero
    hA hB hf_bound hω
  exact apm_a01J06_summable_of_linear_count ω C hC hcount α hα

