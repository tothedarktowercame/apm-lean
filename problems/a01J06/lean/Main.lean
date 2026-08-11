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
  sorry
