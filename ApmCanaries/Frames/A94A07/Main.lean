import Mathlib

open Complex Polynomial

noncomputable section

namespace ApmCanaries.Frames.A94A07.Main

/-- f is a polynomial (the singularity at ∞ is not essential). -/
lemma entire_injective_is_polynomial
    {f : ℂ → ℂ}
    (hf_holo : Differentiable ℂ f)
    (hf_inj : Function.Injective f) :
    ∃ p : ℂ[X], ∀ z, f z = Polynomial.aeval z p := by
  -- Blocker: this requires the analytic classification of the singularity at ∞
  -- (removable / pole / essential) plus a formal Casorati-Weierstrass or Picard step.
  sorry

/-- Degree ≥ 2 polynomial is not injective (takes generic values
    at multiple points). -/
lemma polynomial_degree_ge_two_not_injective
    {p : ℂ[X]} (hdeg : 2 ≤ p.natDegree) :
    ¬Function.Injective (fun z : ℂ => Polynomial.aeval z p) := by
  classical
  intro hp_inj
  let bad : Finset ℂ :=
    p.derivative.roots.toFinset.image (fun z ↦ Polynomial.eval z p)
  obtain ⟨w, -, hw⟩ :=
    Set.Infinite.exists_notMem_finset (s := (Set.univ : Set ℂ)) Set.infinite_univ bad
  let q : ℂ[X] := p - Polynomial.C w
  have hpnatpos : 0 < p.natDegree := lt_of_lt_of_le (by decide) hdeg
  have hpder_ne : p.derivative ≠ 0 := by
    intro hpder0
    simpa [hpder0] using Polynomial.degree_derivative_eq p hpnatpos
  have hqdeg : q.natDegree = p.natDegree := by
    apply Polynomial.natDegree_sub_eq_left_of_natDegree_lt
    calc
      (Polynomial.C w).natDegree = 0 := Polynomial.natDegree_C w
      _ < 2 := by decide
      _ ≤ p.natDegree := hdeg
  have hqne : q ≠ 0 := by
    intro hq0
    have : p.natDegree = 0 := by simpa [q, hq0] using hqdeg.symm
    omega
  have hqsep : q.Separable := by
    rw [Polynomial.separable_def]
    rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ q q.derivative]
    intro z
    by_cases hzq : Polynomial.aeval z q = 0
    · right
      have hz_eval_sub : Polynomial.eval z p - w = 0 := by
        simpa [q, Polynomial.coe_aeval_eq_eval, Polynomial.eval_sub, Polynomial.eval_C] using hzq
      have hz_eval : Polynomial.eval z p = w := sub_eq_zero.mp hz_eval_sub
      have hznotroot : z ∉ p.derivative.roots := by
        intro hzroot
        apply hw
        exact Finset.mem_image.mpr ⟨z, Multiset.mem_toFinset.mpr hzroot, hz_eval⟩
      have hderne : Polynomial.eval z p.derivative ≠ 0 := by
        intro hder0
        apply hznotroot
        rw [Polynomial.mem_roots hpder_ne, Polynomial.IsRoot.def]
        exact hder0
      simpa [q, Polynomial.derivative_sub, Polynomial.derivative_C, Polynomial.coe_aeval_eq_eval] using hderne
    · exact Or.inl hzq
  have hqsplit : q.Splits := IsAlgClosed.splits q
  have hqnodup : q.roots.Nodup := Polynomial.nodup_roots hqsep
  have hcard : q.roots.toFinset.card = q.natDegree := by
    rw [Multiset.toFinset_card_of_nodup hqnodup, ← hqsplit.natDegree_eq_card_roots]
  have htwo : 1 < q.roots.toFinset.card := by
    rw [hcard]
    omega
  rcases Finset.one_lt_card.mp htwo with ⟨z, hz, y, hy, hzy⟩
  have hzroot : q.IsRoot z := (Polynomial.mem_roots hqne).mp (Multiset.mem_toFinset.mp hz)
  have hyroot : q.IsRoot y := (Polynomial.mem_roots hqne).mp (Multiset.mem_toFinset.mp hy)
  have hz_eval_sub : Polynomial.eval z p - w = 0 := by
    simpa [q, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_C] using hzroot
  have hy_eval_sub : Polynomial.eval y p - w = 0 := by
    simpa [q, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_C] using hyroot
  have hz_eval : Polynomial.eval z p = w := sub_eq_zero.mp hz_eval_sub
  have hy_eval : Polynomial.eval y p = w := sub_eq_zero.mp hy_eval_sub
  have hsame : Polynomial.aeval z p = Polynomial.aeval y p := by
    rw [Polynomial.coe_aeval_eq_eval, Polynomial.coe_aeval_eq_eval, hz_eval, hy_eval]
  exact hzy (hp_inj hsame)

/-- An injective polynomial has degree exactly 1. -/
lemma injective_polynomial_degree_one
    {p : ℂ[X]}
    (hp_inj : Function.Injective (fun z : ℂ => Polynomial.aeval z p)) :
    p.natDegree = 1 := by
  have hp_nonconst : p.natDegree ≠ 0 := by
    intro hp0
    have hpconst : p = Polynomial.C (p.coeff 0) :=
      Polynomial.eq_C_of_natDegree_le_zero (by simp [hp0])
    have h0 : Polynomial.aeval (0 : ℂ) p = p.coeff 0 := by
      rw [hpconst]
      simp
    have h1 : Polynomial.aeval (1 : ℂ) p = p.coeff 0 := by
      rw [hpconst]
      simp
    have heq : Polynomial.aeval (0 : ℂ) p = Polynomial.aeval (1 : ℂ) p := by
      rw [h0, h1]
    have h01 : (0 : ℂ) = 1 := hp_inj heq
    exact zero_ne_one h01
  have hlt2 : p.natDegree < 2 := by
    by_contra h
    exact polynomial_degree_ge_two_not_injective (by omega) hp_inj
  omega

/-- Casorati-Weierstrass: essential singularity at ∞ implies
    f is not injective. -/
lemma essential_singularity_not_injective
    {f : ℂ → ℂ}
    (hf_holo : Differentiable ℂ f)
    (hf_ess : ¬∃ p : ℂ[X], ∀ z, f z = Polynomial.aeval z p)
    (hf_unbdd : ¬∃ M, ∀ z, ‖f z‖ ≤ M) :
    ¬Function.Injective f := by
  -- Blocker: this needs a formal essential-singularity theorem near ∞
  -- strong enough to force repeated values, not just density.
  sorry

/-- A degree-1 polynomial is injective. -/
lemma degree_one_injective
    {a₀ a₁ : ℂ} (ha₁ : a₁ ≠ 0) :
    Function.Injective (fun z : ℂ => a₀ + a₁ * z) := by
  intro z w h
  have h' : a₁ * z = a₁ * w := by
    have := congrArg (fun t : ℂ => t - a₀) h
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  exact mul_left_cancel₀ ha₁ h'

/-- Main theorem: an injective entire function is affine linear. -/
theorem entire_injective_is_affine
    {f : ℂ → ℂ}
    (hf_holo : Differentiable ℂ f)
    (hf_inj : Function.Injective f) :
    ∃ a₀ a₁ : ℂ, a₁ ≠ 0 ∧ ∀ z, f z = a₀ + a₁ * z := by
  rcases entire_injective_is_polynomial hf_holo hf_inj with ⟨p, hp⟩
  have hp_inj : Function.Injective (fun z : ℂ => Polynomial.aeval z p) := by
    intro z w hzw
    apply hf_inj
    simpa [hp z, hp w] using hzw
  have hpdeg : p.natDegree = 1 := injective_polynomial_degree_one hp_inj
  rcases (Polynomial.natDegree_eq_one.mp hpdeg) with ⟨a₁, ha₁, a₀, hpform⟩
  refine ⟨a₀, a₁, ha₁, ?_⟩
  intro z
  calc
    f z = Polynomial.aeval z p := hp z
    _ = Polynomial.aeval z (Polynomial.C a₁ * Polynomial.X + Polynomial.C a₀) := by
      rw [← hpform]
    _ = a₀ + a₁ * z := by
      rw [Polynomial.coe_aeval_eq_eval, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_C]
      simp [add_comm]

end ApmCanaries.Frames.A94A07.Main
