import ConstructionTargets.SardConvexDomain
import ConstructionTargets.SardHighOrderSard

open Set MeasureTheory
open scoped ContDiff ENNReal

noncomputable section

namespace ConstructionTargets.SardWhitneyExtension

/-! We work coordinate-free in a finite-dimensional real inner-product source `E` and a
finite-dimensional real normed target `F`.  Local finiteness below is deliberately relative
to `Kᶜ`: `SardConvexDomain.not_locallyFinite_whitneyNetQuarterBalls_of_frontier_nonempty`
shows that ambient local finiteness at the frontier is false. -/

/-- The canonical order-`k` within jet used in the finite-order construction. -/
def convexJet
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k : ℕ) (f : E → F) (K : Set E) (x : E) : E[×k]→L[ℝ] F :=
  iteratedFDerivWithin ℝ k f K x

/-- The degree-`m` Taylor polynomial with prescribed multilinear jet `J` at `a`. -/
def taylorPolynomial
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (m : ℕ) (J : (k : ℕ) → E → E[×k]→L[ℝ] F) (a x : E) : F :=
  ∑ k ∈ Finset.range (m + 1), ((k.factorial : ℝ)⁻¹) • J k a (fun _ ↦ x - a)

/-- Finite differentiability on a convex set with interior gives continuous symmetric
canonical within jets through the requested order.  Prove this by the finite-order versions
of the iterated-derivative continuity and Schwarz lemmas used by `ContDiffOn.convexWithinJet`. -/
theorem convexWithinJet_nat
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} {f : E → F} {m : ℕ}
    (hK : Convex ℝ K) (hKi : (interior K).Nonempty)
    (hf : ContDiffOn ℝ (m + 1) f K) :
    (∀ k ≤ m + 1, ContinuousOn (convexJet k f K) K) ∧
      (∀ x ∈ K, convexJet 0 f K x (fun i ↦ Fin.elim0 i) = f x) ∧
      (∀ x ∈ K, ∀ v, convexJet 1 f K x (fun _ ↦ v) = fderivWithin ℝ f K x v) ∧
      ∀ k ≤ m + 1, ∀ x ∈ K, ∀ σ : Equiv.Perm (Fin k),
        (convexJet k f K x).domDomCongr σ = convexJet k f K x := by
  have hu : UniqueDiffOn ℝ K := uniqueDiffOn_convex hK hKi
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk
    exact hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast hk) hu
  · intro x hx
    exact iteratedFDerivWithin_zero_apply _
  · intro x hx v
    exact iteratedFDerivWithin_one_apply (hu x hx) _
  · intro k hk x hx σ
    let L : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ E) F ≃ₗᵢ[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ E) F :=
      ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E F σ
    have hle : (k : WithTop ENat) ≤ (m + 1 : ℕ) := by exact_mod_cast hk
    have hc := (hf x hx).continuousWithinAt_iteratedFDerivWithin hu hle hx
    apply ContinuousWithinAt.eq_of_eqOn_interior_of_mem_closure
      (by
        rw [hK.closure_interior_eq_closure_of_nonempty_interior hKi]
        exact subset_closure hx)
      (L.continuous.continuousAt.comp_continuousWithinAt hc) hc
    intro y hy
    exact ((hf y (interior_subset hy)).of_le hle).domDomCongr_iteratedFDerivWithin_of_nat_of_mem_interior
      hu k hy σ

/-- On a compact convex set, continuity of the top within derivative gives one uniform
Taylor constant for every lower jet.  Apply the Banach-valued segment integral remainder
on `K`, bound the top jet on the compact set, and absorb factorial constants into `C`. -/
theorem compactConvex_taylor_remainder_bound
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {K : Set E} {f : E → F} {m : ℕ}
    (hKc : IsCompact K) (hK : Convex ℝ K) (hKi : (interior K).Nonempty)
    (hf : ContDiffOn ℝ (m + 1) f K) :
    ∃ C ≥ 0, ∀ k ≤ m, ∀ a ∈ K, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ k (taylorPolynomial m (fun j ↦ convexJet j f K) a) x -
          convexJet k f K x‖ ≤ C * ‖x - a‖ ^ (m + 1 - k) := by
  sorry

/-- Exact derivative formula for the Taylor polynomial.  Evaluate on `v`, differentiate
the diagonal monomials, use symmetry to identify all injections of the `k` derivative
variables, and cancel `j!/(j-k)!` against `j!`; the surviving factor is `(j-k)!⁻¹`. -/
theorem iteratedFDeriv_taylorPolynomial_exact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (m k : ℕ) (J : (j : ℕ) → E → E[×j]→L[ℝ] F) (a x : E)
    (hk : k ≤ m) (v : Fin k → E)
    (hJ : ∀ j ≤ m, ∀ σ : Equiv.Perm (Fin j),
      (J j a).domDomCongr σ = J j a) :
    iteratedFDeriv ℝ k (taylorPolynomial m J a) x v =
      ∑ q ∈ Finset.range (m + 1 - k), (q.factorial : ℝ)⁻¹ •
        J (k + q) a (Fin.append v (fun _ : Fin q ↦ x - a)) := by
  sorry

/-- Norm consequence of the exact shifted-jet formula.  Apply the multilinear norm bound
to every summand of `iteratedFDeriv_taylorPolynomial_exact`; note in particular that the
coefficient is `(j-k)!⁻¹`, not `j!⁻¹`. -/
theorem iteratedFDeriv_taylorPolynomial_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (m k : ℕ) (J : (j : ℕ) → E → E[×j]→L[ℝ] F) (a x : E)
    (hk : k ≤ m)
    (hJ : ∀ j ≤ m, ∀ σ : Equiv.Perm (Fin j),
      (J j a).domDomCongr σ = J j a) :
    ‖iteratedFDeriv ℝ k (taylorPolynomial m J a) x‖ ≤
      ∑ j ∈ Finset.Icc k m,
        (((j - k).factorial : ℝ)⁻¹) * ‖J j a‖ * ‖x - a‖ ^ (j - k) := by
  sorry

/-- Taylor polynomials based at two points of `K` differ to the full Whitney order.
Expand `P_a-P_b` at `b`; its derivatives there are controlled by the compact convex
remainder estimate, then evaluate that finite polynomial using the exact formula above. -/
theorem taylor_difference_bound
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {K : Set E} {f : E → F} {m : ℕ}
    (hKc : IsCompact K) (hK : Convex ℝ K) (hKi : (interior K).Nonempty)
    (hf : ContDiffOn ℝ (m + 1) f K) :
    ∃ C ≥ 0, ∀ r ≤ m, ∀ a ∈ K, ∀ b ∈ K, ∀ x : E,
      ‖iteratedFDeriv ℝ r
          (fun y ↦ taylorPolynomial m (fun j ↦ convexJet j f K) a y -
            taylorPolynomial m (fun j ↦ convexJet j f K) b y) x‖ ≤
        C * (‖x - a‖ + ‖x - b‖) ^ (m + 1 - r) := by
  sorry

/-- Smooth partition data on the complement, indexed by the already constructed dyadic
Whitney nets.  Supports use half-distance balls while quarter-distance balls cover; only
complement-local finiteness is asserted, as ambient local finiteness is false. -/
structure WhitneySmoothPartition
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) where
  phi : SardConvexDomain.WhitneyNetIndex K → E → ℝ
  contDiff_phi : ∀ i, ContDiff ℝ ∞ (phi i)
  support_subset : ∀ i, Function.support (phi i) ⊆
    Metric.ball i.center (Metric.infDist i.center K / 2)
  nonneg : ∀ i x, 0 ≤ phi i x
  sum_one : ∀ x ∉ K, HasSum (fun i ↦ phi i x) 1
  locallyFinite_compl : ∀ x ∉ K, ∃ U ∈ nhds x,
    {i | (U ∩ Function.support (phi i)).Nonempty}.Finite
  derivConstant : ℕ → ℝ
  derivConstant_nonneg : ∀ k, 0 ≤ derivConstant k
  deriv_bound : ∀ k i x,
    ‖iteratedFDeriv ℝ k (phi i) x‖ ≤
      derivConstant k * (Metric.infDist i.center K)⁻¹ ^ k

/-- Construct unnormalised smooth bumps equal to one on the quarter-balls and supported in
the half-balls, with scale-correct derivative bounds.  Rescale one fixed Euclidean bump;
the existing half-ball incidence theorem supplies complement-local finiteness. -/
theorem exists_whitney_bump_family_aux_half_localFinite
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hK : IsClosed K) (hKn : K.Nonempty) :
    ∀ x ∉ K, ∃ U ∈ nhds x,
      {i : SardConvexDomain.WhitneyNetIndex K |
        (U ∩ Metric.ball i.center (Metric.infDist i.center K / 2)).Nonempty}.Finite := by
  intro x hx
  let r := Metric.infDist x K / 16
  let I : Set (SardConvexDomain.WhitneyNetIndex K) := {i |
    (Metric.ball x r ∩ Metric.ball i.center
      (Metric.infDist i.center K / 2)).Nonempty}
  have hxpos : 0 < Metric.infDist x K := (hK.notMem_iff_infDist_pos hKn).1 hx
  have hscale (i : SardConvexDomain.WhitneyNetIndex K) (hi : i ∈ I) :
      5 * Metric.infDist x K < 8 * Metric.infDist i.center K ∧
        8 * Metric.infDist i.center K < 17 * Metric.infDist x K := by
    obtain ⟨y, hyx, hyi⟩ := hi
    have ha : dist x y < Metric.infDist x K / 16 := by
      simpa [r, dist_comm] using Metric.mem_ball.1 hyx
    have hb : dist y i.center < Metric.infDist i.center K / 2 := Metric.mem_ball.1 hyi
    have hxy := Metric.infDist_le_infDist_add_dist (s := K) (x := x) (y := y)
    have hyx' := Metric.infDist_le_infDist_add_dist (s := K) (x := y) (y := x)
    have hc := SardConvexDomain.infDist_center_comparable_of_mem_half_ball K hyi
    have had : dist y x = dist x y := dist_comm _ _
    constructor <;> nlinarith
  have hfiber (k : ℤ) : {i | i.1 = k ∧ i ∈ I}.Finite := by
    let f : SardConvexDomain.WhitneyNetIndex K → E :=
      SardConvexDomain.WhitneyNetIndex.center
    have hinj : Set.InjOn f {i | i.1 = k ∧ i ∈ I} := by
      intro i hi j hj hij
      have hk : i.1 = j.1 := hi.1.trans hj.1.symm
      cases i with
      | mk ik ic =>
        cases j with
        | mk jk jc =>
          dsimp at hk hij ⊢
          subst jk
          exact congrArg (Sigma.mk ik) (Subtype.ext hij)
    apply Set.Finite.of_finite_image (f := f) _ hinj
    apply (SardConvexDomain.finite_inter_whitneyStratumNet_of_isCompact K k
      (isCompact_closedBall x (4 * (2 : ℝ) ^ (k + 1)))).subset
    rintro c ⟨i, hi, rfl⟩
    constructor
    · change i.2.1 ∈ SardConvexDomain.whitneyStratumNet K k
      rw [← hi.1]
      exact i.2.2
    · obtain ⟨y, hyx, hyi⟩ := hi.2
      apply Metric.mem_closedBall.2
      have ha : dist x y < Metric.infDist x K / 16 := by
        simpa [r, dist_comm] using Metric.mem_ball.1 hyx
      have hb : dist y i.center < Metric.infDist i.center K / 2 := Metric.mem_ball.1 hyi
      have hs := hscale i hi.2
      have hstr : Metric.infDist i.center K < (2 : ℝ) ^ (k + 1) := by
        simpa only [hi.1] using
          ((SardConvexDomain.whitneyStratumNet_spec K i.1).1 i.2.2).2.2
      have ht := dist_triangle x y i.center
      have hp : 0 < (2 : ℝ) ^ (k + 1) := by positivity
      rw [show dist (f i) x = dist x i.center by simp [f, dist_comm]]
      nlinarith
  refine ⟨Metric.ball x r, Metric.ball_mem_nhds x (by dsimp [r]; positivity), ?_⟩
  change I.Finite
  by_cases hI : I.Nonempty
  · obtain ⟨i, hi⟩ := hI
    have hfinite := (Set.finite_Icc (i.1 - 3) (i.1 + 3)).biUnion
      (fun k _ => hfiber k)
    apply hfinite.subset
    intro j hj
    have hsi := hscale i hi
    have hsj := hscale j hj
    have hik : (2 : ℝ) ^ i.1 ≤ Metric.infDist i.center K :=
      ((SardConvexDomain.whitneyStratumNet_spec K i.1).1 i.2.2).2.1
    have hjk : Metric.infDist j.center K < (2 : ℝ) ^ (j.1 + 1) :=
      ((SardConvexDomain.whitneyStratumNet_spec K j.1).1 j.2.2).2.2
    have hjlow : (2 : ℝ) ^ j.1 ≤ Metric.infDist j.center K :=
      ((SardConvexDomain.whitneyStratumNet_spec K j.1).1 j.2.2).2.1
    have hiup : Metric.infDist i.center K < (2 : ℝ) ^ (i.1 + 1) :=
      ((SardConvexDomain.whitneyStratumNet_spec K i.1).1 i.2.2).2.2
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)] at hjk hiup
    norm_num at hjk hiup
    have hlo : i.1 - 3 ≤ j.1 := by
      by_contra hn
      have hp : (2 : ℝ) ^ (j.1 + 4) ≤ (2 : ℝ) ^ i.1 :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)] at hp
      norm_num at hp
      have hpi : 0 < (2 : ℝ) ^ i.1 := by positivity
      have hpj : 0 < (2 : ℝ) ^ j.1 := by positivity
      nlinarith
    have hhi : j.1 ≤ i.1 + 3 := by
      by_contra hn
      have hp : (2 : ℝ) ^ (i.1 + 4) ≤ (2 : ℝ) ^ j.1 :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)] at hp
      norm_num at hp
      have hpi : 0 < (2 : ℝ) ^ i.1 := by positivity
      have hpj : 0 < (2 : ℝ) ^ j.1 := by positivity
      nlinarith
    exact Set.mem_iUnion₂.2 ⟨j.1, ⟨hlo, hhi⟩, ⟨rfl, hj⟩⟩
  · rw [Set.not_nonempty_iff_eq_empty.mp hI]
    exact Set.finite_empty

theorem exists_whitney_bump_family
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hK : IsClosed K) (hKn : K.Nonempty) :
    ∃ psi : SardConvexDomain.WhitneyNetIndex K → E → ℝ,
      (∀ i, ContDiff ℝ ∞ (psi i)) ∧
      (∀ i x, 0 ≤ psi i x ∧ psi i x ≤ 1) ∧
      (∀ i, Metric.ball i.center (Metric.infDist i.center K / 4) ⊆
        {x | psi i x = 1}) ∧
      (∀ i, Function.support (psi i) ⊆ Metric.ball i.center (Metric.infDist i.center K / 2)) ∧
      (∀ x ∉ K, ∃ U ∈ nhds x, {i | (U ∩ Function.support (psi i)).Nonempty}.Finite) ∧
      ∃ C : ℕ → ℝ, ∀ k i x,
        ‖iteratedFDeriv ℝ k (psi i) x‖ ≤
          C k * (Metric.infDist i.center K)⁻¹ ^ k := by
  let b : ContDiffBump (0 : E) :=
    ⟨(1 : ℝ) / 4, (1 : ℝ) / 2, by norm_num, by norm_num⟩
  let psi : SardConvexDomain.WhitneyNetIndex K → E → ℝ := fun i x =>
    b ((Metric.infDist i.center K)⁻¹ • (x - i.center))
  have hcenter (i : SardConvexDomain.WhitneyNetIndex K) : i.center ∉ K :=
    ((SardConvexDomain.whitneyStratumNet_spec K i.1).1 i.2.2).1
  have hd (i : SardConvexDomain.WhitneyNetIndex K) : 0 < Metric.infDist i.center K :=
    (hK.notMem_iff_infDist_pos hKn).1 (hcenter i)
  have hbdd : ∀ k : ℕ, ∃ B : ℝ, ∀ x : E,
      ‖iteratedFDeriv ℝ k (b : E → ℝ) x‖ ≤ B := by
    intro k
    have hc : HasCompactSupport (iteratedFDeriv ℝ k (b : E → ℝ)) :=
      b.hasCompactSupport.iteratedFDeriv k
    have hcont : Continuous (iteratedFDeriv ℝ k (b : E → ℝ)) :=
      b.contDiff.continuous_iteratedFDeriv (mod_cast le_top)
    have hbound := hcont.norm.bddAbove_range_of_hasCompactSupport hc.norm
    rw [bddAbove_def] at hbound
    simpa only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff] using hbound
  choose C hC using hbdd
  refine ⟨psi, ?_, ?_, ?_, ?_, ?_, C, ?_⟩
  · intro i
    exact b.contDiff.comp
      (contDiff_const.smul (contDiff_id.sub contDiff_const))
  · intro i x
    exact ⟨b.nonneg, b.le_one⟩
  · intro i x hx
    apply b.one_of_mem_closedBall
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos (hd i)]
    have hx' := Metric.mem_ball.1 hx
    rw [dist_eq_norm] at hx'
    rw [inv_mul_le_iff₀ (hd i)]
    exact (le_of_lt hx').trans_eq (by ring)
  · intro i x hx
    change b ((Metric.infDist i.center K)⁻¹ • (x - i.center)) ≠ 0 at hx
    have hbmem : (Metric.infDist i.center K)⁻¹ • (x - i.center) ∈
        Metric.ball (0 : E) ((1 : ℝ) / 2) := by
      rwa [← b.support_eq]
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos (hd i)] at hbmem
    rw [Metric.mem_ball, dist_eq_norm]
    rw [inv_mul_lt_iff₀ (hd i)] at hbmem
    simpa using hbmem
  · intro x hx
    obtain ⟨U, hU, hfin⟩ :=
      exists_whitney_bump_family_aux_half_localFinite hK hKn x hx
    refine ⟨U, hU, hfin.subset ?_⟩
    intro i hi
    obtain ⟨y, hyU, hypsi⟩ := hi
    refine ⟨y, hyU, ?_⟩
    apply (show Function.support (psi i) ⊆
      Metric.ball i.center (Metric.infDist i.center K / 2) from ?_) hypsi
    intro z hz
    change b ((Metric.infDist i.center K)⁻¹ • (z - i.center)) ≠ 0 at hz
    have hbmem : (Metric.infDist i.center K)⁻¹ • (z - i.center) ∈
        Metric.ball (0 : E) ((1 : ℝ) / 2) := by rwa [← b.support_eq]
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos (hd i)] at hbmem
    rw [inv_mul_lt_iff₀ (hd i)] at hbmem
    rw [Metric.mem_ball, dist_eq_norm]
    simpa using hbmem
  · intro k i x
    change ‖iteratedFDeriv ℝ k
      (fun z => b ((Metric.infDist i.center K)⁻¹ • (z - i.center))) x‖ ≤ _
    rw [iteratedFDeriv_comp_sub (f := fun z => b ((Metric.infDist i.center K)⁻¹ • z))]
    rw [iteratedFDeriv_comp_const_smul _ b.contDiff]
    dsimp only
    rw [norm_smul, Real.norm_eq_abs, abs_pow, abs_inv,
      abs_of_pos (hd i)]
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_left
        (hC k ((Metric.infDist i.center K)⁻¹ • (x - i.center)))
        (pow_nonneg (inv_nonneg.2 (hd i).le) k))

/-- The sum of incident unnormalised bumps is locally a finite smooth positive function on
the complement, bounded below by one.  Use quarter-ball coverage for positivity and the
half-ball local-finiteness result to replace the `tsum` by a finite sum near each point. -/
theorem whitney_bump_sum_positive_smooth
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hK : IsClosed K) (hKn : K.Nonempty)
    (psi : SardConvexDomain.WhitneyNetIndex K → E → ℝ)
    (hnonneg : ∀ i x, 0 ≤ psi i x)
    (hone : ∀ i, Metric.ball i.center (Metric.infDist i.center K / 4) ⊆
      {x | psi i x = 1})
    (hsupp : ∀ i, Function.support (psi i) ⊆
      Metric.ball i.center (Metric.infDist i.center K / 2))
    (hlocal : ∀ x ∉ K, ∃ U ∈ nhds x,
      {i | (U ∩ Function.support (psi i)).Nonempty}.Finite)
    (hsmooth : ∀ i, ContDiff ℝ ∞ (psi i)) :
    ∀ x ∉ K, 1 ≤ ∑' i, psi i x ∧
      ContDiffAt ℝ ∞ (fun y ↦ ∑' i, psi i y) x := by
  sorry

/-- Uniform, rather than merely pointwise finite, incidence of Whitney half-balls.
Adjacent incident strata have comparable scales; within each stratum the net centers are
uniformly separated and lie in a comparable ball, so a finite-dimensional volume packing
argument using additive Haar measure gives a bound independent of `x`. -/
theorem whitney_bounded_overlap_aux_normalized
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Set E) (k : ℤ) (x c : E)
    (hc : c ∈ SardConvexDomain.whitneyScaleStratum s k)
    (hxc : x ∈ Metric.ball c (Metric.infDist c s / 2)) :
    SardConvexDomain.whitneyNormalize k x c ∈ Metric.closedBall (0 : E) 1 := by
  apply Metric.mem_closedBall.2
  have hdist : dist c x < (2 : ℝ) ^ (k + 1) / 2 := by
    have h := Metric.mem_ball.1 hxc
    rw [dist_comm]
    exact h.trans (div_lt_div_of_pos_right hc.2.2 (by norm_num))
  exact le_of_lt (calc
    dist (SardConvexDomain.whitneyNormalize k x c) 0 =
        ((2 : ℝ) ^ k)⁻¹ * dist c x := by
      simpa [SardConvexDomain.whitneyNormalize] using
        SardConvexDomain.dist_whitneyNormalize k x c x
    _ < ((2 : ℝ) ^ k)⁻¹ * ((2 : ℝ) ^ (k + 1) / 2) :=
      mul_lt_mul_of_pos_left hdist (inv_pos.mpr (by positivity))
    _ = 1 := by
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      field_simp)

theorem whitney_bounded_overlap_aux_fiber
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Set E) (k : ℤ) (x : E) :
    {i : SardConvexDomain.WhitneyNetIndex s | i.1 = k ∧
      x ∈ Metric.ball i.center (Metric.infDist i.center s / 2)}.encard ≤
      Metric.packingNumber ((1 : NNReal) / 8) (Metric.closedBall (0 : E) 1) := by
  let I : Set (SardConvexDomain.WhitneyNetIndex s) := {i | i.1 = k ∧
    x ∈ Metric.ball i.center (Metric.infDist i.center s / 2)}
  let f : SardConvexDomain.WhitneyNetIndex s → E := fun i =>
    SardConvexDomain.whitneyNormalize k x i.center
  have hinj : Set.InjOn f I := by
    intro i hi j hj hij
    have hk : i.1 = j.1 := hi.1.trans hj.1.symm
    have hcent : i.center = j.center := by
      have hz : ((2 : ℝ) ^ k)⁻¹ * dist i.center j.center = 0 := by
        rw [← SardConvexDomain.dist_whitneyNormalize k x i.center j.center]
        have hij' : SardConvexDomain.whitneyNormalize k x i.center =
            SardConvexDomain.whitneyNormalize k x j.center := by simpa [f] using hij
        rw [hij', dist_self]
      exact dist_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left
        (ne_of_gt (inv_pos.mpr (by positivity))))
    cases i with
    | mk ik ic =>
      cases j with
      | mk jk jc =>
        dsimp at hk hcent ⊢
        subst jk
        exact congrArg (Sigma.mk ik) (Subtype.ext hcent)
  rw [← hinj.encard_image]
  refine (?_ : Metric.IsSeparated (↑((1 : NNReal) / 8)) (f '' I)).encard_le_packingNumber ?_
  · apply Set.Pairwise.image
    intro (i : SardConvexDomain.WhitneyNetIndex s) hi j hj hne
    have hcne : i.center ≠ j.center := by
      intro h
      apply hne
      have hk : i.1 = j.1 := hi.1.trans hj.1.symm
      cases i with
      | mk ik ic =>
        cases j with
        | mk jk jc =>
          dsimp at hk h ⊢
          subst jk
          exact congrArg (Sigma.mk ik) (Subtype.ext h)
    have hsep := (SardConvexDomain.whitneyStratumNet_spec s k).2.1
      (by rw [← hi.1]; exact i.2.2) (by rw [← hj.1]; exact j.2.2) hcne
    have hr : (2 : ℝ) ^ k / 8 < dist i.center j.center := by
      simpa [SardConvexDomain.whitneyStratumRadius, edist_dist] using hsep
    have hn := SardConvexDomain.dist_whitneyNormalize k x i.center j.center
    have hfixed : (1 / 8 : ℝ) < dist (f i) (f j) := by
      change (1 / 8 : ℝ) < dist (SardConvexDomain.whitneyNormalize k x i.center)
        (SardConvexDomain.whitneyNormalize k x j.center)
      rw [hn]
      calc
        (1 / 8 : ℝ) = ((2 : ℝ) ^ k)⁻¹ * ((2 : ℝ) ^ k / 8) := by field_simp
        _ < ((2 : ℝ) ^ k)⁻¹ * dist i.center j.center :=
          mul_lt_mul_of_pos_left hr (inv_pos.mpr (by positivity))
    dsimp only [Function.onFun]
    rw [edist_dist]
    simpa using (ENNReal.ofReal_lt_ofReal_iff
      (lt_trans (by norm_num : (0 : ℝ) < 1 / 8) hfixed)).2 hfixed
  · rintro _ ⟨i, hi, rfl⟩
    exact whitney_bounded_overlap_aux_normalized s k x i.center
      ((SardConvexDomain.whitneyStratumNet_spec s k).1 (by rw [← hi.1]; exact i.2.2)) hi.2

theorem whitney_bounded_overlap
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hK : IsClosed K) (hKn : K.Nonempty) :
    ∃ N : ℕ, ∀ x : E,
      Set.ncard {i : SardConvexDomain.WhitneyNetIndex K |
        x ∈ Metric.ball i.center (Metric.infDist i.center K / 2)} ≤ N := by
  let P := Metric.packingNumber ((1 : NNReal) / 8) (Metric.closedBall (0 : E) 1)
  have hP : P ≠ ⊤ := by
    exact (isCompact_closedBall (0 : E) 1).packingNumber_ne_top _ (by norm_num)
  refine ⟨P.toNat * 5, fun x => ?_⟩
  let I : Set (SardConvexDomain.WhitneyNetIndex K) :=
    {i | x ∈ Metric.ball i.center (Metric.infDist i.center K / 2)}
  have hfin : I.Finite := SardConvexDomain.finite_whitneyNetHalfIncidence K x
  by_cases hne : I.Nonempty
  · obtain ⟨i, hi⟩ := hne
    let J : ℤ → Set (SardConvexDomain.WhitneyNetIndex K) := fun k =>
      {j | j.1 = k ∧ j ∈ I}
    have hJ (k : ℤ) : (J k).ncard ≤ P.toNat := by
      have he := whitney_bounded_overlap_aux_fiber K k x
      have ht := ENat.toNat_le_toNat he hP
      simpa [J, I, P] using ht
    have hsub : I ⊆ J (i.1 - 2) ∪ J (i.1 - 1) ∪ J i.1 ∪ J (i.1 + 1) ∪ J (i.1 + 2) := by
      intro j hj
      have hb := SardConvexDomain.whitneyStratum_indices_le_add_two_of_mem_half_balls K
        ((SardConvexDomain.whitneyStratumNet_spec K i.1).1 i.2.2)
        ((SardConvexDomain.whitneyStratumNet_spec K j.1).1 j.2.2) hi hj
      have hor : j.1 = i.1 - 2 ∨ j.1 = i.1 - 1 ∨ j.1 = i.1 ∨
          j.1 = i.1 + 1 ∨ j.1 = i.1 + 2 := by omega
      rcases hor with e | e | e | e | e <;> simp [J, e, hj]
    have hJfin (k : ℤ) : (J k).Finite := hfin.subset (fun _ h => h.2)
    have hUfin : (J (i.1 - 2) ∪ J (i.1 - 1) ∪ J i.1 ∪ J (i.1 + 1) ∪
        J (i.1 + 2)).Finite :=
      ((((hJfin (i.1 - 2)).union (hJfin (i.1 - 1))).union (hJfin i.1)).union
        (hJfin (i.1 + 1))).union (hJfin (i.1 + 2))
    have hn := Set.ncard_le_ncard hsub hUfin
    have hu1 := Set.ncard_union_le (J (i.1 - 2)) (J (i.1 - 1))
    have hu2 := Set.ncard_union_le (J (i.1 - 2) ∪ J (i.1 - 1)) (J i.1)
    have hu3 := Set.ncard_union_le (J (i.1 - 2) ∪ J (i.1 - 1) ∪ J i.1) (J (i.1 + 1))
    have hu4 := Set.ncard_union_le
      (J (i.1 - 2) ∪ J (i.1 - 1) ∪ J i.1 ∪ J (i.1 + 1)) (J (i.1 + 2))
    calc
      I.ncard ≤ (J (i.1 - 2) ∪ J (i.1 - 1) ∪ J i.1 ∪ J (i.1 + 1) ∪
        J (i.1 + 2)).ncard := hn
      _ ≤ (J (i.1 - 2)).ncard + (J (i.1 - 1)).ncard + (J i.1).ncard +
          (J (i.1 + 1)).ncard + (J (i.1 + 2)).ncard := by
        omega
      _ ≤ P.toNat * 5 := by
        have h1 := hJ (i.1 - 2)
        have h2 := hJ (i.1 - 1)
        have h3 := hJ i.1
        have h4 := hJ (i.1 + 1)
        have h5 := hJ (i.1 + 2)
        omega
  · have hz : {i : SardConvexDomain.WhitneyNetIndex K |
        x ∈ Metric.ball i.center (Metric.infDist i.center K / 2)} = ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      simpa [I] using hne
    rw [hz]
    simp

/-- Scale-correct derivative bounds for a reciprocal.  For each order and list of input
bounds there is a universal output bound: differentiate `S * S⁻¹ = 1`, isolate the top
derivative of `S⁻¹`, and induct using the multilinear Leibniz formula and `1 ≤ S x`. -/
theorem iteratedFDeriv_inv_bound
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (A : ℕ → ℝ) :
    ∃ B ≥ 0, ∀ (S : E → ℝ) (x : E) (r : ℝ), 0 < r → 1 ≤ S x →
      ContDiffAt ℝ k S x →
      (∀ j ≤ k, ‖iteratedFDeriv ℝ j S x‖ ≤ A j * r⁻¹ ^ j) →
      ‖iteratedFDeriv ℝ k (fun y ↦ (S y)⁻¹) x‖ ≤ B * r⁻¹ ^ k := by
  sorry

/-- Normalising the bump family gives a partition of unity with derivative bounds at every
order needed by the extension.  Combine the reciprocal leaf with the uniform-overlap leaf,
then apply local finite-sum product estimates and comparability of incident scales. -/
theorem exists_whitneySmoothPartition
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hK : IsClosed K) (hKn : K.Nonempty) :
    Nonempty (WhitneySmoothPartition E K) := by
  sorry

/-- At a point in a partition support, its center, anchor, and scale are uniformly comparable
to the point's distance from `K`.  Combine the half-ball comparison lemmas with the anchor
nearest-point identity and the 1-Lipschitz property of `infDist`. -/
theorem whitney_support_geometry
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hK : IsClosed K) (hKn : K.Nonempty)
    (P : WhitneySmoothPartition E K) {i : SardConvexDomain.WhitneyNetIndex K}
    {x : E} (hx : x ∈ Function.support (P.phi i)) :
    Metric.infDist i.center K ≤ 2 * Metric.infDist x K ∧
      Metric.infDist x K ≤ 2 * Metric.infDist i.center K ∧
      dist x (SardConvexDomain.whitneyNetAnchor hK hKn i) ≤
        3 * Metric.infDist x K := by
  have hxb : x ∈ Metric.ball i.center (Metric.infDist i.center K / 2) :=
    P.support_subset i hx
  have hcomp :=
    SardConvexDomain.infDist_center_comparable_of_mem_half_ball K hxb
  have hc0 : 0 ≤ Metric.infDist i.center K := Metric.infDist_nonneg
  have hdist : dist x i.center < Metric.infDist i.center K / 2 :=
    Metric.mem_ball.1 hxb
  have hanchor := SardConvexDomain.whitneyNetAnchor_nearest hK hKn i
  refine ⟨hcomp.1.le, by linarith, ?_⟩
  calc dist x (SardConvexDomain.whitneyNetAnchor hK hKn i)
      ≤ dist x i.center +
          dist i.center (SardConvexDomain.whitneyNetAnchor hK hKn i) :=
        dist_triangle _ _ _
    _ = dist x i.center + Metric.infDist i.center K := by rw [hanchor]
    _ ≤ Metric.infDist i.center K / 2 + Metric.infDist i.center K := by
        linarith [hdist.le]
    _ ≤ 3 * Metric.infDist x K := by linarith

/-- The off-set Whitney formula is a `tsum`; complement-local finiteness makes it a finite
sum in a neighborhood of every point where it is used. -/
def whitneyOffExtension
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} (m : ℕ) (f : E → F) (hK : IsClosed K) (hKn : K.Nonempty)
    (P : WhitneySmoothPartition E K) (x : E) : F :=
  ∑' i, P.phi i x • taylorPolynomial m (fun k ↦ convexJet k f K)
    (SardConvexDomain.whitneyNetAnchor hK hKn i) x

/-- The Whitney sum is `Cᵐ` on the complement.  Near a complement point reduce the `tsum`
to the finite support family supplied by `locallyFinite_compl`, then use smoothness of each
partition function and the polynomial nature of each Taylor term. -/
theorem whitneyOffExtension_contDiffOn_compl
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} {m : ℕ} {f : E → F} (hK : IsClosed K) (hKn : K.Nonempty)
    (P : WhitneySmoothPartition E K) :
    ContDiffOn ℝ m (whitneyOffExtension m f hK hKn P) Kᶜ := by
  intro x hx
  rcases P.locallyFinite_compl x hx with ⟨U, hU, hfin⟩
  let S : Finset (SardConvexDomain.WhitneyNetIndex K) := hfin.toFinset
  have hzero : ∀ y ∈ U, ∀ i ∉ S, P.phi i y = 0 := by
    intro y hy i hi
    by_contra hne
    have hys : y ∈ Function.support (P.phi i) := hne
    have hi' : i ∈ {i | (U ∩ Function.support (P.phi i)).Nonempty} := by
      exact ⟨y, hy, hys⟩
    exact hi (by simpa [S] using hi')
  have heq : ∀ y ∈ U,
      whitneyOffExtension m f hK hKn P y =
        ∑ i ∈ S, P.phi i y • taylorPolynomial m (fun k ↦ convexJet k f K)
          (SardConvexDomain.whitneyNetAnchor hK hKn i) y := by
    intro y hy
    unfold whitneyOffExtension
    exact tsum_eq_sum (fun i hi ↦ by simp [hzero y hy i hi])
  have hsmooth : ContDiff ℝ m (fun y : E ↦
      ∑ i ∈ S, P.phi i y • taylorPolynomial m (fun k ↦ convexJet k f K)
        (SardConvexDomain.whitneyNetAnchor hK hKn i) y) := by
    apply ContDiff.sum
    intro i hi
    apply (P.contDiff_phi i).of_le
      (by exact_mod_cast (show (m : ℕ∞) ≤ ⊤ from le_top)) |>.smul
    unfold taylorPolynomial
    apply ContDiff.sum
    intro k hk
    apply contDiff_const.smul
    exact (ContinuousMultilinearMap.contDiff _).comp
      (contDiff_pi.2 fun _ ↦ contDiff_id.sub contDiff_const)
  apply hsmooth.contDiffAt.contDiffWithinAt.congr_of_eventuallyEq
  · have hUw : ∀ᶠ y in nhdsWithin x Kᶜ, y ∈ U :=
      Filter.Eventually.filter_mono inf_le_left hU
    filter_upwards [hUw] with y hy
    exact heq y hy
  · exact heq x (mem_of_mem_nhds hU)

/-- The exact subtraction identity behind the off-set estimate.  Replace `1` by the locally
finite sum of the partition and distribute the common polynomial; no differentiated
partition-cancellation lemma is needed once subtraction occurs before differentiating. -/
theorem whitneyOffExtension_sub_taylor
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} {m : ℕ} {f : E → F}
    (hK : IsClosed K) (hKn : K.Nonempty) (P : WhitneySmoothPartition E K)
    {x a : E} (hx : x ∉ K) :
    whitneyOffExtension m f hK hKn P x -
        taylorPolynomial m (fun j ↦ convexJet j f K) a x =
      ∑' i, P.phi i x •
        (taylorPolynomial m (fun j ↦ convexJet j f K)
            (SardConvexDomain.whitneyNetAnchor hK hKn i) x -
          taylorPolynomial m (fun j ↦ convexJet j f K) a x) := by
  let Q : SardConvexDomain.WhitneyNetIndex K → F := fun i ↦
    taylorPolynomial m (fun j ↦ convexJet j f K)
      (SardConvexDomain.whitneyNetAnchor hK hKn i) x
  let T : F := taylorPolynomial m (fun j ↦ convexJet j f K) a x
  obtain ⟨U, hU, hfin⟩ := P.locallyFinite_compl x hx
  have hxU : x ∈ U := mem_of_mem_nhds hU
  have hfinite : (fun i ↦ P.phi i x • Q i).HasFiniteSupport := by
    refine hfin.subset ?_
    intro i hi
    have hphi : P.phi i x ≠ 0 := by
      intro hz
      apply hi
      simp [hz]
    exact ⟨x, hxU, hphi⟩
  have hQ : Summable (fun i ↦ P.phi i x • Q i) :=
    summable_of_hasFiniteSupport hfinite
  have hT : HasSum (fun i ↦ P.phi i x • T) T := by
    simpa using (P.sum_one x hx).smul_const T
  have hsub : HasSum (fun i ↦ P.phi i x • Q i - P.phi i x • T)
      ((∑' i, P.phi i x • Q i) - T) := hQ.hasSum.sub hT
  change (∑' i, P.phi i x • Q i) - T =
    ∑' i, P.phi i x • (Q i - T)
  rw [← hsub.tsum_eq]
  apply tsum_congr
  intro i
  exact (smul_sub (P.phi i x) (Q i) T).symm

/-- The complete finite-overlap estimate near the frontier, now relative to the Taylor
polynomial at a nearest point.  Differentiate the subtraction identity, use
`norm_iteratedFDeriv_smul_le`, `taylor_difference_bound`, support geometry, derivative
bounds, and uniform overlap; each Leibniz term has power `dist(x,K)^(m+1-k)`. -/
theorem whitneyOffExtension_jet_bound
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {K : Set E} {m : ℕ} {f : E → F}
    (hKc : IsCompact K) (hK : Convex ℝ K) (hKi : (interior K).Nonempty)
    (hf : ContDiffOn ℝ (m + 1) f K) (P : WhitneySmoothPartition E K) :
    ∃ C ≥ 0, ∀ k ≤ m, ∀ x ∉ K,
      ∃ a ∈ K, Metric.infDist x K = dist x a ∧
        ‖iteratedFDeriv ℝ k (whitneyOffExtension m f hKc.isClosed
              (hKi.mono interior_subset) P) x -
            iteratedFDeriv ℝ k
              (taylorPolynomial m (fun j ↦ convexJet j f K) a) x‖ ≤
          C * (Metric.infDist x K) ^ (m + 1 - k) := by
  sorry

/-- The candidate global Taylor series: within jets on `K`, ordinary iterated derivatives
off `K`.  The order-zero terms are stored as continuous zero-linear maps, just as in
Mathlib's `FormalMultilinearSeries`. -/
def gluedWhitneyJet
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : Set E) (f G : E → F) (x : E) : FormalMultilinearSeries ℝ E F := by
  classical
  exact fun k ↦ if x ∈ K then convexJet k f K x else iteratedFDeriv ℝ k G x

/-- Each component of the glued jet is continuous across `K`.  Off `K` this follows from
smoothness.  At `a' ∈ K`, choose a nearest `a` to an exterior `x`, compare through
`D^k P_a(x)`, then use the two-base-point Taylor bound and continuity of the within jet. -/
theorem continuous_gluedWhitneyJet
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {K : Set E} {m : ℕ} {f G : E → F}
    (hK : IsClosed K) (hKn : K.Nonempty)
    (hGo : ContDiffOn ℝ m G Kᶜ)
    (hjet : ∀ k ≤ m, ContinuousOn (convexJet k f K) K)
    (hsym : ∀ r ≤ m, ∀ x ∈ K, ∀ σ : Equiv.Perm (Fin r),
      (convexJet r f K x).domDomCongr σ = convexJet r f K x)
    (hdiff : ∃ C ≥ 0, ∀ r ≤ m, ∀ a ∈ K, ∀ b ∈ K, ∀ x : E,
      ‖iteratedFDeriv ℝ r
          (fun y ↦ taylorPolynomial m (fun j ↦ convexJet j f K) a y -
            taylorPolynomial m (fun j ↦ convexJet j f K) b y) x‖ ≤
        C * (‖x - a‖ + ‖x - b‖) ^ (m + 1 - r))
    (hbound : ∀ k ≤ m, ∃ C ≥ 0, ∀ x ∉ K,
      ∃ a ∈ K, Metric.infDist x K = dist x a ∧
        ‖iteratedFDeriv ℝ k G x - iteratedFDeriv ℝ k
            (taylorPolynomial m (fun j ↦ convexJet j f K) a) x‖ ≤
          C * (Metric.infDist x K) ^ (m + 1 - k)) :
    ∀ k ≤ m, Continuous (fun x ↦ gluedWhitneyJet K f G x k) := by
  sorry

/-- Off `K` the glued jet is the iterated derivative of `G`, and `Kᶜ` is open, so the
derivative of the `k`-th component is the next component (`ContDiffOn` on the open set,
`fderiv_iteratedFDeriv` and `iteratedFDeriv_succ_eq_comp_left`). -/
theorem hasFDerivAt_gluedWhitneyJet_of_not_mem
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} {m k : ℕ} {f G : E → F} {x : E}
    (hK : IsClosed K) (hx : x ∉ K) (hk : k < m)
    (hGo : ContDiffOn ℝ m G Kᶜ) :
    HasFDerivAt (fun y ↦ gluedWhitneyJet K f G y k)
      (gluedWhitneyJet K f G x (k + 1)).curryLeft x := by
  sorry

/-- Boundary differentiability of successive glued jets.  Subtract the linear term
`(J_(k+1)(a')).curryLeft (x-a')`; the exact Taylor formula at `a'` leaves order two,
while the off-set and two-base-point errors have exponent `m+1-k ≥ 2`. -/
theorem hasFDerivAt_gluedWhitneyJet_of_mem
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {K : Set E} {m k : ℕ} {f G : E → F} {x : E}
    (hK : IsClosed K) (hKn : K.Nonempty) (hx : x ∈ K) (hk : k < m)
    (hjet : ∀ r ≤ m, ContinuousOn (convexJet r f K) K)
    (hsym : ∀ r ≤ m, ∀ x ∈ K, ∀ σ : Equiv.Perm (Fin r),
      (convexJet r f K x).domDomCongr σ = convexJet r f K x)
    (hdiff : ∃ C ≥ 0, ∀ r ≤ m, ∀ a ∈ K, ∀ b ∈ K, ∀ y : E,
      ‖iteratedFDeriv ℝ r
          (fun z ↦ taylorPolynomial m (fun j ↦ convexJet j f K) a z -
            taylorPolynomial m (fun j ↦ convexJet j f K) b z) y‖ ≤
        C * (‖y - a‖ + ‖y - b‖) ^ (m + 1 - r))
    (hbound : ∀ r ≤ m, ∃ C ≥ 0, ∀ y ∉ K,
      ∃ a ∈ K, Metric.infDist y K = dist y a ∧
        ‖iteratedFDeriv ℝ r G y - iteratedFDeriv ℝ r
            (taylorPolynomial m (fun j ↦ convexJet j f K) a) y‖ ≤
          C * (Metric.infDist y K) ^ (m + 1 - r)) :
    HasFDerivAt (fun y ↦ gluedWhitneyJet K f G y k)
      (gluedWhitneyJet K f G x (k + 1)).curryLeft x := by
  sorry

/-- Assemble the zero-term identity, off-set derivatives, boundary derivative leaf, and
component continuity into Mathlib's `HasFTaylorSeriesUpTo` structure.  This isolates the
actual gluing argument from the standard Taylor-series-to-`ContDiff` conversion. -/
theorem hasFTaylorSeriesUpTo_gluedWhitneyJet
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {K : Set E} {m : ℕ} {f G : E → F}
    (hzero : ∀ x, (gluedWhitneyJet K f G x 0).curry0 = G x)
    (hcont : ∀ k ≤ m, Continuous (fun x ↦ gluedWhitneyJet K f G x k))
    (hderiv : ∀ k < m, ∀ x, HasFDerivAt (fun y ↦ gluedWhitneyJet K f G y k)
      (gluedWhitneyJet K f G x (k + 1)).curryLeft x) :
    HasFTaylorSeriesUpTo (m : WithTop ℕ∞) G (gluedWhitneyJet K f G) := by
  refine {
    zero_eq := hzero
    fderiv := ?_
    cont := ?_
  }
  · intro k hk x
    apply hderiv k ?_ x
    exact_mod_cast hk
  · intro k hk
    apply hcont k
    exact_mod_cast hk

/-- A global Taylor series through order `m` gives `C^m`; identify its first component
with the ordinary derivative and the on-`K` component with the within derivative. -/
theorem contDiff_and_fderiv_eq_of_gluedTaylorSeries
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} {m : ℕ} {f G : E → F}
    (hm : 1 ≤ m)
    (hone : ∀ x ∈ K, ∀ v, convexJet 1 f K x (fun _ ↦ v) = fderivWithin ℝ f K x v)
    (hT : HasFTaylorSeriesUpTo (m : WithTop ℕ∞) G (gluedWhitneyJet K f G)) :
    ContDiff ℝ m G ∧ ∀ x ∈ K, fderiv ℝ G x = fderivWithin ℝ f K x := by
  constructor
  · exact hT.contDiff
  · intro x hx
    have hm0 : (m : WithTop ℕ∞) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hm)
    rw [(hT.hasFDerivAt hm0 x).fderiv]
    ext v
    simp only [gluedWhitneyJet, hx, if_pos]
    convert hone x hx v using 1

/-- Fixed-order Whitney extension on a compact convex domain.  For positive `m`, choose the
partition, apply the polynomial-relative off-set estimate, and assemble the Taylor series.
For `m=0`, use the separate `C¹` differentiable-extension leaf so the derivative conclusion
is not incorrectly inferred from an order-zero Taylor series. -/
theorem exists_contDiff_extension_compactConvex
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {K : Set E} {f : E → F} (m : ℕ) (hm : 1 ≤ m)
    (hKc : IsCompact K) (hK : Convex ℝ K) (hKi : (interior K).Nonempty)
    (hf : ContDiffOn ℝ (m + 1) f K) :
    ∃ F' : E → F, ContDiff ℝ m F' ∧ Set.EqOn F' f K ∧
      ∀ x ∈ K, fderiv ℝ F' x = fderivWithin ℝ f K x := by
  sorry

/-- Intersecting a closed convex set with a sufficiently large closed ball about an interior
point remains compact convex with nonempty interior.  Use finite-dimensional properness and
the original interior point, choosing a positive radius. -/
theorem compactExhaustion_piece
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {s : Set E} (hs : IsClosed s) (hsc : Convex ℝ s)
    {p : E} (hp : p ∈ interior s) {R : ℝ} (hR : 0 < R) :
    IsCompact (s ∩ Metric.closedBall p R) ∧
      Convex ℝ (s ∩ Metric.closedBall p R) ∧
      (interior (s ∩ Metric.closedBall p R)).Nonempty := by
  refine ⟨(isCompact_closedBall p R).inter_left hs,
    hsc.inter (convex_closedBall p R), ?_⟩
  refine ⟨p, ?_⟩
  rw [interior_inter, interior_closedBall p (ne_of_gt hR)]
  exact ⟨hp, Metric.mem_ball_self hR⟩

/-- Inside the open ball, adding the closed-ball constraint does not change the within
derivative.  The two domains agree in a neighborhood of `x`; apply `fderivWithin_congr_set`
or the corresponding filter congruence lemma. -/
theorem fderivWithin_inter_closedBall_eq
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (s : Set E) (p : E) (R : ℝ) {x : E}
    (hx : x ∈ s ∩ Metric.ball p R) :
    fderivWithin ℝ f (s ∩ Metric.closedBall p R) x = fderivWithin ℝ f s x := by
  sorry

/-- Every point of `s` lies in an open ball of some positive integer radius about `p`.
This is the countable exhaustion needed to cover the relative critical image. -/
theorem subset_iUnion_inter_ball_nat
    {E : Type*} [PseudoMetricSpace E] (s : Set E) (p : E) :
    s ⊆ ⋃ n : ℕ, s ∩ Metric.ball p (n + 1 : ℝ) := by
  sorry

/-- On one compact exhaustion piece, the relative critical image is null.  Extend with
order `d(d+1)+2`, rewrite the within derivative on the open-ball core, and apply
`critical_image_null_of_high_order` to that arbitrary core set. -/
theorem compactExhaustion_critical_image_null
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (mu : Measure F) [mu.IsAddHaarMeasure]
    {s : Set E} (hs : IsClosed s) (hsc : Convex ℝ s) {p : E} (hp : p ∈ interior s)
    (f : E → F) (hf : ContDiffOn ℝ ∞ f s) (n : ℕ) :
    mu (f '' {x | x ∈ s ∩ Metric.ball p (n + 1 : ℝ) ∧
      ¬ Function.Surjective (fderivWithin ℝ f s x)}) = 0 := by
  sorry

/-- Sard for a closed convex domain with nonempty interior.  Cover its critical image by
the countable union of the compact-exhaustion critical images, apply the preceding nullity
leaf to each, and conclude with `measure_iUnion_null`. -/
theorem closedConvex_critical_image_null_innerProduct
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (mu : Measure F) [mu.IsAddHaarMeasure]
    {s : Set E} (hs : IsClosed s) (hsc : Convex ℝ s) (hsi : (interior s).Nonempty)
    (f : E → F) (hf : ContDiffOn ℝ ∞ f s) :
    mu (f '' {x | x ∈ s ∧
      ¬ Function.Surjective (fderivWithin ℝ f s x)}) = 0 := by
  sorry

/-- The same closed-convex Sard theorem for an arbitrary finite-dimensional normed source.
Choose a continuous linear equivalence with `EuclideanSpace ℝ (Fin (finrank ℝ E))`, transport
the set and map, apply the inner-product version, and conjugate the within derivative. -/
theorem closedConvex_critical_image_null
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (mu : Measure F) [mu.IsAddHaarMeasure]
    {s : Set E} (hs : IsClosed s) (hsc : Convex ℝ s) (hsi : (interior s).Nonempty)
    (f : E → F) (hf : ContDiffOn ℝ ∞ f s) :
    mu (f '' {x | x ∈ s ∧
      ¬ Function.Surjective (fderivWithin ℝ f s x)}) = 0 := by
  sorry

/-- Local chartwise Sard estimate used by both manifold consumers.  In the source chart at
`x`, choose `range I ∩ closedBall y r` inside the extended-chart target; it is closed convex
with nonempty interior because `y` lies in the closure of `interior (range I)`.  Apply the
normed-source theorem, use the open-ball derivative leaf, then transport `mfderiv`. -/
theorem manifold_local_critical_image_null
    {E H X V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace X]
    [SecondCountableTopology X] (I : ModelWithCorners ℝ E H) [ChartedSpace H X]
    [IsManifold I ∞ X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (mu : Measure V) [mu.IsAddHaarMeasure] (g : X → V)
    (hg : ContMDiff I (modelWithCornersSelf ℝ V) ∞ g) :
    ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      mu (g '' ({z | ¬ Function.Surjective
        (mfderiv I (modelWithCornersSelf ℝ V) g z)} ∩ U)) = 0 := by
  sorry

end ConstructionTargets.SardWhitneyExtension
