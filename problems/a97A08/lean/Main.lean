import Mathlib
import ConstructionTargets.Rouche

open Complex Polynomial Set Metric

noncomputable section

/-- The polynomial f(z) = z⁵ + 15z + 1. -/
def apm_a97A08_f : Polynomial ℂ :=
  Polynomial.X ^ 5 + 15 * Polynomial.X + 1

/-- Helper: |15z + 1| < |z⁵| on the circle |z| = 2. -/
theorem apm_a97A08_rouche_outer
    (z : ℂ) (hz : ‖z‖ = 2) :
    ‖15 * z + 1‖ < ‖z ^ 5‖ := by
  have h1 : ‖15 * z + 1‖ ≤ 31 := by
    calc
      ‖15 * z + 1‖ ≤ ‖15 * z‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = 15 * ‖z‖ + 1 := by simp
      _ = 31 := by rw [hz]; norm_num
  have h2 : ‖z ^ 5‖ = 32 := by
    rw [norm_pow, hz]
    norm_num
  exact lt_of_le_of_lt h1 (by simpa [h2] using (show (31 : ℝ) < 32 by norm_num))

/-- Helper: |z⁵ + 1| < |15z| on the circle |z| = 3/2. -/
theorem apm_a97A08_rouche_inner
    (z : ℂ) (hz : ‖z‖ = 3/2) :
    ‖z ^ 5 + 1‖ < ‖15 * z‖ := by
  have h1 : ‖z ^ 5 + 1‖ ≤ (3 / 2 : ℝ) ^ 5 + 1 := by
    calc
      ‖z ^ 5 + 1‖ ≤ ‖z ^ 5‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = ‖z‖ ^ 5 + 1 := by simp [norm_pow]
      _ = (3 / 2 : ℝ) ^ 5 + 1 := by rw [hz]
  have h2 : ‖15 * z‖ = 15 * (3 / 2 : ℝ) := by
    rw [norm_mul, hz]
    norm_num
  have hlt : ((3 / 2 : ℝ) ^ 5 + 1) < 15 * (3 / 2 : ℝ) := by
    norm_num
  rw [h2]
  exact lt_of_le_of_lt h1 hlt

/-- f has no zeros on |z| = 2 (so the count on the open disk is well-defined). -/
theorem apm_a97A08_no_zeros_outer
    (z : ℂ) (hz : ‖z‖ = 2) :
    apm_a97A08_f.aeval z ≠ 0 := by
  intro hzero
  have hzero' : z ^ 5 + 15 * z + 1 = 0 := by
    simpa [apm_a97A08_f, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm, mul_left_comm] using hzero
  have hnorm : ‖15 * z + 1‖ = ‖z ^ 5‖ := by
    have hz5 : z ^ 5 = -(15 * z + 1) := by
      apply eq_neg_of_add_eq_zero_left
      simpa [add_assoc, add_comm, add_left_comm] using hzero'
    rw [hz5, norm_neg]
  nlinarith [apm_a97A08_rouche_outer z hz, hnorm]

/-- f has no zeros on |z| = 3/2. -/
theorem apm_a97A08_no_zeros_inner
    (z : ℂ) (hz : ‖z‖ = 3/2) :
    apm_a97A08_f.aeval z ≠ 0 := by
  intro hzero
  have hzero' : z ^ 5 + 15 * z + 1 = 0 := by
    simpa [apm_a97A08_f, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm, mul_left_comm] using hzero
  have hnorm : ‖z ^ 5 + 1‖ = ‖15 * z‖ := by
    have hz5 : z ^ 5 + 1 = -(15 * z) := by
      apply eq_neg_of_add_eq_zero_left
      simpa [add_assoc, add_comm, add_left_comm] using hzero'
    rw [hz5, norm_neg]
  nlinarith [apm_a97A08_rouche_inner z hz, hnorm]

/-- For a monic complex polynomial, the divisor zero count on a closed ball
is the cardinality of the roots there, with multiplicity. -/
lemma zeroCountInClosedBall_aeval_eq_card_filter
    (q : ℂ[X]) (hq : q.Monic) (c : ℂ) (R : ℝ) :
    ConstructionTargets.Rouche.zeroCountInClosedBall (fun z ↦ aeval z q) c R =
      (q.roots.filter (fun z ↦ dist z c ≤ R)).card := by
  classical
  let D : Function.locallyFinsupp ℂ ℤ :=
    { toFun := fun z ↦ q.roots.count z
      supportWithinDomain' := fun _ _ ↦ Set.mem_univ _
      supportLocallyFiniteWithinDomain' := by
        intro z _
        refine ⟨Set.univ, Filter.univ_mem, ?_⟩
        apply q.roots.toFinset.finite_toSet.subset
        intro x hx
        simp only [Set.mem_inter_iff, mem_univ, true_and, Function.mem_support,
          ne_eq] at hx
        apply Multiset.mem_toFinset.mpr
        apply Multiset.count_pos.mp
        have : q.roots.count x ≠ 0 := by exact_mod_cast hx
        omega }
  have hD : D.support.Finite := by
    apply q.roots.toFinset.finite_toSet.subset
    intro x hx
    apply Multiset.mem_toFinset.mpr
    apply Multiset.count_pos.mp
    have : q.roots.count x ≠ 0 := by
      change (q.roots.count x : ℤ) ≠ 0 at hx
      have hi : (q.roots.count x : ℤ) ≠ 0 := hx
      exact_mod_cast hi
    omega
  have hfactor : (fun z ↦ aeval z q) = ∏ᶠ u, (· - u) ^ D u := by
    funext z
    change q.eval z = _
    rw [(IsAlgClosed.splits q).eval_eq_prod_roots_of_monic hq]
    rw [Finset.prod_multiset_map_count]
    rw [finprod_eq_prod_of_mulSupport_subset (s := q.roots.toFinset)]
    simp only [Finset.prod_apply]
    · apply Finset.prod_congr rfl
      intro u hu
      change (z - u) ^ q.roots.count u = (z - u) ^ (q.roots.count u : ℤ)
      simp
    · intro u hu
      simp only [Function.FactorizedRational.mulSupport, Function.mem_support] at hu
      apply Multiset.mem_toFinset.mpr
      apply Multiset.count_pos.mp
      have : q.roots.count u ≠ 0 := by
        change (q.roots.count u : ℤ) ≠ 0 at hu
        exact_mod_cast hu
      omega
  unfold ConstructionTargets.Rouche.zeroCountInClosedBall
  rw [hfactor]
  have hmer : MeromorphicOn (∏ᶠ u, (· - u) ^ D u) Set.univ :=
    (Function.FactorizedRational.meromorphicNFOn D Set.univ).meromorphicOn
  rw [← hmer.divisor_restrict (show closedBall c R ⊆ Set.univ from subset_univ _),
    Function.FactorizedRational.divisor hD]
  rw [finsum_eq_sum_of_support_subset (s := q.roots.toFinset)]
  · have hcount :
        (∑ z ∈ q.roots.toFinset, if dist z c ≤ R then q.roots.count z else 0) =
          (q.roots.filter (fun z ↦ dist z c ≤ R)).card := by
      calc
        _ = ∑ z ∈ q.roots.toFinset,
              q.roots.count z * (if dist z c ≤ R then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro z _
            split <;> simp_all
        _ = (q.roots.map fun z ↦ if dist z c ≤ R then 1 else 0).sum :=
          Finset.sum_multiset_map_count q.roots _ |>.symm
        _ = _ := by
          induction q.roots using Multiset.induction_on with
          | empty => simp
          | cons a s ih =>
              by_cases ha : dist a c ≤ R <;> simp [ha, ih, Nat.add_comm]
    simp only [Function.locallyFinsuppWithin.restrict_apply]
    change (∑ z ∈ q.roots.toFinset,
      if dist z c ≤ R then (q.roots.count z : ℤ) else 0) = _
    exact_mod_cast hcount
  · intro z hz
    simp only [Function.mem_support] at hz
    by_contra hzroot
    have hznot : z ∉ q.roots := fun hm => hzroot (Multiset.mem_toFinset.mpr hm)
    have hzcount : q.roots.count z = 0 := Multiset.count_eq_zero.mpr hznot
    simp only [Function.locallyFinsuppWithin.restrict_apply] at hz
    change (if z ∈ closedBall c R then (q.roots.count z : ℤ) else 0) ≠ 0 at hz
    simp [hzcount] at hz

/-- f has 5 zeros (with multiplicity) in the open disk |z| < 2. -/
theorem apm_a97A08_count_outer :
    (apm_a97A08_f.roots.filter (fun z => ‖z‖ < 2)).card = 5 := by
  have hdeg : apm_a97A08_f.natDegree = 5 := by
    rw [show apm_a97A08_f =
        Polynomial.X ^ 5 + (15 * Polynomial.X + 1) by
      simp only [apm_a97A08_f]
      ring]
    have hq :
        (15 * Polynomial.X + 1 : Polynomial ℂ).natDegree <
          (Polynomial.X ^ 5 : Polynomial ℂ).natDegree := by
      rw [Polynomial.natDegree_X_pow]
      calc
        (15 * Polynomial.X + 1 : Polynomial ℂ).natDegree
            ≤ max (15 * Polynomial.X : Polynomial ℂ).natDegree
                (1 : Polynomial ℂ).natDegree :=
          Polynomial.natDegree_add_le _ _
        _ ≤ 1 := by norm_num
        _ < 5 := by norm_num
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hq,
      Polynomial.natDegree_X_pow]
  have hall : ∀ z ∈ apm_a97A08_f.roots, ‖z‖ < 2 := by
    intro z hz
    have hzero : z ^ 5 + 15 * z + 1 = 0 := by
      have := Polynomial.isRoot_of_mem_roots hz
      simpa [Polynomial.IsRoot, apm_a97A08_f, add_assoc, add_comm,
        add_left_comm, mul_assoc, mul_comm, mul_left_comm] using this
    have hnorm : ‖z‖ ^ 5 ≤ 15 * ‖z‖ + 1 := by
      have hz5 : z ^ 5 = -(15 * z + 1) := by
        apply eq_neg_of_add_eq_zero_left
        simpa [add_assoc, add_comm, add_left_comm] using hzero
      rw [← norm_pow, hz5, norm_neg]
      calc
        ‖15 * z + 1‖ ≤ ‖15 * z‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ = 15 * ‖z‖ + 1 := by simp
    by_contra hnot
    have hr : 2 ≤ ‖z‖ := le_of_not_gt hnot
    have hr0 : 0 ≤ ‖z‖ := norm_nonneg z
    have hr_sq : (4 : ℝ) ≤ ‖z‖ ^ 2 := by nlinarith
    have hr_four : (16 : ℝ) ≤ ‖z‖ ^ 4 := by nlinarith [sq_nonneg (‖z‖ ^ 2 - 4)]
    have hmul : 16 * ‖z‖ ≤ ‖z‖ ^ 5 := by
      calc
        16 * ‖z‖ ≤ ‖z‖ ^ 4 * ‖z‖ :=
          mul_le_mul_of_nonneg_right hr_four hr0
        _ = ‖z‖ ^ 5 := by ring
    nlinarith
  rw [Multiset.filter_eq_self.2 hall]
  have hsplits : apm_a97A08_f.Splits :=
    IsAlgClosed.splits apm_a97A08_f
  rw [← hsplits.natDegree_eq_card_roots, hdeg]

/-- f has 1 zero in the open disk |z| < 3/2. -/
theorem apm_a97A08_count_inner :
    (apm_a97A08_f.roots.filter (fun z => ‖z‖ < 3/2)).card = 1 := by
  let dominant : ℂ → ℂ := fun z => 15 * z
  let perturbation : ℂ → ℂ := fun z => z ^ 5 + 1
  have hdominant : AnalyticOnNhd ℂ dominant (closedBall 0 (3 / 2)) := by
    exact analyticOnNhd_const.mul analyticOnNhd_id
  have hperturbation :
      AnalyticOnNhd ℂ perturbation (closedBall 0 (3 / 2)) := by
    exact (analyticOnNhd_id.pow 5).add analyticOnNhd_const
  have hboundary : ∀ z ∈ sphere (0 : ℂ) (3 / 2),
      ‖perturbation z‖ < ‖dominant z‖ := by
    intro z hz
    apply apm_a97A08_rouche_inner
    simpa [mem_sphere, dist_zero_right] using hz
  have hrouche :=
    ConstructionTargets.Rouche.zeroCountInClosedBall_add_eq
      (c := (0 : ℂ)) (R := 3 / 2) (by norm_num : (0 : ℝ) < 3 / 2)
      hdominant hperturbation hboundary
  have hsum : dominant + perturbation = fun z => apm_a97A08_f.aeval z := by
    funext z
    simp [dominant, perturbation, apm_a97A08_f]
    ring
  rw [hsum] at hrouche
  let correction : ℂ → ℂ := fun z => -14 * z
  have hcorrection :
      AnalyticOnNhd ℂ correction (closedBall 0 (3 / 2)) := by
    exact analyticOnNhd_const.mul analyticOnNhd_id
  have hcorrection_boundary : ∀ z ∈ sphere (0 : ℂ) (3 / 2),
      ‖correction z‖ < ‖dominant z‖ := by
    intro z hz
    have hznorm : ‖z‖ = 3 / 2 := by
      simpa [mem_sphere, dist_zero_right] using hz
    simp [correction, dominant, hznorm]
    norm_num
  have hlinear :=
    ConstructionTargets.Rouche.zeroCountInClosedBall_add_eq
      (c := (0 : ℂ)) (R := 3 / 2) (by norm_num : (0 : ℝ) < 3 / 2)
      hdominant hcorrection hcorrection_boundary
  have hlinear_sum : dominant + correction =
      fun z => aeval z (Polynomial.X : ℂ[X]) := by
    funext z
    simp [dominant, correction]
    ring
  rw [hlinear_sum] at hlinear
  have hmonic : apm_a97A08_f.Monic := by
    rw [apm_a97A08_f]
    rw [show (Polynomial.X ^ 5 + 15 * Polynomial.X + 1 : Polynomial ℂ) =
        Polynomial.X ^ 5 + (15 * Polynomial.X + 1) by ring]
    apply (Polynomial.monic_X_pow 5).add_of_left
    compute_degree
    norm_num [Polynomial.degree_X_pow]
  have hclosed := zeroCountInClosedBall_aeval_eq_card_filter
    apm_a97A08_f hmonic 0 (3 / 2)
  have hxclosed := zeroCountInClosedBall_aeval_eq_card_filter
    (Polynomial.X : ℂ[X]) Polynomial.monic_X 0 (3 / 2)
  have hclosed_count :
      (apm_a97A08_f.roots.filter (fun z => dist z 0 ≤ 3 / 2)).card = 1 := by
    have hcast :
        ((apm_a97A08_f.roots.filter (fun z => dist z 0 ≤ 3 / 2)).card : ℤ) = 1 := by
      rw [← hclosed, hrouche, ← hlinear, hxclosed]
      have hz0 : ‖(0 : ℂ)‖ ≤ (3 / 2 : ℝ) := by norm_num
      have hfilter :
          ({0} : Multiset ℂ).filter (fun z => ‖z‖ ≤ 3 / 2) = {0} := by
        apply Multiset.filter_eq_self.mpr
        intro z hz
        simp at hz
        subst z
        exact hz0
      rw [Polynomial.roots_X]
      simp only [dist_zero_right]
      rw [hfilter]
      simp
    exact_mod_cast hcast
  have hfilters :
      apm_a97A08_f.roots.filter (fun z => dist z 0 ≤ 3 / 2) =
        apm_a97A08_f.roots.filter (fun z => ‖z‖ < 3 / 2) := by
    apply Multiset.filter_congr
    intro z hz
    rw [dist_zero_right]
    constructor
    · intro hle
      exact lt_of_le_of_ne hle fun heq => by
        apply apm_a97A08_no_zeros_inner z heq
        have hzroot := Polynomial.isRoot_of_mem_roots hz
        simpa [Polynomial.IsRoot, Polynomial.aeval_def,
          Polynomial.coe_aeval_eq_eval] using hzroot
    · exact fun hlt => hlt.le
  rw [← hfilters]
  exact hclosed_count

/-- Main theorem: the count in disk |z| < 2 is 5, and the count in
    annulus 3/2 < |z| < 2 is 4. -/
theorem apm_a97A08_main :
    (apm_a97A08_f.roots.filter (fun z => ‖z‖ < 2)).card = 5 ∧
    (apm_a97A08_f.roots.filter (fun z => 3/2 < ‖z‖ ∧ ‖z‖ < 2)).card = 4 := by
  refine ⟨apm_a97A08_count_outer, ?_⟩
  let s := apm_a97A08_f.roots.filter (fun z => ‖z‖ < 2)
  have hpartition :=
    Multiset.filter_add_not (p := fun z : ℂ => ‖z‖ < 3 / 2) s
  have hinner :
      s.filter (fun z => ‖z‖ < 3 / 2) =
        apm_a97A08_f.roots.filter (fun z => ‖z‖ < 3 / 2) := by
    simp only [s, Multiset.filter_filter]
    apply Multiset.filter_congr
    intro z hz
    constructor
    · exact fun h => h.1
    · intro h
      exact ⟨h, h.trans (by norm_num)⟩
  have hannulus :
      s.filter (fun z => ¬ ‖z‖ < 3 / 2) =
        apm_a97A08_f.roots.filter (fun z => 3 / 2 < ‖z‖ ∧ ‖z‖ < 2) := by
    simp only [s, Multiset.filter_filter]
    apply Multiset.filter_congr
    intro z hz
    have hboundary : ‖z‖ ≠ 3 / 2 := by
      intro heq
      apply apm_a97A08_no_zeros_inner z heq
      have hzroot := Polynomial.isRoot_of_mem_roots hz
      simpa [Polynomial.IsRoot, Polynomial.aeval_def,
        Polynomial.coe_aeval_eq_eval] using hzroot
    constructor
    · rintro ⟨hge, hout⟩
      exact ⟨lt_of_le_of_ne (le_of_not_gt hge) hboundary.symm, hout⟩
    · rintro ⟨hin, hout⟩
      exact ⟨not_lt_of_ge hin.le, hout⟩
  have hcard := congrArg Multiset.card hpartition
  rw [Multiset.card_add, hinner, hannulus, apm_a97A08_count_inner,
    show s.card = 5 by simpa [s] using apm_a97A08_count_outer] at hcard
  omega
