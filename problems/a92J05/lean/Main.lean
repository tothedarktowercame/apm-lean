import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Tactic.ComputeDegree
import ConstructionTargets.Rouche

/-!
# APM a92J05: Counting roots outside the unit disk via Rouché

**Problem.** How many roots (with multiplicity) of z¹⁰ + 5z³ + 2z + 1 = 0
lie in {|z| > 1}? **Answer: 7.** By Rouché on |z| = 1.

## Formalization status

Mathlib does not currently provide Rouché's theorem or the equivalent
argument-principle invariance of zero count. We prove the elementary boundary
estimate, exclude boundary roots, establish the total root count, and reduce
the final theorem to the single assertion that three roots lie in the open
unit disk.
-/

set_option linter.unusedVariables false in
noncomputable section

open Complex Polynomial
open Metric Set

namespace ApmCanaries.A92J05

noncomputable def p : ℂ[X] := X ^ 10 + C (5 : ℂ) * X ^ 3 + C (2 : ℂ) * X + C (1 : ℂ)
noncomputable def g : ℂ[X] := C (5 : ℂ) * X ^ 3
noncomputable def h : ℂ[X] := X ^ 10 + C (2 : ℂ) * X + C (1 : ℂ)

lemma aeval_g (z : ℂ) : aeval z g = 5 * z ^ 3 := by simp [g]
lemma aeval_h (z : ℂ) : aeval z h = z ^ 10 + 2 * z + 1 := by simp [h]
lemma aeval_p (z : ℂ) : aeval z p = z ^ 10 + 5 * z ^ 3 + 2 * z + 1 := by simp [p]

lemma p_natDegree : p.natDegree = 10 := by
  unfold p
  compute_degree!

lemma p_monic : p.Monic := by
  unfold p
  monicity!

lemma p_card_roots : p.roots.card = 10 := by
  rw [← (IsAlgClosed.splits p).natDegree_eq_card_roots, p_natDegree]

/-- Auxiliary: if ‖z‖ = 1 then ‖z^n‖ = 1. -/
lemma norm_pow_of_norm_one (z : ℂ) (hz : ‖z‖ = 1) (n : ℕ) : ‖z ^ n‖ = 1 := by
  rw [norm_pow, hz]; simp

/-- Auxiliary: if ‖z‖ = 1 then ‖(c : ℂ) * z^n‖ = ‖c‖. -/
lemma norm_smul_pow_of_norm_one (z : ℂ) (hz : ‖z‖ = 1) (c : ℂ) (n : ℕ) :
    ‖c * z ^ n‖ = ‖c‖ := by
  rw [norm_mul, norm_pow, hz, one_pow, mul_one]

/-- On |z| = 1: |h(z)| ≤ 4 < 5 = |g(z)|. -/
lemma rouche_condition (z : ℂ) (hz : ‖z‖ = 1) : ‖aeval z h‖ < ‖aeval z g‖ := by
  rw [aeval_h, aeval_g]
  have h4 : ‖z ^ 10 + 2 * z + 1‖ ≤ 4 := by
    have h01 : ‖(z ^ 10 + 2 * z) + (1 : ℂ)‖ ≤ ‖z ^ 10 + 2 * z‖ + ‖(1 : ℂ)‖ :=
      norm_add_le _ _
    have h02 : ‖z ^ 10 + (2 : ℂ) * z‖ ≤ ‖z ^ 10‖ + ‖(2 : ℂ) * z‖ :=
      norm_add_le _ _
    have h03 : ‖z ^ 10‖ = (1 : ℝ) := norm_pow_of_norm_one z hz 10
    have h04 : ‖(2 : ℂ) * z‖ = 2 := by
      have : z = z ^ 1 := (pow_one z).symm
      rw [this, norm_smul_pow_of_norm_one z hz (2:ℂ) 1]; norm_num
    have h06 : ‖(1 : ℂ)‖ = 1 := by norm_num
    -- z^10 + 2*z = z^10 + (2:ℂ)*z definitionally
    linarith [h01, h02, h03, h04, h06]
  have h5 : ‖(5 : ℂ) * z ^ 3‖ = 5 := by
    rw [norm_smul_pow_of_norm_one z hz (5:ℂ) 3]; norm_num
  linarith

/-- The straight-line homotopy from the dominant term `g` to `p = g + h`
does not vanish on the unit circle. This is the complete elementary
boundary-homotopy input to Rouché's theorem. -/
lemma rouche_homotopy_ne_zero_on_circle
    (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (z : ℂ) (hz : ‖z‖ = 1) :
    aeval z g + (t : ℂ) * aeval z h ≠ 0 := by
  intro hzero
  have heq : aeval z g = -((t : ℂ) * aeval z h) :=
    eq_neg_of_add_eq_zero_left hzero
  have ht_norm : ‖(t : ℂ)‖ ≤ 1 := by
    simpa [abs_of_nonneg ht₀] using ht₁
  have hle : ‖aeval z g‖ ≤ ‖aeval z h‖ := by
    rw [heq, norm_neg, norm_mul]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right ht_norm (norm_nonneg (aeval z h))
  exact (not_lt_of_ge hle) (rouche_condition z hz)

/-- p has no roots on |z| = 1.

    If |z| = 1 and p(z) = 0: z¹⁰+1 = -(5z³+2z), so |z¹⁰+1| = |5z³+2z| ≥ 3,
    but |z¹⁰+1| ≤ 2. Contradiction. -/
lemma p_no_roots_on_circle (z : ℂ) (hz : ‖z‖ = 1) : aeval z p ≠ 0 := by
  intro hzero
  rw [aeval_p] at hzero
  -- z^10 + 1 = -(5z^3 + 2z) from p(z) = 0
  have heq : z ^ 10 + (1 : ℂ) = -((5 : ℂ) * z ^ 3 + (2 : ℂ) * z) := by
    have hconv : z ^ 10 + (1 : ℂ) + ((5 : ℂ) * z ^ 3 + (2 : ℂ) * z) =
        z ^ 10 + 5 * z ^ 3 + 2 * z + 1 := by push_cast; ring
    have hsum : z ^ 10 + (1 : ℂ) + ((5 : ℂ) * z ^ 3 + (2 : ℂ) * z) = 0 := by
      rw [hconv]; exact hzero
    -- a + b = 0 implies a = -b
    calc z ^ 10 + (1 : ℂ)
        = z ^ 10 + (1 : ℂ) + ((5 : ℂ) * z ^ 3 + (2 : ℂ) * z) -
            ((5 : ℂ) * z ^ 3 + (2 : ℂ) * z) := by ring
      _ = 0 - ((5 : ℂ) * z ^ 3 + (2 : ℂ) * z) := by rw [hsum]
      _ = -((5 : ℂ) * z ^ 3 + (2 : ℂ) * z) := by ring
  -- |z^10 + 1| ≤ 2
  have hle : ‖z ^ 10 + (1 : ℂ)‖ ≤ 2 := by
    have h01 : ‖z ^ 10 + (1 : ℂ)‖ ≤ ‖z ^ 10‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    have h02 : ‖z ^ 10‖ = (1 : ℝ) := norm_pow_of_norm_one z hz 10
    have h03 : ‖(1 : ℂ)‖ = 1 := by norm_num
    linarith
  -- |5z^3 + 2z| ≥ 3 via |5z^3| ≤ |5z^3 + 2z| + |2z|
  have hge : 3 ≤ ‖(5 : ℂ) * z ^ 3 + (2 : ℂ) * z‖ := by
    have h5z3 : ‖(5 : ℂ) * z ^ 3‖ = 5 := by
      rw [norm_smul_pow_of_norm_one z hz (5:ℂ) 3]; norm_num
    have h2z : ‖(2 : ℂ) * z‖ = 2 := by
      have : z = z ^ 1 := (pow_one z).symm
      rw [this, norm_smul_pow_of_norm_one z hz (2:ℂ) 1]; norm_num
    -- |5z^3| = |5z^3 + 2z - 2z| ≤ |5z^3 + 2z| + |2z|
    have key : ‖(5 : ℂ) * z ^ 3‖ ≤ ‖(5 : ℂ) * z ^ 3 + (2 : ℂ) * z‖ + ‖(2 : ℂ) * z‖ := by
      have htri : ‖((5 : ℂ) * z ^ 3 + (2 : ℂ) * z) + -((2 : ℂ) * z)‖ ≤
          ‖(5 : ℂ) * z ^ 3 + (2 : ℂ) * z‖ + ‖-((2 : ℂ) * z)‖ := norm_add_le _ _
      rw [norm_neg, add_neg_cancel_right] at htri
      linarith
    linarith
  -- |z^10 + 1| = |5z^3 + 2z| ≥ 3 but ≤ 2
  -- From heq: -(z^10 + 1) = 5z^3 + 2z
  have hneg : (5 : ℂ) * z ^ 3 + (2 : ℂ) * z = -(z ^ 10 + (1 : ℂ)) := by
    have h1 : z ^ 10 + (1 : ℂ) + ((5 : ℂ) * z ^ 3 + (2 : ℂ) * z) = 0 := by
      have : z ^ 10 + (1 : ℂ) + ((5 : ℂ) * z ^ 3 + (2 : ℂ) * z) =
          z ^ 10 + 5 * z ^ 3 + 2 * z + 1 := by push_cast; ring
      rw [this]; exact hzero
    have h2 : (5 : ℂ) * z ^ 3 + (2 : ℂ) * z = -(z ^ 10 + (1 : ℂ)) := by
      calc (5 : ℂ) * z ^ 3 + (2 : ℂ) * z
          = -(z ^ 10 + (1 : ℂ)) + ((5 : ℂ) * z ^ 3 + (2 : ℂ) * z + (z ^ 10 + (1 : ℂ))) := by ring
        _ = -(z ^ 10 + (1 : ℂ)) + 0 := by rw [← h1]; ring
        _ = -(z ^ 10 + (1 : ℂ)) := by ring
    exact h2
  rw [hneg, norm_neg] at hge
  linarith

/-- Since `p` has no roots on the unit circle, its roots partition into those
strictly inside and those strictly outside. -/
lemma roots_inside_add_outside :
    p.roots.filter (fun z => ‖z‖ < 1) +
      p.roots.filter (fun z => 1 < ‖z‖) = p.roots := by
  have houtside :
      p.roots.filter (fun z => 1 < ‖z‖) =
        p.roots.filter (fun z => ¬‖z‖ < 1) := by
    apply Multiset.filter_congr
    intro z hz
    constructor
    · exact fun hzout hzin => (not_lt_of_ge hzout.le) hzin
    · intro hznot
      have hle : 1 ≤ ‖z‖ := le_of_not_gt hznot
      exact hle.lt_of_ne fun heq => by
        have hp0 : p ≠ 0 := by
          intro hpzero
          have := p_natDegree
          rw [hpzero, natDegree_zero] at this
          norm_num at this
        have hzroot : aeval z p = 0 :=
          (Polynomial.mem_roots_iff_aeval_eq_zero hp0).mp hz
        exact p_no_roots_on_circle z heq.symm hzroot
  calc
    p.roots.filter (fun z => ‖z‖ < 1) +
          p.roots.filter (fun z => 1 < ‖z‖) =
        p.roots.filter (fun z => ‖z‖ < 1) +
          p.roots.filter (fun z => ¬‖z‖ < 1) := congrArg _ houtside
    _ = p.roots := Multiset.filter_add_not (fun z : ℂ => ‖z‖ < 1) p.roots

/-- The already-formalized algebraic bookkeeping after Rouché: once the
inside count is known to be three, the outside count is seven. -/
lemma roots_outside_card_eq_of_inside_card_eq
    (hinside : (p.roots.filter (fun z => ‖z‖ < 1)).card = 3) :
    (p.roots.filter (fun z => 1 < ‖z‖)).card = 7 := by
  have hcard := congrArg Multiset.card roots_inside_add_outside
  rw [Multiset.card_add, p_card_roots, hinside] at hcard
  omega

/-- For a monic complex polynomial, the divisor-based zero count on a closed
ball is the cardinality of the roots in that ball, with multiplicity. -/
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

/-- Main theorem: p has exactly 7 roots in {|z| > 1}.

    The reusable Rouché theorem transfers the zero count from `5z³` to `p`.
    A second transfer from `5z³` to the monic polynomial `z³` lets the general
    polynomial/divisor bridge evaluate that count as three. -/
theorem roots_outside_unit_disk :
    (p.roots.filter (fun z => 1 < ‖z‖)).card = 7 := by
  apply roots_outside_card_eq_of_inside_card_eq
  let F : ℂ → ℂ := fun z ↦ aeval z g
  let H : ℂ → ℂ := fun z ↦ aeval z h
  have hFan : AnalyticOnNhd ℂ F (closedBall 0 1) :=
    analyticOnNhd_id.aeval_polynomial g
  have hHan : AnalyticOnNhd ℂ H (closedBall 0 1) :=
    analyticOnNhd_id.aeval_polynomial h
  have hdom : ∀ z ∈ sphere (0 : ℂ) 1, ‖H z‖ < ‖F z‖ := by
    intro z hz
    apply rouche_condition
    simpa [mem_sphere] using hz
  have hp_transfer := ConstructionTargets.Rouche.zeroCountInClosedBall_add_eq
    (f := F) (g := H) (c := (0 : ℂ)) (R := 1) (by norm_num) hFan hHan hdom
  have hp_fun : F + H = fun z ↦ aeval z p := by
    funext z
    simp only [Pi.add_apply, F, H]
    rw [aeval_g, aeval_h, aeval_p]
    ring
  rw [hp_fun] at hp_transfer
  let K : ℂ → ℂ := fun z ↦ -4 * z ^ 3
  have hKan : AnalyticOnNhd ℂ K (closedBall 0 1) := by
    change AnalyticOnNhd ℂ (fun z : ℂ ↦ (-4 : ℂ) * z ^ 3) (closedBall 0 1)
    exact analyticOnNhd_const.mul (analyticOnNhd_id.pow 3)
  have hdomK : ∀ z ∈ sphere (0 : ℂ) 1, ‖K z‖ < ‖F z‖ := by
    intro z hz
    have hzn : ‖z‖ = 1 := by simpa [mem_sphere] using hz
    change ‖-4 * z ^ 3‖ < ‖aeval z g‖
    rw [aeval_g, norm_mul, norm_neg, norm_pow, hzn]
    norm_num [hzn]
  have hmono_transfer := ConstructionTargets.Rouche.zeroCountInClosedBall_add_eq
    (f := F) (g := K) (c := (0 : ℂ)) (R := 1) (by norm_num) hFan hKan hdomK
  have hmono_fun : F + K = fun z ↦ aeval z (X ^ 3 : ℂ[X]) := by
    funext z
    simp only [Pi.add_apply, F, K, aeval_g]
    simp
    ring
  rw [hmono_fun] at hmono_transfer
  have hp_count := zeroCountInClosedBall_aeval_eq_card_filter p p_monic 0 1
  have hmono_count := zeroCountInClosedBall_aeval_eq_card_filter
    (X ^ 3 : ℂ[X]) (monic_X.pow 3) 0 1
  rw [hp_count] at hp_transfer
  rw [hmono_count] at hmono_transfer
  have hinside_closed :
      (p.roots.filter (fun z ↦ dist z 0 ≤ 1)).card = 3 := by
    have hcast :
        ((p.roots.filter (fun z ↦ dist z 0 ≤ 1)).card : ℤ) = 3 := by
      rw [hp_transfer, ← hmono_transfer]
      simp
      have hfilter :
          (3 • ({0} : Multiset ℂ)).filter (fun z ↦ ‖z‖ ≤ 1) = 3 • {0} := by
        apply Multiset.filter_eq_self.mpr
        intro z hz
        simp at hz
        subst z
        simp
      rw [hfilter]
      simp
    exact_mod_cast hcast
  have hfilters : p.roots.filter (fun z ↦ ‖z‖ < 1) =
      p.roots.filter (fun z ↦ dist z 0 ≤ 1) := by
    apply Multiset.filter_congr
    intro z hzroot
    simp only [dist_zero_right]
    constructor
    · exact fun hz ↦ hz.le
    · intro hz
      exact hz.lt_of_ne fun heq ↦ by
        have hp0 : p ≠ 0 := fun hpzero ↦ by
          have := p_natDegree
          rw [hpzero, natDegree_zero] at this
          norm_num at this
        have hzroot' : aeval z p = 0 :=
          (Polynomial.mem_roots_iff_aeval_eq_zero hp0).mp hzroot
        exact p_no_roots_on_circle z heq hzroot'
  rw [hfilters, hinside_closed]

end ApmCanaries.A92J05
