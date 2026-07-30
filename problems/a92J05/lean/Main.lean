import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.ComputeDegree

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

/-- Main theorem: p has exactly 7 roots in {|z| > 1}.

    **SORRY BOUNDARY:** the remaining goal is precisely the Rouché conclusion
    that `p` has three roots in the open unit disk, counted with multiplicity.
    `ConstructionTargets/Rouche.lean` proves boundary nonvanishing for the
    straight-line homotopy, but its zero-count homotopy-invariance theorem is
    still open. Importing that theorem would only relocate `sorryAx`. -/
theorem roots_outside_unit_disk :
    (p.roots.filter (fun z => 1 < ‖z‖)).card = 7 := by
  apply roots_outside_card_eq_of_inside_card_eq
  sorry

end ApmCanaries.A92J05
