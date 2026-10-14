import Mathlib
import ConstructionTargets.ProjectiveSpaceTopology
import ConstructionTargets.RationalLefschetz
import ConstructionTargets.ProjectiveConsumerLiftDemonstrations

/-! # Blueprint for t96A06

The projective descent is already in the construction bank.  The remaining
library-sized theorem packages the rational homology and degree computation
which are not currently represented in Mathlib by a usable projective-space
API.
-/

open ConstructionTargets.ProjectiveSpaceTopology
open ConstructionTargets.RationalLefschetz
open ConstructionTargets.ProjectiveConsumerLiftDemonstrations
noncomputable section

namespace T96A06

abbrev RP3 := Space ℝ 3

def polynomialMap (v : Vectors ℝ 3) : Vectors ℝ 3 :=
  ![v 0 ^ 2 - v 1 ^ 2, 2 * v 0 * v 1,
    v 2 ^ 2 - v 3 ^ 2, 2 * v 2 * v 3]

/-- A map is the projective descent of the displayed quadratic formula. -/
def IsPolynomialDescent (f : ContinuousMap RP3 RP3) : Prop :=
  ∀ v : NonzeroVectors ℝ 3,
    f (quotientMap ℝ 3 v) = quotientMap ℝ 3
      ⟨polynomialMap v.val, by
        change t96A06Polynomial v.val ≠ 0
        exact t96A06Polynomial_nonzero v⟩

end T96A06

lemma T96A06_polynomialMap_eq_consumerPolynomial (v : Vectors ℝ 3) :
    T96A06.polynomialMap v = t96A06Polynomial v := by
  rfl

/-- The printed quadratic formula has a continuous projective descent. -/
theorem T96A06_polynomialMap_descends :
    ∃ f : ContinuousMap T96A06.RP3 T96A06.RP3,
      T96A06.IsPolynomialDescent f := by
  simpa only [T96A06.IsPolynomialDescent,
    T96A06_polynomialMap_eq_consumerPolynomial] using
    t96A06Polynomial_descends

/-! The invariant calculation is split at the singular-homology interface.
Each lemma below is independent: in particular, none uses another lemma in
this block.  This lets the RP³ computation, the four trace computations, and
homotopy invariance be developed in parallel. -/

lemma T96A06_rp3_rationalHomology_finite (k : ℕ) :
    FiniteDimensional ℚ (Homology T96A06.RP3 k) := by
  sorry

lemma T96A06_rp3_rationalHomology_vanishes_above_three (k : ℕ)
    (hk : 3 < k) :
    Subsingleton (Homology T96A06.RP3 k) := by
  sorry

lemma T96A06_polynomialDescent_trace_zero
    (f : ContinuousMap T96A06.RP3 T96A06.RP3)
    (hf : T96A06.IsPolynomialDescent f) :
    LinearMap.trace ℚ (Homology T96A06.RP3 0) (induced f 0).hom = 1 := by
  sorry

lemma T96A06_polynomialDescent_trace_one
    (f : ContinuousMap T96A06.RP3 T96A06.RP3)
    (hf : T96A06.IsPolynomialDescent f) :
    LinearMap.trace ℚ (Homology T96A06.RP3 1) (induced f 1).hom = 0 := by
  sorry

lemma T96A06_polynomialDescent_trace_two
    (f : ContinuousMap T96A06.RP3 T96A06.RP3)
    (hf : T96A06.IsPolynomialDescent f) :
    LinearMap.trace ℚ (Homology T96A06.RP3 2) (induced f 2).hom = 0 := by
  sorry

lemma T96A06_polynomialDescent_trace_three
    (f : ContinuousMap T96A06.RP3 T96A06.RP3)
    (hf : T96A06.IsPolynomialDescent f) :
    LinearMap.trace ℚ (Homology T96A06.RP3 3) (induced f 3).hom = 4 := by
  sorry

lemma T96A06_identity_trace_three :
    LinearMap.trace ℚ (Homology T96A06.RP3 3)
      (induced (ContinuousMap.id T96A06.RP3) 3).hom = 1 := by
  sorry

lemma T96A06_homotopic_induced_eq
    (f g : ContinuousMap T96A06.RP3 T96A06.RP3)
    (h : ContinuousMap.Homotopic f g) (k : ℕ) :
    induced f k = induced g k := by
  sorry

/-- **LIBRARY: RP³ rational homology and degree of complex squaring.**

The descended map has degree four.  Since rationally RP³ has homology only
in degrees zero and three, its Lefschetz number is `1 - 4 = -3`; homotopy
invariance then separates it from the identity, whose Lefschetz number is
zero. -/
theorem T96A06_polynomialDescent_invariants
    (f : ContinuousMap T96A06.RP3 T96A06.RP3)
    (hf : T96A06.IsPolynomialDescent f) :
    HasLefschetzNumber f (-3) ∧
      ¬ ContinuousMap.Homotopic f (ContinuousMap.id T96A06.RP3) := by
  constructor
  · refine ⟨T96A06_rp3_rationalHomology_finite, 3, ?_, ?_⟩
    · exact T96A06_rp3_rationalHomology_vanishes_above_three
    · rw [Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ]
      rw [T96A06_polynomialDescent_trace_zero f hf,
        T96A06_polynomialDescent_trace_one f hf,
        T96A06_polynomialDescent_trace_two f hf,
        T96A06_polynomialDescent_trace_three f hf]
      norm_num
  · intro h
    have heq := T96A06_homotopic_induced_eq f
      (ContinuousMap.id T96A06.RP3) h 3
    have htrace := congrArg
      (fun u => LinearMap.trace ℚ (Homology T96A06.RP3 3) u.hom) heq
    dsimp only at htrace
    rw [T96A06_polynomialDescent_trace_three f hf,
      T96A06_identity_trace_three] at htrace
    norm_num at htrace

theorem apm_t96a06 :
    ∃ f : ContinuousMap T96A06.RP3 T96A06.RP3,
      (∀ v : NonzeroVectors ℝ 3, ∃ hv : T96A06.polynomialMap v.val ≠ 0,
        f (quotientMap ℝ 3 v) = quotientMap ℝ 3 ⟨T96A06.polynomialMap v.val, hv⟩) ∧
      HasLefschetzNumber f (-3) ∧
      ¬ ContinuousMap.Homotopic f (ContinuousMap.id T96A06.RP3) := by
  obtain ⟨f, hf⟩ := T96A06_polynomialMap_descends
  refine ⟨f, ?_, T96A06_polynomialDescent_invariants f hf⟩
  intro v
  let hv : T96A06.polynomialMap v.val ≠ 0 := by
    change t96A06Polynomial v.val ≠ 0
    exact t96A06Polynomial_nonzero v
  exact ⟨hv, hf v⟩

#print axioms apm_t96a06
