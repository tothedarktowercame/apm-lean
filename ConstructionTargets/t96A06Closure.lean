import Mathlib
import ConstructionTargets.ProjectiveSpaceTopology
import ConstructionTargets.ProjectiveConsumerLiftDemonstrations
import ConstructionTargets.RationalLefschetz

/-! Compiled closure milestones for t96A06. -/

open ConstructionTargets.ProjectiveSpaceTopology
open ConstructionTargets.ProjectiveConsumerLiftDemonstrations
open ConstructionTargets.RationalLefschetz

noncomputable section
namespace ConstructionTargets.t96A06Closure

abbrev RP3 := Space ℝ 3

def polynomialMap (v : Vectors ℝ 3) : Vectors ℝ 3 :=
  ![v 0 ^ 2 - v 1 ^ 2, 2 * v 0 * v 1,
    v 2 ^ 2 - v 3 ^ 2, 2 * v 2 * v 3]

theorem polynomialMap_eq_consumerPolynomial (v : Vectors ℝ 3) :
    polynomialMap v = t96A06Polynomial v := rfl

theorem polynomialMap_nonzero (v : NonzeroVectors ℝ 3) :
    polynomialMap v.1 ≠ 0 := by
  rw [polynomialMap_eq_consumerPolynomial]
  exact t96A06Polynomial_nonzero v

/-- A fixed choice of the actual projective descent of the printed quadratic.
Later degree and trace milestones refer to this map. -/
noncomputable def polynomialDescent : C(RP3, RP3) :=
  Classical.choose t96A06Polynomial_descends

/-- The chosen descent agrees with the printed formula on every nonzero
representative. -/
theorem polynomialDescent_quotientMap (v : NonzeroVectors ℝ 3) :
    polynomialDescent (quotientMap ℝ 3 v) =
      quotientMap ℝ 3 ⟨polynomialMap v.1, polynomialMap_nonzero v⟩ := by
  change (Classical.choose t96A06Polynomial_descends)
      (quotientMap ℝ 3 v) = _
  simpa only [polynomialMap, t96A06Polynomial] using
    (Classical.choose_spec t96A06Polynomial_descends v)

/-- Existential form consumed verbatim by the registered theorem. -/
theorem exists_polynomialDescent_formula :
    ∃ f : C(RP3, RP3),
      ∀ v : NonzeroVectors ℝ 3, ∃ hv : polynomialMap v.1 ≠ 0,
        f (quotientMap ℝ 3 v) = quotientMap ℝ 3 ⟨polynomialMap v.1, hv⟩ := by
  refine ⟨polynomialDescent, ?_⟩
  intro v
  exact ⟨polynomialMap_nonzero v, polynomialDescent_quotientMap v⟩

#print axioms polynomialMap_nonzero
#print axioms polynomialDescent
#print axioms polynomialDescent_quotientMap
#print axioms exists_polynomialDescent_formula

end ConstructionTargets.t96A06Closure
