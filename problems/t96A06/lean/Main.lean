import Mathlib
import ConstructionTargets.ProjectiveSpaceTopology
import ConstructionTargets.RationalLefschetz

/-! # t96A06: quadratic self-map of real projective three-space

RP3 is the algebraic quotient of nonzero real four-vectors by nonzero scalar
multiples, equipped with the coinduced topology. The existential continuous
map must commute with the printed quadratic formula on EVERY nonzero vector;
the same clause requires that its image vector is nonzero. Thus the map is
not an arbitrary parameter with a guessed invariant. All three parts are
stated: descent, Lefschetz number -3, and not homotopic to identity.
-/

open ConstructionTargets.ProjectiveSpaceTopology
open ConstructionTargets.RationalLefschetz
noncomputable section

namespace T96A06
abbrev RP3 := Space ℝ 3

def polynomialMap (v : Vectors ℝ 3) : Vectors ℝ 3 :=
  ![v 0 ^ 2 - v 1 ^ 2, 2 * v 0 * v 1,
    v 2 ^ 2 - v 3 ^ 2, 2 * v 2 * v 3]
end T96A06

theorem apm_t96a06 :
    ∃ f : ContinuousMap T96A06.RP3 T96A06.RP3,
      (∀ v : NonzeroVectors ℝ 3, ∃ hv : T96A06.polynomialMap v.val ≠ 0,
        f (quotientMap ℝ 3 v) = quotientMap ℝ 3 ⟨T96A06.polynomialMap v.val, hv⟩) ∧
      HasLefschetzNumber f (-3) ∧
      ¬ ContinuousMap.Homotopic f (ContinuousMap.id T96A06.RP3) := by
  sorry
