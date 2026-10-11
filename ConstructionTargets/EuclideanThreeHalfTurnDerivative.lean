import Mathlib

noncomputable section

namespace ConstructionTargets.EuclideanThreeHalfTurnDerivative

abbrev E3 := EuclideanSpace ℝ (Fin 3)

def halfTurnLinearMap : E3 →ₗ[ℝ] E3 where
  toFun p := WithLp.toLp 2 ![p 0, -p 1, -p 2]
  map_add' p q := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp <;> ac_rfl
  map_smul' a p := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp

def halfTurnLinear : E3 →L[ℝ] E3 := halfTurnLinearMap.toContinuousLinearMap

theorem halfTurnLinear_apply (p : E3) :
    halfTurnLinear p = WithLp.toLp 2 ![p 0, -p 1, -p 2] := by
  rfl

theorem hasFDerivAt_halfTurnLinear (p : E3) :
    HasFDerivAt (fun q : E3 => WithLp.toLp 2 ![q 0, -q 1, -q 2])
      halfTurnLinear p := by
  simpa only [← halfTurnLinear_apply] using halfTurnLinear.hasFDerivAt

theorem fderiv_halfTurn (p : E3) :
    fderiv ℝ (fun q : E3 => WithLp.toLp 2 ![q 0, -q 1, -q 2]) p =
      halfTurnLinear :=
  (hasFDerivAt_halfTurnLinear p).fderiv

theorem fderiv_halfTurn_single_succ (p : E3) (i : Fin 2) :
    fderiv ℝ (fun q : E3 => WithLp.toLp 2 ![q 0, -q 1, -q 2]) p
        (EuclideanSpace.single i.succ 1) =
      -EuclideanSpace.single i.succ 1 := by
  rw [fderiv_halfTurn]
  apply PiLp.ext
  intro j
  fin_cases i <;> fin_cases j <;> simp [halfTurnLinear, halfTurnLinearMap]

end ConstructionTargets.EuclideanThreeHalfTurnDerivative

#print axioms ConstructionTargets.EuclideanThreeHalfTurnDerivative.fderiv_halfTurn
#print axioms ConstructionTargets.EuclideanThreeHalfTurnDerivative.fderiv_halfTurn_single_succ
