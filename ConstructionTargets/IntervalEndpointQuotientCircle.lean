import ConstructionTargets.PolygonBoundaryVertexClasses
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

open Set Topology
noncomputable section

namespace ConstructionTargets.IntervalEndpointQuotientCircle

abbrev Interval := Set.Icc (0 : ℝ) (0 + 1)
abbrev EndpointRel := AddCircle.EndpointIdent (1 : ℝ) 0
abbrev EndpointQuotient := Quot EndpointRel

def endpointQuotientHomeomorphCircle : EndpointQuotient ≃ₜ Circle :=
  (AddCircle.homeoIccQuot (1 : ℝ) 0).symm.trans
    (AddCircle.homeomorphCircle one_ne_zero)

@[simp] theorem endpointQuotientHomeomorphCircle_mk (t : Interval) :
    endpointQuotientHomeomorphCircle (Quot.mk _ t) =
      AddCircle.toCircle (t.1 : AddCircle (1 : ℝ)) := by
  rw [endpointQuotientHomeomorphCircle, Homeomorph.trans_apply,
    AddCircle.homeomorphCircle_apply]
  rfl

def intervalQuotientMap : Interval → EndpointQuotient :=
  fun t => Quot.mk EndpointRel t

theorem intervalQuotientMap_zero_eq_one :
    intervalQuotientMap ⟨0, by norm_num⟩ =
      intervalQuotientMap ⟨1, by norm_num⟩ :=
  by
    apply Quot.sound
    convert (AddCircle.EndpointIdent.mk (p := (1 : ℝ)) (a := 0)) using 1 <;>
      norm_num

@[simp] theorem endpointQuotientHomeomorphCircle_zero :
  endpointQuotientHomeomorphCircle (intervalQuotientMap ⟨0, by norm_num⟩) = 1 := by
  rw [intervalQuotientMap, endpointQuotientHomeomorphCircle_mk]
  exact AddCircle.toCircle_zero

@[simp] theorem endpointQuotientHomeomorphCircle_one :
    endpointQuotientHomeomorphCircle (intervalQuotientMap ⟨1, by norm_num⟩) = 1 := by
  rw [← intervalQuotientMap_zero_eq_one]
  exact endpointQuotientHomeomorphCircle_zero

end ConstructionTargets.IntervalEndpointQuotientCircle
