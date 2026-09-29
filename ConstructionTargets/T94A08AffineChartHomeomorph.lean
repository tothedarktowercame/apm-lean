import ConstructionTargets.T94A08AffineCoordinateQuotientCompatibility

open Set Topology
open scoped LinearAlgebra.Projectivization

noncomputable section

namespace ConstructionTargets.T94A08ProjectiveConic

open ConstructionTargets.ComplexProjectiveChartTargets

theorem continuous_coordinates (i : Fin 3) :
    ContinuousOn (coordinates i)
      {x : CP 2 | Projectivization.rep x i ≠ 0} :=
  (affineCoordinateQuotientCompatibility i).2.1

theorem affineChartConstruction : AffineChartConstruction 2 :=
  affineChartConstruction_of_quotientCompatibility
    affineCoordinateQuotientCompatibility

end ConstructionTargets.T94A08ProjectiveConic
