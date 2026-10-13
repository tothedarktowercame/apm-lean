import Mathlib
import ConstructionTargets.StatementSurfaceModels

/-! # APM t99A02: fundamental groups of the two requested wedges -/

open ConstructionTargets.PointWedgeQuotient
open ConstructionTargets.StatementSurfaceModels

noncomputable section

namespace APMT99A02

def rp2WedgeRp2Point : ProjectivePlaneWedge :=
  quotientMap (surfacePoint false 1) (surfacePoint false 1)
    (Sum.inl (surfacePoint false 1))

abbrev CircleWedgeProjectivePlane := Wedge (1 : Circle) (surfacePoint false 1)

def circleWedgeRp2Point : CircleWedgeProjectivePlane :=
  quotientMap (1 : Circle) (surfacePoint false 1) (Sum.inl 1)

end APMT99A02

theorem apm_t99a02 :
    Nonempty
      (FundamentalGroup ProjectivePlaneWedge APMT99A02.rp2WedgeRp2Point ≃*
        DihedralGroup 0) ∧
    Nonempty
      (FundamentalGroup APMT99A02.CircleWedgeProjectivePlane
          APMT99A02.circleWedgeRp2Point ≃*
        Monoid.Coprod (Multiplicative ℤ) (Multiplicative (ZMod 2))) := by
  sorry
