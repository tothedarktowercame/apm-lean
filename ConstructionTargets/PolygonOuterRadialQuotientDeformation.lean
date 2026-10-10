import ConstructionTargets.PolygonOuterRadialRelation
import Mathlib.Topology.CompactOpen

open Set Topology
open unitInterval
noncomputable section

namespace ConstructionTargets.PolygonOuterRadialQuotientDeformation

open ConstructionTargets.PolygonRadialOpenCover
open ConstructionTargets.PolygonOuterRadialDeformation
open ConstructionTargets.PolygonOuterRadialRelation
open ConstructionTargets.Surfaces

variable (R : Surfaces.Disk → Surfaces.Disk → Prop)

abbrev OuterQuotient (R : Surfaces.Disk → Surfaces.Disk → Prop) :=
  Quotient (Relation.EqvGen.setoid (OuterRel R))

def quotientHomotopy
    (hboundary : ∀ ⦃x y⦄, R x y → radius x = 1 ∧ radius y = 1) :
    I × OuterQuotient R → OuterQuotient R :=
  fun p => quotientTimeSlice R hboundary p.1 p.2

theorem quotientHomotopy_mk
    (hboundary : ∀ ⦃x y⦄, R x y → radius x = 1 ∧ radius y = 1)
    (t : I) (x : Outer) :
    quotientHomotopy R hboundary (t, Quotient.mk _ x) =
      Quotient.mk _ (radialHomotopy (t, x)) := rfl

theorem continuous_quotientHomotopy
    (hboundary : ∀ ⦃x y⦄, R x y → radius x = 1 ∧ radius y = 1) :
    Continuous (quotientHomotopy R hboundary) := by
  apply isQuotientMap_quotient_mk'.continuous_lift_prod_right
  simpa [quotientHomotopy] using
    isQuotientMap_quotient_mk'.continuous.comp continuous_radialHomotopy

def quotientHomotopyContinuous
    (hboundary : ∀ ⦃x y⦄, R x y → radius x = 1 ∧ radius y = 1) :
    C(I × OuterQuotient R, OuterQuotient R) :=
  ⟨quotientHomotopy R hboundary, continuous_quotientHomotopy R hboundary⟩

theorem quotientHomotopy_zero
    (hboundary : ∀ ⦃x y⦄, R x y → radius x = 1 ∧ radius y = 1)
    (z : OuterQuotient R) :
    quotientHomotopy R hboundary (0, z) = z :=
  quotientTimeSlice_zero R hboundary z

theorem quotientHomotopy_one_rep
    (hboundary : ∀ ⦃x y⦄, R x y → radius x = 1 ∧ radius y = 1)
    (x : Outer) :
    quotientHomotopy R hboundary (1, Quotient.mk _ x) =
        Quotient.mk _ (radialHomotopy (1, x)) ∧
      radius (radialHomotopy (1, x)).1 = 1 := by
  exact ⟨rfl, radialHomotopy_one_radius x⟩

end ConstructionTargets.PolygonOuterRadialQuotientDeformation
