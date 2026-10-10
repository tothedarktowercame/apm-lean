import ConstructionTargets.PolygonOuterRestrictedEqvGen

open Set Topology
open unitInterval
noncomputable section

namespace ConstructionTargets.PolygonOuterOpenDeformation

open ConstructionTargets.Surfaces
open ConstructionTargets.PolygonRadialOpenCover
open ConstructionTargets.PolygonOuterRadialDeformation
open ConstructionTargets.PolygonOuterRadialRelation
open ConstructionTargets.PolygonOuterRadialQuotientDeformation
open ConstructionTargets.PolygonOuterOpenRestrictedQuotient
open ConstructionTargets.PolygonOuterRestrictedEqvGen

variable (R : Surfaces.Disk → Surfaces.Disk → Prop)

def outerOpenHomotopy
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y)
    (hboundary : ∀ ⦃x y⦄, R x y → radius x = 1 ∧ radius y = 1) :
    I × outerOpen R → outerOpen R :=
  fun p => outerQuotientHomeomorph R hR
    (quotientHomotopy R hboundary
      (p.1, (outerQuotientHomeomorph R hR).symm p.2))

theorem continuous_outerOpenHomotopy
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y)
    (hboundary : ∀ ⦃x y⦄, R x y → radius x = 1 ∧ radius y = 1) :
    Continuous (outerOpenHomotopy R hR hboundary) := by
  apply (outerQuotientHomeomorph R hR).continuous.comp
  apply (continuous_quotientHomotopy R hboundary).comp
  exact continuous_fst.prodMk
    ((outerQuotientHomeomorph R hR).symm.continuous.comp continuous_snd)

theorem outerOpenHomotopy_zero
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y)
    (hboundary : ∀ ⦃x y⦄, R x y → radius x = 1 ∧ radius y = 1)
    (z : outerOpen R) :
    outerOpenHomotopy R hR hboundary (0, z) = z := by
  simp only [outerOpenHomotopy, quotientHomotopy_zero]
  exact (outerQuotientHomeomorph R hR).apply_symm_apply z

def IsBoundaryClass
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y)
    (z : outerOpen R) : Prop :=
  ∃ x : Outer, radius x.1 = 1 ∧
    z = outerQuotientHomeomorph R hR (Quotient.mk _ x)

theorem outerOpenHomotopy_one_boundary
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y)
    (hboundary : ∀ ⦃x y⦄, R x y → radius x = 1 ∧ radius y = 1)
    (z : outerOpen R) :
    IsBoundaryClass R hR (outerOpenHomotopy R hR hboundary (1, z)) := by
  obtain ⟨x, hx⟩ := Quotient.exists_rep ((outerQuotientHomeomorph R hR).symm z)
  refine ⟨radialHomotopy (1, x), radialHomotopy_one_radius x, ?_⟩
  simp only [outerOpenHomotopy]
  rw [← hx]
  rfl

theorem outerOpenHomotopy_fixed
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y)
    (hboundary : ∀ ⦃x y⦄, R x y → radius x = 1 ∧ radius y = 1)
    (t : I) (z : outerOpen R) (hz : IsBoundaryClass R hR z) :
    outerOpenHomotopy R hR hboundary (t, z) = z := by
  rcases hz with ⟨x, hx, rfl⟩
  simp only [outerOpenHomotopy, Homeomorph.symm_apply_apply]
  change outerQuotientHomeomorph R hR
      (Quotient.mk _ (radialHomotopy (t, x))) =
    outerQuotientHomeomorph R hR (Quotient.mk _ x)
  rw [radialHomotopy_fixed_of_radius_one t x hx]

end ConstructionTargets.PolygonOuterOpenDeformation
