import ConstructionTargets.PolygonTorusCrosscapRelation

open Set Topology
noncomputable section

namespace ConstructionTargets.PolygonBoundaryCircleSource

open ConstructionTargets.Surfaces
open ConstructionTargets.PolygonRadialOpenCover

abbrev Boundary := {x : Disk // radius x = 1}

def circleToBoundary (z : Circle) : Boundary := by
  refine ⟨⟨(z : ℂ), ?_⟩, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_eq (by simpa [Metric.mem_sphere, dist_zero_right] using z.2)
  · simpa [radius, Metric.mem_sphere, dist_zero_right] using z.2

def boundaryToCircle (x : Boundary) : Circle := by
  refine ⟨(x.1.1 : ℂ), ?_⟩
  change (x.1.1 : ℂ) ∈ Metric.sphere 0 1
  rw [Metric.mem_sphere, dist_zero_right]
  exact x.2

@[simp] theorem boundaryToCircle_circleToBoundary (z : Circle) :
    boundaryToCircle (circleToBoundary z) = z := by
  apply Subtype.ext
  rfl

@[simp] theorem circleToBoundary_boundaryToCircle (x : Boundary) :
    circleToBoundary (boundaryToCircle x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

def boundaryCircleHomeomorph : Circle ≃ₜ Boundary where
  toFun := circleToBoundary
  invFun := boundaryToCircle
  left_inv := boundaryToCircle_circleToBoundary
  right_inv := circleToBoundary_boundaryToCircle
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

theorem circleToBoundary_val (z : Circle) :
    (circleToBoundary z).1.1 = (z : ℂ) := rfl

theorem boundaryCircleHomeomorph_apply (z : Circle) :
    boundaryCircleHomeomorph z = circleToBoundary z := rfl

end ConstructionTargets.PolygonBoundaryCircleSource
