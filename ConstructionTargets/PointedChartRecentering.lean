import ConstructionTargets.RotatedCircleChartTransport
open CategoryTheory
noncomputable section
set_option autoImplicit false
namespace ConstructionTargets.PointedChartRecentering
open OneDimensionalChartLocalGenerator OneDiskIncreasingOrientation
open NestedOrientedChartCompatibility NestedOrientedChartCompatibility.PointedModelChart
open OrientedOverlapPuncturedCircle
variable {M : Type} [TopologicalSpace M] {x : M}

def ballSubtype (v : D) (r : ℝ) (hs : Metric.ball v.1 r ⊆ Metric.ball (0 : E) 1) :
    Metric.ball v.1 r ≃ₜ Metric.ball v r where
  toFun w := ⟨⟨w.1, hs w.2⟩, w.2⟩
  invFun w := ⟨w.1.1, w.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def affineBall (v : D) (r : ℝ) (hr : 0 < r)
    (hs : Metric.ball v.1 r ⊆ Metric.ball (0 : E) 1) : D ≃ₜ Metric.ball v r :=
  (OpenPartialHomeomorph.unitBallBall v.1 r hr).toHomeomorphSourceTarget.trans (ballSubtype v r hs)

def recenteredChart (c : PointedModelChart x) (v : D) (r : ℝ) (hr : 0 < r)
    (hs : Metric.ball v.1 r ⊆ Metric.ball (0 : E) 1) : PointedModelChart (c.ambient v) where
  neighborhood := c.ambient '' Metric.ball v r
  open_neighborhood :=
    (c.open_neighborhood.isOpenMap_subtype_val.comp c.coordinates.isOpenMap) _ Metric.isOpen_ball
  coordinates := (affineBall v r hr hs).trans
    ((c.open_neighborhood.isOpenEmbedding_subtypeVal.isEmbedding.comp c.coordinates.isEmbedding).homeomorphImage _)
  origin_eq := by
    change c.ambient ⟨r • (0 : E) + v.1, _⟩ = c.ambient v
    congr 1
    apply Subtype.ext
    simp

theorem recentered_ambient_formula (c : PointedModelChart x) (v : D) (r : ℝ) (hr : 0 < r)
    (hs : Metric.ball v.1 r ⊆ Metric.ball (0 : E) 1) (u : D) :
    (recenteredChart c v r hr hs).ambient u = c.ambient (affineBall v r hr hs u).1 := rfl

theorem recentered_coordinate_increasing (v : D) (r : ℝ) (hr : 0 < r)
    (hs : Metric.ball v.1 r ⊆ Metric.ball (0 : E) 1) (u w : D)
    (huw : coord u < coord w) :
    coord (affineBall v r hr hs u).1 < coord (affineBall v r hr hs w).1 := by
  change r * coord u + coord v < r * coord w + coord v
  linarith [mul_lt_mul_of_pos_left huw hr]

/-- A radius is constructed inside both the original coordinate disk and a requested ambient open. -/
theorem exists_recenter_radius (c : PointedModelChart x) (v : D) (U : Set M)
    (hU : IsOpen U) (hv : c.ambient v ∈ U) :
    ∃ r : ℝ, 0 < r ∧ (Metric.ball v.1 r ⊆ Metric.ball (0 : E) 1) ∧
      c.ambient '' Metric.ball v r ⊆ U := by
  obtain ⟨a, ha, hball⟩ := Metric.isOpen_iff.mp
    (hU.preimage c.ambient.continuous) v hv
  obtain ⟨b, hb, hbsub⟩ := Metric.isOpen_iff.mp Metric.isOpen_ball v.1 v.2
  refine ⟨min a b, lt_min ha hb, (Metric.ball_subset_ball (min_le_right _ _)).trans hbsub, ?_⟩
  rintro y ⟨u, hu, rfl⟩
  apply hball
  change dist u v < a
  change dist u v < min a b at hu
  exact lt_of_lt_of_le hu (min_le_left _ _)

/-- Construct a pointed chart at an arbitrary coordinate point inside a requested open neighborhood. -/
theorem exists_recentered_chart (c : PointedModelChart x) (v : D) (U : Set M)
    (hU : IsOpen U) (hv : c.ambient v ∈ U) :
    ∃ d : PointedModelChart (c.ambient v), d.neighborhood ⊆ U ∧
      d.neighborhood ⊆ c.neighborhood := by
  obtain ⟨r, hr, hs, hU'⟩ := exists_recenter_radius c v U hU hv
  refine ⟨recenteredChart c v r hr hs, hU', ?_⟩
  rintro y ⟨u, _, rfl⟩
  exact (c.coordinates u).2
theorem circle_overlap_recenter (x y : Circle) (v : D)
    (hv : (RotatedCircleChartTransport.rotatedChart x).ambient v ∈
      (RotatedCircleChartTransport.rotatedChart y).neighborhood) :
    ∃ d : PointedModelChart ((RotatedCircleChartTransport.rotatedChart x).ambient v),
      d.neighborhood ⊆ (RotatedCircleChartTransport.rotatedChart y).neighborhood ∧
      d.neighborhood ⊆ (RotatedCircleChartTransport.rotatedChart x).neighborhood :=
  exists_recentered_chart _ v _ (RotatedCircleChartTransport.rotatedChart y).open_neighborhood hv

end ConstructionTargets.PointedChartRecentering
#print axioms ConstructionTargets.PointedChartRecentering.recenteredChart
#print axioms ConstructionTargets.PointedChartRecentering.recentered_ambient_formula
#print axioms ConstructionTargets.PointedChartRecentering.recentered_coordinate_increasing
#print axioms ConstructionTargets.PointedChartRecentering.exists_recenter_radius
#print axioms ConstructionTargets.PointedChartRecentering.exists_recentered_chart

#print axioms ConstructionTargets.PointedChartRecentering.circle_overlap_recenter
